import Solutions.V4.Stable

/-! # V4: size soundness and substitution lemmas for the interpretation -/

namespace NishtAbel2024V4

open Order

/-! ## Sizes -/

theorem add_nat_lt_add_nat {α β : Ordinal.{0}} (h : α < β) (n : Nat) : α + n < β + n := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, ← add_assoc, ← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
    exact Order.succ_lt_succ ih

theorem SizeCtx.mem_dom {Ψ : SizeCtx} {i : Nat} {a : Size} (h : (i, a) ∈ Ψ) : i ∈ Ψ.dom :=
  List.mem_map.mpr ⟨(i, a), h, rfl⟩

theorem ValidVal.lt_omega {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {i : Nat}
    (hi : i ∈ Ψ.dom) : ρ i < Omega := by
  obtain ⟨⟨j, a⟩, hm, rfl⟩ := List.mem_map.mp hi
  exact (hv _ hm).2

/-- Locally closed sizes do not depend on the bound-size environment. -/
theorem sizeVal_closed {Ψ : SizeCtx} {a : Size} (ha : SizeWf Ψ a) (ρ : SizeVal) (ζ ζ' : SzEnv) :
    sizeVal ρ ζ a = sizeVal ρ ζ' a := by
  cases a with
  | inf => rfl
  | var i n => rfl
  | bvar k n => exact absurd ha (Nat.not_lt_zero _)

theorem sizeVal_le_omega {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {a : Size}
    (ha : SizeWf Ψ a) (ζ : SzEnv) : sizeVal ρ ζ a ≤ Omega := by
  cases a with
  | inf => exact le_rfl
  | var i n => exact (add_nat_lt_omega (hv.lt_omega ha) n).le
  | bvar k n => exact absurd ha (Nat.not_lt_zero _)

theorem sizeVal_shift_var (ρ : SizeVal) (ζ : SzEnv) (j m n : Nat) :
    sizeVal ρ ζ ((Size.var j m).shift n) = sizeVal ρ ζ (.var j m) + n := by
  simp [Size.shift, sizeVal, Nat.cast_add, add_assoc]

theorem sizeVal_shift_bvar (ρ : SizeVal) (ζ : SzEnv) (j m n : Nat) :
    sizeVal ρ ζ ((Size.bvar j m).shift n) = sizeVal ρ ζ (.bvar j m) + n := by
  simp [Size.shift, sizeVal, Nat.cast_add, add_assoc]

/-- Size soundness (Theorem 2, strict part), at the closed valuation. -/
theorem sizeLt_sound {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {a b : Size}
    (h : SizeLt Ψ a b) : sizeVal ρ SzEnv.zero a < sizeVal ρ SzEnv.zero b := by
  induction h with
  | var_var hi hnm =>
    simp only [sizeVal]
    exact (add_lt_add_iff_left _).mpr (by exact_mod_cast hnm)
  | var_inf hi => exact add_nat_lt_omega (hv.lt_omega hi) _
  | @bound i n a hm =>
    have hlt := (hv _ hm).1
    cases a with
    | inf => exact add_nat_lt_omega (hv _ hm).2 n
    | var j m =>
      rw [sizeVal_shift_var]
      exact add_nat_lt_add_nat hlt n
    | bvar j m =>
      rw [sizeVal_shift_bvar]
      exact add_nat_lt_add_nat hlt n
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem sizeLt_wf_left {Ψ : SizeCtx} {a b : Size} (h : SizeLt Ψ a b) :
    ∃ i n, a = .var i n ∧ i ∈ Ψ.dom := by
  induction h with
  | var_var hi _ => exact ⟨_, _, rfl, hi⟩
  | var_inf hi => exact ⟨_, _, rfl, hi⟩
  | bound hm => exact ⟨_, _, rfl, SizeCtx.mem_dom hm⟩
  | trans _ _ ih _ => exact ih

/-- Size soundness (Theorem 2, non-strict part). -/
theorem sizeLe_sound {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {a b : Size}
    (h : SizeLe Ψ a b) : sizeVal ρ SzEnv.zero a ≤ sizeVal ρ SzEnv.zero b := by
  rcases h with ⟨rfl, _⟩ | ⟨rfl, ha⟩ | h | ⟨i, n, m, rfl, rfl, hnm, _⟩
  · exact le_rfl
  · exact sizeVal_le_omega hv ha _
  · exact (sizeLt_sound hv h).le
  · simp only [sizeVal]
    exact add_le_add_right (by exact_mod_cast hnm) _

theorem sizeBelow_sound {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {b a : Size}
    (h : SizeBelow Ψ b a) :
    sizeVal ρ SzEnv.zero b < sizeVal ρ SzEnv.zero a ∨ (b = .inf ∧ a = .inf) := by
  rcases h with h | h
  · exact Or.inl (sizeLt_sound hv h)
  · exact Or.inr h

/-! ## Environments -/

def SzEnv.insert (k : Nat) (β : Ordinal.{0}) (ζ : SzEnv) : SzEnv := fun x =>
  if x < k then ζ x else if x = k then β else ζ (x - 1)

theorem SzEnv.insert_succ_cons (k : Nat) (β γ : Ordinal.{0}) (ζ : SzEnv) :
    SzEnv.insert (k + 1) β (SzEnv.cons γ ζ) = SzEnv.cons γ (SzEnv.insert k β ζ) := by
  funext x
  cases x with
  | zero => simp [SzEnv.insert, SzEnv.cons]
  | succ y =>
    simp only [SzEnv.insert, SzEnv.cons]
    by_cases h1 : y < k
    · simp [h1]
    · by_cases h2 : y = k
      · subst h2; simp
      · have h3 : ¬ y + 1 < k + 1 := by omega
        have h4 : y + 1 ≠ k + 1 := by omega
        simp only [h1, h2, h3, h4, if_false]
        cases y with
        | zero => omega
        | succ z => rfl

theorem SzEnv.insert_zero (β : Ordinal.{0}) (ζ : SzEnv) : SzEnv.insert 0 β ζ = SzEnv.cons β ζ := by
  funext x
  cases x with
  | zero => simp [SzEnv.insert, SzEnv.cons]
  | succ y => simp [SzEnv.insert, SzEnv.cons]

/-- Insert `𝒳` at position `k`, shifting the variables above. -/
def Env.insert (k : Nat) (𝒳 : Set Tm) (η : Env) : Env := fun X =>
  if X < k then η X else if X = k then 𝒳 else η (X - 1)

theorem Env.insert_succ_cons (k : Nat) (𝒳 𝒴 : Set Tm) (η : Env) :
    Env.insert (k + 1) 𝒳 (Env.cons 𝒴 η) = Env.cons 𝒴 (Env.insert k 𝒳 η) := by
  funext X
  cases X with
  | zero => simp [Env.insert, Env.cons]
  | succ Y =>
    simp only [Env.insert, Env.cons]
    by_cases h1 : Y < k
    · simp [h1]
    · by_cases h2 : Y = k
      · subst h2; simp
      · have h3 : ¬ Y + 1 < k + 1 := by omega
        have h4 : Y + 1 ≠ k + 1 := by omega
        simp only [h1, h2, h3, h4, if_false]
        cases Y with
        | zero => omega
        | succ Z => rfl

theorem Env.insert_zero (𝒳 : Set Tm) (η : Env) : Env.insert 0 𝒳 η = Env.cons 𝒳 η := by
  funext X
  cases X with
  | zero => simp [Env.insert, Env.cons]
  | succ Y => simp [Env.insert, Env.cons]

/-! ## Agreement -/

theorem sizeVal_agree {Ψ : SizeCtx} {m : Nat} {ρ ρ' : SizeVal} {ζ ζ' : SzEnv}
    (hρ : ∀ i ∈ Ψ.dom, ρ i = ρ' i) (hζ : ∀ x < m, ζ x = ζ' x) {a : Size}
    (ha : SizeWfAt Ψ m a) : sizeVal ρ ζ a = sizeVal ρ' ζ' a := by
  cases a with
  | inf => rfl
  | var i n => simp only [sizeVal, hρ i ha]
  | bvar k n => simp only [sizeVal, hζ k ha]

theorem SzEnv.cons_agree {ζ ζ' : SzEnv} {m : Nat} (h : ∀ x < m, ζ x = ζ' x) (β : Ordinal.{0}) :
    ∀ x < m + 1, SzEnv.cons β ζ x = SzEnv.cons β ζ' x
  | 0, _ => rfl
  | x + 1, hx => h x (by omega)

theorem Env.cons_agree {η η' : Env} {k : Nat} (h : ∀ X < k, η X = η' X) (𝒳 : Set Tm) :
    ∀ X < k + 1, Env.cons 𝒳 η X = Env.cons 𝒳 η' X
  | 0, _ => rfl
  | X + 1, hX => h X (by omega)

theorem interp_agree {W : World} {Ψ : SizeCtx} {Θ : List Nat} {k m : Nat} {A : Ty}
    (hA : TyWf Ψ Θ k m A) :
    ∀ (ρ ρ' : SizeVal) (θ θ' : TEnv) (ζ ζ' : SzEnv) (η η' : Env),
      (∀ i ∈ Ψ.dom, ρ i = ρ' i) → (∀ X ∈ Θ, θ X = θ' X) → (∀ x < m, ζ x = ζ' x) →
      (∀ X < k, η X = η' X) → interp W ρ θ A ζ η = interp W ρ' θ' A ζ' η' := by
  induction hA with
  | unit k => intro _ _ _ _ _ _ _ _ _ _ _ _; rfl
  | prod _ _ ihA ihB =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη
    simp only [interp]
    rw [ihA ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη, ihB ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη]
  | arr _ _ ihA ihB =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη
    simp only [interp]
    rw [ihA ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη, ihB ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη]
  | var hX => intro _ _ _ _ _ _ η η' _ _ _ hη; exact hη _ hX
  | fvar hX => intro _ _ θ θ' _ _ _ _ _ hθ _ _; exact hθ _ hX
  | @mu k m a S ha _ _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη
    simp only [interp]
    rw [sizeVal_agree hρ hζ ha]
    have : (fun c 𝒳 => interpAt W ρ θ S c ζ (Env.cons 𝒳 η)) =
        (fun c 𝒳 => interpAt W ρ' θ' S c ζ' (Env.cons 𝒳 η')) := by
      funext c 𝒳
      by_cases hc : c < S.length
      · rw [interpAt_eq W ρ θ S c _ _ hc, interpAt_eq W ρ' θ' S c _ _ hc]
        exact ih _ (List.getElem_mem hc) _ _ _ _ _ _ _ _ hρ hθ hζ (Env.cons_agree hη 𝒳)
      · rw [interpAt_out W ρ θ S c _ _ (by omega), interpAt_out W ρ' θ' S c _ _ (by omega)]
    rw [this]
  | @nu k m a R ha _ _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη
    simp only [interp]
    rw [sizeVal_agree hρ hζ ha]
    have : (fun d 𝒳 => interpAt W ρ θ R d ζ (Env.cons 𝒳 η)) =
        (fun d 𝒳 => interpAt W ρ' θ' R d ζ' (Env.cons 𝒳 η')) := by
      funext d 𝒳
      by_cases hd : d < R.length
      · rw [interpAt_eq W ρ θ R d _ _ hd, interpAt_eq W ρ' θ' R d _ _ hd]
        exact ih _ (List.getElem_mem hd) _ _ _ _ _ _ _ _ hρ hθ hζ (Env.cons_agree hη 𝒳)
      · rw [interpAt_out W ρ θ R d _ _ (by omega), interpAt_out W ρ' θ' R d _ _ (by omega)]
    rw [this]
  | @allT k m B _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη
    simp only [interp]
    have : (fun 𝒳 => interp W ρ θ B ζ (Env.cons 𝒳 η)) =
        (fun 𝒳 => interp W ρ' θ' B ζ' (Env.cons 𝒳 η')) := by
      funext 𝒳; exact ih _ _ _ _ _ _ _ _ hρ hθ hζ (Env.cons_agree hη 𝒳)
    rw [this]
  | @exT k m B _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη
    simp only [interp]
    have : (fun 𝒳 => interp W ρ θ B ζ (Env.cons 𝒳 η)) =
        (fun 𝒳 => interp W ρ' θ' B ζ' (Env.cons 𝒳 η')) := by
      funext 𝒳; exact ih _ _ _ _ _ _ _ _ hρ hθ hζ (Env.cons_agree hη 𝒳)
    rw [this]
  | @allS k m a B ha _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη
    simp only [interp]
    rw [sizeVal_agree hρ hζ ha]
    have : (fun β => interp W ρ θ B (SzEnv.cons β ζ) η) =
        (fun β => interp W ρ' θ' B (SzEnv.cons β ζ') η') := by
      funext β; exact ih _ _ _ _ _ _ _ _ hρ hθ (SzEnv.cons_agree hζ β) hη
    rw [this]
  | @exS k m a B ha _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη
    simp only [interp]
    rw [sizeVal_agree hρ hζ ha]
    have : (fun β => interp W ρ θ B (SzEnv.cons β ζ) η) =
        (fun β => interp W ρ' θ' B (SzEnv.cons β ζ') η') := by
      funext β; exact ih _ _ _ _ _ _ _ _ hρ hθ (SzEnv.cons_agree hζ β) hη
    rw [this]

/-- Locally closed types depend on neither bound environment. -/
theorem interp_closed_env {W : World} {Ψ : SizeCtx} {Θ : List Nat} {A : Ty}
    (hA : TyWf Ψ Θ 0 0 A) (ρ : SizeVal) (θ : TEnv) (ζ ζ' : SzEnv) (η η' : Env) :
    interp W ρ θ A ζ η = interp W ρ θ A ζ' η' :=
  interp_agree hA ρ ρ θ θ ζ ζ' η η' (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))

/-! ## Substitution of free size variables -/

/-- The valuation induced by a size substitution. -/
noncomputable def substVal (ρ : SizeVal) (σ : List (Nat × Size)) : SizeVal := fun i =>
  match σ.lookup i with
  | some b => sizeVal ρ SzEnv.zero b
  | none => ρ i

/-- Substitutions whose values are free size variables with offsets. -/
def VarSubst (σ : List (Nat × Size)) : Prop := ∀ i b, σ.lookup i = some b → ∃ j m, b = .var j m

theorem sizeVal_subst {σ : List (Nat × Size)} (hσ : VarSubst σ) (ρ : SizeVal) (ζ : SzEnv)
    (a : Size) : sizeVal ρ ζ (a.subst σ) = sizeVal (substVal ρ σ) ζ a := by
  cases a with
  | inf => rfl
  | bvar k n => rfl
  | var i n =>
    simp only [Size.subst, sizeVal, substVal]
    cases h : σ.lookup i with
    | none => rfl
    | some b =>
      obtain ⟨j, m, rfl⟩ := hσ i _ h
      simp [Size.shift, Nat.cast_add, add_assoc, sizeVal]

theorem Ty.substSizeList_length (σ : List (Nat × Size)) :
    ∀ S : List Ty, (Ty.substSizeList σ S).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.substSizeList, Ty.substSizeList_length σ S]

mutual

theorem interp_substSize (W : World) (ρ : SizeVal) (θ : TEnv) {σ : List (Nat × Size)}
    (hσ : VarSubst σ) :
    ∀ (A : Ty) (ζ : SzEnv) (η : Env),
      interp W ρ θ (A.substSize σ) ζ η = interp W (substVal ρ σ) θ A ζ η
  | .unit, _, _ => rfl
  | .prod A B, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [interp_substSize W ρ θ hσ A ζ η, interp_substSize W ρ θ hσ B ζ η]
  | .arr A B, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [interp_substSize W ρ θ hσ A ζ η, interp_substSize W ρ θ hσ B ζ η]
  | .var _, _, _ => rfl
  | .fvar _, _, _ => rfl
  | .mu a S, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ]
    have : (fun c 𝒳 => interpAt W ρ θ (Ty.substSizeList σ S) c ζ (Env.cons 𝒳 η)) =
        (fun c 𝒳 => interpAt W (substVal ρ σ) θ S c ζ (Env.cons 𝒳 η)) := by
      funext c 𝒳; exact interpAt_substSize W ρ θ hσ S c ζ _
    rw [this]
  | .nu a R, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ, Ty.substSizeList_length]
    have : (fun d 𝒳 => interpAt W ρ θ (Ty.substSizeList σ R) d ζ (Env.cons 𝒳 η)) =
        (fun d 𝒳 => interpAt W (substVal ρ σ) θ R d ζ (Env.cons 𝒳 η)) := by
      funext d 𝒳; exact interpAt_substSize W ρ θ hσ R d ζ _
    rw [this]
  | .allT B, ζ, η => by
    simp only [Ty.substSize, interp]
    have : (fun 𝒳 => interp W ρ θ (B.substSize σ) ζ (Env.cons 𝒳 η)) =
        (fun 𝒳 => interp W (substVal ρ σ) θ B ζ (Env.cons 𝒳 η)) := by
      funext 𝒳; exact interp_substSize W ρ θ hσ B ζ _
    rw [this]
  | .exT B, ζ, η => by
    simp only [Ty.substSize, interp]
    have : (fun 𝒳 => interp W ρ θ (B.substSize σ) ζ (Env.cons 𝒳 η)) =
        (fun 𝒳 => interp W (substVal ρ σ) θ B ζ (Env.cons 𝒳 η)) := by
      funext 𝒳; exact interp_substSize W ρ θ hσ B ζ _
    rw [this]
  | .allS a B, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ]
    have : (fun β => interp W ρ θ (B.substSize σ) (SzEnv.cons β ζ) η) =
        (fun β => interp W (substVal ρ σ) θ B (SzEnv.cons β ζ) η) := by
      funext β; exact interp_substSize W ρ θ hσ B _ η
    rw [this]
  | .exS a B, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ]
    have : (fun β => interp W ρ θ (B.substSize σ) (SzEnv.cons β ζ) η) =
        (fun β => interp W (substVal ρ σ) θ B (SzEnv.cons β ζ) η) := by
      funext β; exact interp_substSize W ρ θ hσ B _ η
    rw [this]

theorem interpAt_substSize (W : World) (ρ : SizeVal) (θ : TEnv) {σ : List (Nat × Size)}
    (hσ : VarSubst σ) :
    ∀ (S : List Ty) (c : Nat) (ζ : SzEnv) (η : Env),
      interpAt W ρ θ (Ty.substSizeList σ S) c ζ η = interpAt W (substVal ρ σ) θ S c ζ η
  | [], c, _, _ => by cases c <;> rfl
  | A :: _, 0, ζ, η => interp_substSize W ρ θ hσ A ζ η
  | _ :: S, c + 1, ζ, η => interpAt_substSize W ρ θ hσ S c ζ η

end

/-! ## Substitution of bound type variables -/

theorem Ty.substTyList_length (k : Nat) (T : Ty) :
    ∀ S : List Ty, (Ty.substTyList S k T).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.substTyList, Ty.substTyList_length k T S]

/-- Types whose interpretation ignores both bound environments. -/
def EnvFree (W : World) (ρ : SizeVal) (θ : TEnv) (T : Ty) : Prop :=
  ∀ (ζ ζ' : SzEnv) (η η' : Env), interp W ρ θ T ζ η = interp W ρ θ T ζ' η'

mutual

theorem interp_substTy (W : World) (ρ : SizeVal) (θ : TEnv) {T : Ty} (hT : EnvFree W ρ θ T) :
    ∀ (A : Ty) (k : Nat) (ζ : SzEnv) (η : Env),
      interp W ρ θ (A.substTy k T) ζ η =
        interp W ρ θ A ζ (Env.insert k (interp W ρ θ T ζ η) η)
  | .unit, _, _, _ => rfl
  | .prod A B, k, ζ, η => by
    simp only [Ty.substTy, interp]
    rw [interp_substTy W ρ θ hT A k ζ η, interp_substTy W ρ θ hT B k ζ η]
  | .arr A B, k, ζ, η => by
    simp only [Ty.substTy, interp]
    rw [interp_substTy W ρ θ hT A k ζ η, interp_substTy W ρ θ hT B k ζ η]
  | .var X, k, ζ, η => by
    by_cases h1 : X = k
    · subst h1; simp [Ty.substTy, interp, Env.insert]
    · by_cases h2 : k < X
      · have h3 : ¬ X < k := by omega
        simp [Ty.substTy, h1, h2, h3, interp, Env.insert]
      · have h3 : X < k := by omega
        simp [Ty.substTy, h1, h2, h3, interp, Env.insert]
  | .fvar _, _, _, _ => rfl
  | .mu a S, k, ζ, η => by
    simp only [Ty.substTy, interp]
    have : (fun c 𝒳 => interpAt W ρ θ (Ty.substTyList S (k + 1) T) c ζ (Env.cons 𝒳 η)) =
        (fun c 𝒳 => interpAt W ρ θ S c ζ (Env.cons 𝒳 (Env.insert k (interp W ρ θ T ζ η) η))) := by
      funext c 𝒳
      rw [interpAt_substTy W ρ θ hT S c (k + 1), hT ζ ζ (Env.cons 𝒳 η) η, Env.insert_succ_cons]
    rw [this]
  | .nu a R, k, ζ, η => by
    simp only [Ty.substTy, interp]
    rw [Ty.substTyList_length]
    have : (fun d 𝒳 => interpAt W ρ θ (Ty.substTyList R (k + 1) T) d ζ (Env.cons 𝒳 η)) =
        (fun d 𝒳 => interpAt W ρ θ R d ζ (Env.cons 𝒳 (Env.insert k (interp W ρ θ T ζ η) η))) := by
      funext d 𝒳
      rw [interpAt_substTy W ρ θ hT R d (k + 1), hT ζ ζ (Env.cons 𝒳 η) η, Env.insert_succ_cons]
    rw [this]
  | .allT B, k, ζ, η => by
    simp only [Ty.substTy, interp]
    have : (fun 𝒳 => interp W ρ θ (B.substTy (k + 1) T) ζ (Env.cons 𝒳 η)) =
        (fun 𝒳 => interp W ρ θ B ζ (Env.cons 𝒳 (Env.insert k (interp W ρ θ T ζ η) η))) := by
      funext 𝒳
      rw [interp_substTy W ρ θ hT B (k + 1), hT ζ ζ (Env.cons 𝒳 η) η, Env.insert_succ_cons]
    rw [this]
  | .exT B, k, ζ, η => by
    simp only [Ty.substTy, interp]
    have : (fun 𝒳 => interp W ρ θ (B.substTy (k + 1) T) ζ (Env.cons 𝒳 η)) =
        (fun 𝒳 => interp W ρ θ B ζ (Env.cons 𝒳 (Env.insert k (interp W ρ θ T ζ η) η))) := by
      funext 𝒳
      rw [interp_substTy W ρ θ hT B (k + 1), hT ζ ζ (Env.cons 𝒳 η) η, Env.insert_succ_cons]
    rw [this]
  | .allS a B, k, ζ, η => by
    simp only [Ty.substTy, interp]
    have : (fun β => interp W ρ θ (B.substTy k T) (SzEnv.cons β ζ) η) =
        (fun β => interp W ρ θ B (SzEnv.cons β ζ) (Env.insert k (interp W ρ θ T ζ η) η)) := by
      funext β
      rw [interp_substTy W ρ θ hT B k, hT (SzEnv.cons β ζ) ζ η η]
    rw [this]
  | .exS a B, k, ζ, η => by
    simp only [Ty.substTy, interp]
    have : (fun β => interp W ρ θ (B.substTy k T) (SzEnv.cons β ζ) η) =
        (fun β => interp W ρ θ B (SzEnv.cons β ζ) (Env.insert k (interp W ρ θ T ζ η) η)) := by
      funext β
      rw [interp_substTy W ρ θ hT B k, hT (SzEnv.cons β ζ) ζ η η]
    rw [this]

theorem interpAt_substTy (W : World) (ρ : SizeVal) (θ : TEnv) {T : Ty} (hT : EnvFree W ρ θ T) :
    ∀ (S : List Ty) (c k : Nat) (ζ : SzEnv) (η : Env),
      interpAt W ρ θ (Ty.substTyList S k T) c ζ η =
        interpAt W ρ θ S c ζ (Env.insert k (interp W ρ θ T ζ η) η)
  | [], c, _, _, _ => by cases c <;> rfl
  | A :: _, 0, k, ζ, η => interp_substTy W ρ θ hT A k ζ η
  | _ :: S, c + 1, k, ζ, η => interpAt_substTy W ρ θ hT S c k ζ η

end

/-! ## Opening bound size variables -/

theorem sizeVal_openAt (ρ : SizeVal) (ζ : SzEnv) (k j m : Nat) (a : Size) :
    sizeVal ρ ζ (a.openAt k (.var j m)) =
      sizeVal ρ (SzEnv.insert k (sizeVal ρ ζ (.var j m)) ζ) a := by
  cases a with
  | inf => rfl
  | var i n => rfl
  | bvar k' n =>
    by_cases h1 : k' = k
    · subst h1
      simp [Size.openAt, Size.shift, sizeVal, SzEnv.insert, Nat.cast_add, add_assoc]
    · by_cases h2 : k < k'
      · have h3 : ¬ k' < k := by omega
        simp [Size.openAt, h1, h2, h3, sizeVal, SzEnv.insert]
      · have h3 : k' < k := by omega
        simp [Size.openAt, h1, h2, h3, sizeVal, SzEnv.insert]

theorem Ty.openSzList_length (k : Nat) (b : Size) :
    ∀ S : List Ty, (Ty.openSzList S k b).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.openSzList, Ty.openSzList_length k b S]

mutual

theorem interp_openSz (W : World) (ρ : SizeVal) (θ : TEnv) (j m : Nat) :
    ∀ (A : Ty) (k : Nat) (ζ : SzEnv) (η : Env),
      interp W ρ θ (A.openSz k (.var j m)) ζ η =
        interp W ρ θ A (SzEnv.insert k (sizeVal ρ ζ (.var j m)) ζ) η
  | .unit, _, _, _ => rfl
  | .prod A B, k, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [interp_openSz W ρ θ j m A k ζ η, interp_openSz W ρ θ j m B k ζ η]
  | .arr A B, k, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [interp_openSz W ρ θ j m A k ζ η, interp_openSz W ρ θ j m B k ζ η]
  | .var _, _, _, _ => rfl
  | .fvar _, _, _, _ => rfl
  | .mu a S, k, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [sizeVal_openAt]
    have : (fun c 𝒳 => interpAt W ρ θ (Ty.openSzList S k (.var j m)) c ζ (Env.cons 𝒳 η)) =
        (fun c 𝒳 => interpAt W ρ θ S c (SzEnv.insert k (sizeVal ρ ζ (.var j m)) ζ)
          (Env.cons 𝒳 η)) := by
      funext c 𝒳; exact interpAt_openSz W ρ θ j m S c k ζ _
    rw [this]
  | .nu a R, k, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [sizeVal_openAt, Ty.openSzList_length]
    have : (fun d 𝒳 => interpAt W ρ θ (Ty.openSzList R k (.var j m)) d ζ (Env.cons 𝒳 η)) =
        (fun d 𝒳 => interpAt W ρ θ R d (SzEnv.insert k (sizeVal ρ ζ (.var j m)) ζ)
          (Env.cons 𝒳 η)) := by
      funext d 𝒳; exact interpAt_openSz W ρ θ j m R d k ζ _
    rw [this]
  | .allT B, k, ζ, η => by
    simp only [Ty.openSz, interp]
    have : (fun 𝒳 => interp W ρ θ (B.openSz k (.var j m)) ζ (Env.cons 𝒳 η)) =
        (fun 𝒳 => interp W ρ θ B (SzEnv.insert k (sizeVal ρ ζ (.var j m)) ζ)
          (Env.cons 𝒳 η)) := by
      funext 𝒳; exact interp_openSz W ρ θ j m B k ζ _
    rw [this]
  | .exT B, k, ζ, η => by
    simp only [Ty.openSz, interp]
    have : (fun 𝒳 => interp W ρ θ (B.openSz k (.var j m)) ζ (Env.cons 𝒳 η)) =
        (fun 𝒳 => interp W ρ θ B (SzEnv.insert k (sizeVal ρ ζ (.var j m)) ζ)
          (Env.cons 𝒳 η)) := by
      funext 𝒳; exact interp_openSz W ρ θ j m B k ζ _
    rw [this]
  | .allS a B, k, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [sizeVal_openAt]
    have : (fun β => interp W ρ θ (B.openSz (k + 1) (.var j m)) (SzEnv.cons β ζ) η) =
        (fun β => interp W ρ θ B
          (SzEnv.cons β (SzEnv.insert k (sizeVal ρ ζ (.var j m)) ζ)) η) := by
      funext β
      rw [interp_openSz W ρ θ j m B (k + 1)]
      simp only [sizeVal]
      rw [SzEnv.insert_succ_cons]
    rw [this]
  | .exS a B, k, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [sizeVal_openAt]
    have : (fun β => interp W ρ θ (B.openSz (k + 1) (.var j m)) (SzEnv.cons β ζ) η) =
        (fun β => interp W ρ θ B
          (SzEnv.cons β (SzEnv.insert k (sizeVal ρ ζ (.var j m)) ζ)) η) := by
      funext β
      rw [interp_openSz W ρ θ j m B (k + 1)]
      simp only [sizeVal]
      rw [SzEnv.insert_succ_cons]
    rw [this]

theorem interpAt_openSz (W : World) (ρ : SizeVal) (θ : TEnv) (j m : Nat) :
    ∀ (S : List Ty) (c k : Nat) (ζ : SzEnv) (η : Env),
      interpAt W ρ θ (Ty.openSzList S k (.var j m)) c ζ η =
        interpAt W ρ θ S c (SzEnv.insert k (sizeVal ρ ζ (.var j m)) ζ) η
  | [], c, _, _, _ => by cases c <;> rfl
  | A :: _, 0, k, ζ, η => interp_openSz W ρ θ j m A k ζ η
  | _ :: S, c + 1, k, ζ, η => interpAt_openSz W ρ θ j m S c k ζ η

end

/-! ## Substitution of free type variables -/

/-- The type valuation induced by a substitution of types for free type variables. -/
noncomputable def substTVal (W : World) (ρ : SizeVal) (θ : TEnv) (τ : List (Nat × Ty)) : TEnv :=
  fun X =>
    match τ.lookup X with
    | some T => interp W ρ θ T SzEnv.zero Env.empty
    | none => θ X

theorem Ty.substFTyList_length (τ : List (Nat × Ty)) :
    ∀ S : List Ty, (Ty.substFTyList τ S).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.substFTyList, Ty.substFTyList_length τ S]

mutual

theorem interp_substFTy (W : World) (ρ : SizeVal) (θ : TEnv) {τ : List (Nat × Ty)}
    (hτ : ∀ X T, τ.lookup X = some T → EnvFree W ρ θ T) :
    ∀ (A : Ty) (ζ : SzEnv) (η : Env),
      interp W ρ θ (A.substFTy τ) ζ η = interp W ρ (substTVal W ρ θ τ) A ζ η
  | .unit, _, _ => rfl
  | .prod A B, ζ, η => by
    simp only [Ty.substFTy, interp]
    rw [interp_substFTy W ρ θ hτ A ζ η, interp_substFTy W ρ θ hτ B ζ η]
  | .arr A B, ζ, η => by
    simp only [Ty.substFTy, interp]
    rw [interp_substFTy W ρ θ hτ A ζ η, interp_substFTy W ρ θ hτ B ζ η]
  | .var _, _, _ => rfl
  | .fvar X, ζ, η => by
    show interp W ρ θ ((τ.lookup X).getD (.fvar X)) ζ η = substTVal W ρ θ τ X
    unfold substTVal
    cases h : τ.lookup X with
    | none => rfl
    | some T => exact hτ X T h ζ SzEnv.zero η Env.empty
  | .mu a S, ζ, η => by
    simp only [Ty.substFTy, interp]
    have : (fun c 𝒳 => interpAt W ρ θ (Ty.substFTyList τ S) c ζ (Env.cons 𝒳 η)) =
        (fun c 𝒳 => interpAt W ρ (substTVal W ρ θ τ) S c ζ (Env.cons 𝒳 η)) := by
      funext c 𝒳; exact interpAt_substFTy W ρ θ hτ S c ζ _
    rw [this]
  | .nu a R, ζ, η => by
    simp only [Ty.substFTy, interp]
    rw [Ty.substFTyList_length]
    have : (fun d 𝒳 => interpAt W ρ θ (Ty.substFTyList τ R) d ζ (Env.cons 𝒳 η)) =
        (fun d 𝒳 => interpAt W ρ (substTVal W ρ θ τ) R d ζ (Env.cons 𝒳 η)) := by
      funext d 𝒳; exact interpAt_substFTy W ρ θ hτ R d ζ _
    rw [this]
  | .allT B, ζ, η => by
    simp only [Ty.substFTy, interp]
    have : (fun 𝒳 => interp W ρ θ (B.substFTy τ) ζ (Env.cons 𝒳 η)) =
        (fun 𝒳 => interp W ρ (substTVal W ρ θ τ) B ζ (Env.cons 𝒳 η)) := by
      funext 𝒳; exact interp_substFTy W ρ θ hτ B ζ _
    rw [this]
  | .exT B, ζ, η => by
    simp only [Ty.substFTy, interp]
    have : (fun 𝒳 => interp W ρ θ (B.substFTy τ) ζ (Env.cons 𝒳 η)) =
        (fun 𝒳 => interp W ρ (substTVal W ρ θ τ) B ζ (Env.cons 𝒳 η)) := by
      funext 𝒳; exact interp_substFTy W ρ θ hτ B ζ _
    rw [this]
  | .allS a B, ζ, η => by
    simp only [Ty.substFTy, interp]
    have : (fun β => interp W ρ θ (B.substFTy τ) (SzEnv.cons β ζ) η) =
        (fun β => interp W ρ (substTVal W ρ θ τ) B (SzEnv.cons β ζ) η) := by
      funext β; exact interp_substFTy W ρ θ hτ B _ η
    rw [this]
  | .exS a B, ζ, η => by
    simp only [Ty.substFTy, interp]
    have : (fun β => interp W ρ θ (B.substFTy τ) (SzEnv.cons β ζ) η) =
        (fun β => interp W ρ (substTVal W ρ θ τ) B (SzEnv.cons β ζ) η) := by
      funext β; exact interp_substFTy W ρ θ hτ B _ η
    rw [this]

theorem interpAt_substFTy (W : World) (ρ : SizeVal) (θ : TEnv) {τ : List (Nat × Ty)}
    (hτ : ∀ X T, τ.lookup X = some T → EnvFree W ρ θ T) :
    ∀ (S : List Ty) (c : Nat) (ζ : SzEnv) (η : Env),
      interpAt W ρ θ (Ty.substFTyList τ S) c ζ η = interpAt W ρ (substTVal W ρ θ τ) S c ζ η
  | [], c, _, _ => by cases c <;> rfl
  | A :: _, 0, ζ, η => interp_substFTy W ρ θ hτ A ζ η
  | _ :: S, c + 1, ζ, η => interpAt_substFTy W ρ θ hτ S c ζ η

end

/-! ## Unfolding and opening -/

theorem envFree_of_closed {W : World} {Ψ : SizeCtx} {Θ : List Nat} {T : Ty} (hT : TyWf Ψ Θ 0 0 T)
    (ρ : SizeVal) (θ : TEnv) : EnvFree W ρ θ T :=
  fun ζ ζ' η η' => interp_closed_env hT ρ θ ζ ζ' η η'

/-- Unfolding a branch: `⟦S_c[μ^b S]⟧ = ⟦S_c⟧(stage ⟦b⟧)`. -/
theorem interp_unfold_mu {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {b : Size} {S : List Ty} {c : Nat} (hc : c < S.length) (hwf : TyWf Ψ Θ 0 0 (.mu b S))
    (ζ : SzEnv) (η : Env) :
    interp W ρ θ ((S[c]'hc).substTy 0 (.mu b S)) ζ η =
      interpAt W ρ θ S c ζ (Env.cons (MuSet W (fun c 𝒳 => interpAt W ρ θ S c ζ (Env.cons 𝒳 η))
        (sizeVal ρ ζ b)) η) := by
  rw [interp_substTy W ρ θ (envFree_of_closed hwf ρ θ) _ 0 ζ η, Env.insert_zero,
    interpAt_eq W ρ θ S c _ _ hc]
  rfl

theorem interp_unfold_nu {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {b : Size} {R : List Ty} {d : Nat} (hd : d < R.length) (hwf : TyWf Ψ Θ 0 0 (.nu b R))
    (ζ : SzEnv) (η : Env) :
    interp W ρ θ ((R[d]'hd).substTy 0 (.nu b R)) ζ η =
      interpAt W ρ θ R d ζ (Env.cons (NuSet W R.length
        (fun d 𝒳 => interpAt W ρ θ R d ζ (Env.cons 𝒳 η)) (sizeVal ρ ζ b)) η) := by
  rw [interp_substTy W ρ θ (envFree_of_closed hwf ρ θ) _ 0 ζ η, Env.insert_zero,
    interpAt_eq W ρ θ R d _ _ hd]
  rfl

/-- Opening `∀X`/`∃X` with a type. -/
theorem interp_openTy {W : World} {ρ : SizeVal} {θ : TEnv} {T : Ty} (hT : EnvFree W ρ θ T)
    (B : Ty) (ζ : SzEnv) (η : Env) :
    interp W ρ θ (B.substTy 0 T) ζ η = interp W ρ θ B ζ (Env.cons (interp W ρ θ T ζ η) η) := by
  rw [interp_substTy W ρ θ hT B 0 ζ η, Env.insert_zero]

/-- Opening `∀(j<a)`/`∃(j<a)` with a size variable. -/
theorem interp_openSz0 (W : World) (ρ : SizeVal) (θ : TEnv) (j m : Nat) (B : Ty) (ζ : SzEnv)
    (η : Env) :
    interp W ρ θ (B.openSz 0 (.var j m)) ζ η =
      interp W ρ θ B (SzEnv.cons (sizeVal ρ ζ (.var j m)) ζ) η := by
  rw [interp_openSz W ρ θ j m B 0 ζ η, SzEnv.insert_zero]

end NishtAbel2024V4
