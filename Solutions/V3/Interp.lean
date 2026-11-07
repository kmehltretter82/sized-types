import Solutions.V3.Stable

/-! # V3: size soundness and substitution lemmas for the interpretation -/

namespace NishtAbel2024V3

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

theorem sizeVal_le_omega {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {a : Size}
    (ha : SizeWf Ψ a) : sizeVal ρ a ≤ Omega := by
  cases a with
  | inf => exact le_rfl
  | var i n => exact (add_nat_lt_omega (hv.lt_omega ha) n).le

theorem sizeVal_shift (ρ : SizeVal) (j m n : Nat) :
    sizeVal ρ ((Size.var j m).shift n) = sizeVal ρ (.var j m) + n := by
  simp [Size.shift, sizeVal, Nat.cast_add, add_assoc]

/-- Size soundness (Theorem 2, strict part). -/
theorem sizeLt_sound {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {a b : Size}
    (h : SizeLt Ψ a b) : sizeVal ρ a < sizeVal ρ b := by
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
      rw [sizeVal_shift]
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
    (h : SizeLe Ψ a b) : sizeVal ρ a ≤ sizeVal ρ b := by
  rcases h with ⟨rfl, _⟩ | ⟨rfl, ha⟩ | h | ⟨i, n, m, rfl, rfl, hnm, _⟩
  · exact le_rfl
  · exact sizeVal_le_omega hv ha
  · exact (sizeLt_sound hv h).le
  · simp only [sizeVal]
    exact add_le_add_right (by exact_mod_cast hnm) _

theorem sizeBelow_sound {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {b a : Size}
    (h : SizeBelow Ψ b a) :
    sizeVal ρ b < sizeVal ρ a ∨ (b = .inf ∧ a = .inf) := by
  rcases h with h | h
  · exact Or.inl (sizeLt_sound hv h)
  · exact Or.inr h

/-! ## Agreement of valuations and environments -/

theorem sizeVal_agree {Ψ : SizeCtx} {ρ ρ' : SizeVal} (hag : ∀ i ∈ Ψ.dom, ρ i = ρ' i) {a : Size}
    (ha : SizeWf Ψ a) : sizeVal ρ a = sizeVal ρ' a := by
  cases a with
  | inf => rfl
  | var i n => simp only [sizeVal, hag i ha]

theorem interp_agree {W : World} {Ψ : SizeCtx} {k : Nat} {A : Ty} (hA : TyWf Ψ k A) :
    ∀ (ρ ρ' : SizeVal) (η η' : Env), (∀ i ∈ Ψ.dom, ρ i = ρ' i) → (∀ X < k, η X = η' X) →
      interp W ρ A η = interp W ρ' A η' := by
  induction hA with
  | unit k => intro _ _ _ _ _ _; rfl
  | prod _ _ ihA ihB =>
    intro ρ ρ' η η' hr he
    simp only [interp]; rw [ihA ρ ρ' η η' hr he, ihB ρ ρ' η η' hr he]
  | arr _ _ ihA ihB =>
    intro ρ ρ' η η' hr he
    simp only [interp]; rw [ihA ρ ρ' η η' hr he, ihB ρ ρ' η η' hr he]
  | var hX => intro _ _ η η' _ he; exact he _ hX
  | @mu k a S ha _ _ ih =>
    intro ρ ρ' η η' hr he
    simp only [interp]
    rw [sizeVal_agree hr ha]
    have : (fun c 𝒳 => interpAt W ρ S c (Env.cons 𝒳 η)) =
        (fun c 𝒳 => interpAt W ρ' S c (Env.cons 𝒳 η')) := by
      funext c 𝒳
      by_cases hc : c < S.length
      · rw [interpAt_eq W ρ S c _ hc, interpAt_eq W ρ' S c _ hc]
        apply ih _ (List.getElem_mem hc) _ _ _ _ hr
        intro X hX
        cases X with
        | zero => rfl
        | succ X => exact he X (by omega)
      · rw [interpAt_out W ρ S c _ (by omega), interpAt_out W ρ' S c _ (by omega)]
    rw [this]
  | @nu k a R ha _ _ ih =>
    intro ρ ρ' η η' hr he
    simp only [interp]
    rw [sizeVal_agree hr ha]
    have : (fun d 𝒳 => interpAt W ρ R d (Env.cons 𝒳 η)) =
        (fun d 𝒳 => interpAt W ρ' R d (Env.cons 𝒳 η')) := by
      funext d 𝒳
      by_cases hd : d < R.length
      · rw [interpAt_eq W ρ R d _ hd, interpAt_eq W ρ' R d _ hd]
        apply ih _ (List.getElem_mem hd) _ _ _ _ hr
        intro X hX
        cases X with
        | zero => rfl
        | succ X => exact he X (by omega)
      · rw [interpAt_out W ρ R d _ (by omega), interpAt_out W ρ' R d _ (by omega)]
    rw [this]

/-- Closed types do not depend on the environment. -/
theorem interp_closed_env {W : World} {Ψ : SizeCtx} {A : Ty} (hA : TyWf Ψ 0 A) (ρ : SizeVal)
    (η η' : Env) : interp W ρ A η = interp W ρ A η' :=
  interp_agree hA ρ ρ η η' (fun _ _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _))

/-! ## Size substitution -/

/-- The valuation induced by a size substitution. -/
noncomputable def substVal (ρ : SizeVal) (σ : List (Nat × Size)) : SizeVal := fun i =>
  match σ.lookup i with
  | some b => sizeVal ρ b
  | none => ρ i

/-- Substitutions whose values are variable sizes. -/
def VarSubst (σ : List (Nat × Size)) : Prop := ∀ i b, σ.lookup i = some b → ∃ j m, b = .var j m

theorem sizeVal_subst {σ : List (Nat × Size)} (hσ : VarSubst σ) (ρ : SizeVal) (a : Size) :
    sizeVal ρ (a.subst σ) = sizeVal (substVal ρ σ) a := by
  cases a with
  | inf => rfl
  | var i n =>
    simp only [Size.subst, sizeVal, substVal]
    cases h : σ.lookup i with
    | none => rfl
    | some b =>
      obtain ⟨j, m, rfl⟩ := hσ i _ h
      simp [Size.shift, Nat.cast_add, add_assoc]

theorem Ty.substSizeList_length (σ : List (Nat × Size)) :
    ∀ S : List Ty, (Ty.substSizeList σ S).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.substSizeList, Ty.substSizeList_length σ S]

mutual

theorem interp_substSize (W : World) (ρ : SizeVal) {σ : List (Nat × Size)} (hσ : VarSubst σ) :
    ∀ (A : Ty) (η : Env), interp W ρ (A.substSize σ) η = interp W (substVal ρ σ) A η
  | .unit, _ => rfl
  | .prod A B, η => by
    simp only [Ty.substSize, interp]
    rw [interp_substSize W ρ hσ A η, interp_substSize W ρ hσ B η]
  | .arr A B, η => by
    simp only [Ty.substSize, interp]
    rw [interp_substSize W ρ hσ A η, interp_substSize W ρ hσ B η]
  | .var _, _ => rfl
  | .mu a S, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ]
    have : (fun c 𝒳 => interpAt W ρ (Ty.substSizeList σ S) c (Env.cons 𝒳 η)) =
        (fun c 𝒳 => interpAt W (substVal ρ σ) S c (Env.cons 𝒳 η)) := by
      funext c 𝒳; exact interpAt_substSize W ρ hσ S c _
    rw [this]
  | .nu a R, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ, Ty.substSizeList_length]
    have : (fun d 𝒳 => interpAt W ρ (Ty.substSizeList σ R) d (Env.cons 𝒳 η)) =
        (fun d 𝒳 => interpAt W (substVal ρ σ) R d (Env.cons 𝒳 η)) := by
      funext d 𝒳; exact interpAt_substSize W ρ hσ R d _
    rw [this]

theorem interpAt_substSize (W : World) (ρ : SizeVal) {σ : List (Nat × Size)} (hσ : VarSubst σ) :
    ∀ (S : List Ty) (c : Nat) (η : Env),
      interpAt W ρ (Ty.substSizeList σ S) c η = interpAt W (substVal ρ σ) S c η
  | [], c, _ => by cases c <;> rfl
  | A :: _, 0, η => interp_substSize W ρ hσ A η
  | _ :: S, c + 1, η => interpAt_substSize W ρ hσ S c η

end

/-! ## Type substitution -/

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

theorem Ty.substTyList_length (k : Nat) (T : Ty) :
    ∀ S : List Ty, (Ty.substTyList S k T).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.substTyList, Ty.substTyList_length k T S]

mutual

theorem interp_substTy (W : World) (ρ : SizeVal) {T : Ty}
    (hT : ∀ η η', interp W ρ T η = interp W ρ T η') :
    ∀ (A : Ty) (k : Nat) (η : Env),
      interp W ρ (A.substTy k T) η = interp W ρ A (Env.insert k (interp W ρ T η) η)
  | .unit, _, _ => rfl
  | .prod A B, k, η => by
    simp only [Ty.substTy, interp]
    rw [interp_substTy W ρ hT A k η, interp_substTy W ρ hT B k η]
  | .arr A B, k, η => by
    simp only [Ty.substTy, interp]
    rw [interp_substTy W ρ hT A k η, interp_substTy W ρ hT B k η]
  | .var X, k, η => by
    by_cases h1 : X = k
    · subst h1; simp [Ty.substTy, interp, Env.insert]
    · by_cases h2 : k < X
      · have h3 : ¬ X < k := by omega
        simp [Ty.substTy, h1, h2, h3, interp, Env.insert]
      · have h3 : X < k := by omega
        simp [Ty.substTy, h1, h2, h3, interp, Env.insert]
  | .mu a S, k, η => by
    simp only [Ty.substTy, interp]
    have : (fun c 𝒳 => interpAt W ρ (Ty.substTyList S (k + 1) T) c (Env.cons 𝒳 η)) =
        (fun c 𝒳 => interpAt W ρ S c (Env.cons 𝒳 (Env.insert k (interp W ρ T η) η))) := by
      funext c 𝒳
      rw [interpAt_substTy W ρ hT S c (k + 1), hT (Env.cons 𝒳 η) η, Env.insert_succ_cons]
    rw [this]
  | .nu a R, k, η => by
    simp only [Ty.substTy, interp]
    rw [Ty.substTyList_length]
    have : (fun d 𝒳 => interpAt W ρ (Ty.substTyList R (k + 1) T) d (Env.cons 𝒳 η)) =
        (fun d 𝒳 => interpAt W ρ R d (Env.cons 𝒳 (Env.insert k (interp W ρ T η) η))) := by
      funext d 𝒳
      rw [interpAt_substTy W ρ hT R d (k + 1), hT (Env.cons 𝒳 η) η, Env.insert_succ_cons]
    rw [this]

theorem interpAt_substTy (W : World) (ρ : SizeVal) {T : Ty}
    (hT : ∀ η η', interp W ρ T η = interp W ρ T η') :
    ∀ (S : List Ty) (c k : Nat) (η : Env),
      interpAt W ρ (Ty.substTyList S k T) c η =
        interpAt W ρ S c (Env.insert k (interp W ρ T η) η)
  | [], c, _, _ => by cases c <;> rfl
  | A :: _, 0, k, η => interp_substTy W ρ hT A k η
  | _ :: S, c + 1, k, η => interpAt_substTy W ρ hT S c k η

end

/-- Unfolding a branch: `⟦S_c[μ^b S]⟧ = ⟦S_c⟧(stage ⟦b⟧)`. -/
theorem interp_unfold_mu {W : World} {Ψ : SizeCtx} {ρ : SizeVal} {b : Size} {S : List Ty} {c : Nat}
    (hc : c < S.length) (hwf : TyWf Ψ 0 (.mu b S)) (η : Env) :
    interp W ρ ((S[c]'hc).substTy 0 (.mu b S)) η =
      interpAt W ρ S c (Env.cons (MuSet W (fun c 𝒳 => interpAt W ρ S c (Env.cons 𝒳 η))
        (sizeVal ρ b)) η) := by
  rw [interp_substTy W ρ (interp_closed_env hwf ρ) _ 0 η, Env.insert_zero, interpAt_eq W ρ S c _ hc]
  rfl

theorem interp_unfold_nu {W : World} {Ψ : SizeCtx} {ρ : SizeVal} {b : Size} {R : List Ty} {d : Nat}
    (hd : d < R.length) (hwf : TyWf Ψ 0 (.nu b R)) (η : Env) :
    interp W ρ ((R[d]'hd).substTy 0 (.nu b R)) η =
      interpAt W ρ R d (Env.cons (NuSet W R.length
        (fun d 𝒳 => interpAt W ρ R d (Env.cons 𝒳 η)) (sizeVal ρ b)) η) := by
  rw [interp_substTy W ρ (interp_closed_env hwf ρ) _ 0 η, Env.insert_zero, interpAt_eq W ρ R d _ hd]
  rfl

end NishtAbel2024V3
