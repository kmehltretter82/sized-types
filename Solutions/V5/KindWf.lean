import Solutions.V5.Wf

/-! # V5: syntactic lemmas about kinding -/

namespace NishtAbel2024V5

/-! ## Contexts -/

@[simp] theorem KCtx.dom_inv (π : Pol) (Δ : KCtx) : (Δ.inv π).dom = Δ.dom := by
  simp [KCtx.inv, KCtx.dom]

@[simp] theorem BCtx.length_inv (π : Pol) (Δb : BCtx) : (Δb.inv π).length = Δb.length := by
  simp [BCtx.inv]

@[simp] theorem BCtx.inv_append (π : Pol) (Δb Δb' : BCtx) :
    (Δb ++ Δb').inv π = Δb.inv π ++ Δb'.inv π := by
  simp [BCtx.inv]

@[simp] theorem BCtx.inv_cons (π : Pol) (e : Pol × Kind) (Δb : BCtx) :
    BCtx.inv π (e :: Δb) = (Pol.inv π e.1, e.2) :: Δb.inv π := rfl

@[simp] theorem BCtx.inv_nil (π : Pol) : BCtx.inv π [] = [] := rfl

@[simp] theorem KCtx.inv_append (π : Pol) (Δ Δ' : KCtx) : (Δ ++ Δ').inv π = Δ.inv π ++ Δ'.inv π := by
  simp [KCtx.inv]

theorem KCtx.lookup_some_dom {Δ : KCtx} {X : Nat} {e : Pol × Kind} (h : Δ.lookup X = some e) :
    X ∈ Δ.dom := by
  induction Δ with
  | nil => simp [List.lookup] at h
  | cons p Δ ih =>
    obtain ⟨Y, e'⟩ := p
    by_cases hXY : X = Y
    · subst hXY; simp [KCtx.dom]
    · have hb : (X == Y) = false := by simpa using hXY
      simp only [List.lookup, hb] at h
      simp only [KCtx.dom, List.map_cons, List.mem_cons]
      exact Or.inr (ih h)

/-- All variables have mixed polarity. -/
def KCtx.AllMix (Δ : KCtx) : Prop := ∀ e ∈ Δ, e.2.1 = .mix

theorem KCtx.AllMix.inv {Δ : KCtx} (h : Δ.AllMix) (π : Pol) : Δ.inv π = Δ := by
  unfold KCtx.inv
  conv_rhs => rw [← List.map_id Δ]
  apply List.map_congr_left
  intro e he
  obtain ⟨X, π', κ⟩ := e
  have : π' = .mix := h _ he
  subst this
  cases π <;> rfl

theorem TyCtx.toK_allMix (Θ : TyCtx) : Θ.toK.AllMix := by
  intro e he
  simp only [TyCtx.toK, List.mem_map] at he
  obtain ⟨_, _, rfl⟩ := he
  rfl

@[simp] theorem TyCtx.toK_append (Θ Θ' : TyCtx) : (Θ ++ Θ').toK = Θ.toK ++ Θ'.toK := by
  simp [TyCtx.toK]

@[simp] theorem TyCtx.toK_dom (Θ : TyCtx) : Θ.toK.dom = Θ.map Prod.fst := by
  simp [TyCtx.toK, KCtx.dom]

theorem TyCtx.toK_lookup (Θ : TyCtx) (X : Nat) :
    Θ.toK.lookup X = (Θ.lookup X).map fun κ => (Pol.mix, κ) := by
  induction Θ with
  | nil => rfl
  | cons p Θ ih =>
    obtain ⟨Y, κ⟩ := p
    by_cases h : X = Y
    · subst h; simp [TyCtx.toK, List.lookup]
    · have hb : (X == Y) = false := by simpa using h
      simp only [TyCtx.toK, List.map_cons, List.lookup, hb] at ih ⊢
      exact ih

/-! ## Subkinding -/

theorem SubKind.trans : ∀ {κ₁ κ₂ κ₃ : Kind}, SubKind κ₁ κ₂ → SubKind κ₂ κ₃ → SubKind κ₁ κ₃
  | _, .star, _, h₁, h₂ => by cases h₁; cases h₂; exact .star
  | _, .arr _ _ _, _, h₁, h₂ => by
    cases h₁ with
    | arr hπ ha hb =>
      cases h₂ with
      | arr hπ' ha' hb' => exact .arr (Pol.le_trans hπ' hπ) (SubKind.trans ha' ha) (SubKind.trans hb hb')

theorem SubKind.star_left {κ : Kind} (h : SubKind .star κ) : κ = .star := by
  cases h; rfl

theorem SubKind.star_right {κ : Kind} (h : SubKind κ .star) : κ = .star := by
  cases h; rfl

/-! ## Kinding implies scoping -/

theorem Kinding.tyWf {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m A κ) : TyWf Ψ Δ.dom Δb.length m A := by
  induction h with
  | unit => exact .unit _ _
  | prod _ _ ihA ihB => exact .prod ihA ihB
  | arr _ _ ihA ihB =>
    simp only [KCtx.dom_inv, BCtx.length_inv] at ihA
    exact .arr ihA ihB
  | var hk _ => exact .var (List.getElem?_eq_some_iff.mp hk).1
  | fvar hX _ => exact .fvar (KCtx.lookup_some_dom hX)
  | lam _ _ ih => exact .lam (by simpa using ih)
  | app _ _ _ ihF ihG =>
    simp only [KCtx.dom_inv, BCtx.length_inv] at ihG
    exact .app ihF ihG
  | mu _ ha _ ih =>
    refine .mu ha fun T hT => ?_
    have := ih T hT
    simpa using this
  | nu _ ha _ ih =>
    refine .nu ha fun T hT => ?_
    have := ih T hT
    simpa using this
  | allT _ ih => exact .allT (by simpa using ih)
  | exT _ ih => exact .exT (by simpa using ih)
  | allS ha _ ih => exact .allS ha ih
  | exS ha _ ih => exact .exS ha ih
  | sub _ _ ih => exact ih

theorem KindingC.tyWf {Ψ : SizeCtx} {Δ : KCtx} {A : Ty} {κ : Kind} (h : KindingC Ψ Δ A κ) :
    TyWf Ψ Δ.dom 0 0 A :=
  Kinding.tyWf h

/-! ## Inversion -/

theorem Kinding.inv_mu {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {a : Size} {S : List Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.mu a S) κ) :
    κ = .star ∧ ∃ π, (π = .pos ∨ π = .mix) ∧ SizeWfAt Ψ m a ∧
      ∀ T ∈ S, Kinding Ψ (Δ.inv π) ((π, .star) :: Δb.inv π) m T .star := by
  generalize hA : Ty.mu a S = A at h
  induction h with
  | mu hπ ha hS => cases hA; exact ⟨rfl, _, hπ, ha, hS⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hA
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hA

theorem Kinding.inv_nu {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {a : Size} {R : List Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.nu a R) κ) :
    κ = .star ∧ ∃ π, (π = .pos ∨ π = .mix) ∧ SizeWfAt Ψ m a ∧
      ∀ T ∈ R, Kinding Ψ (Δ.inv π) ((π, .star) :: Δb.inv π) m T .star := by
  generalize hA : Ty.nu a R = A at h
  induction h with
  | nu hπ ha hR => cases hA; exact ⟨rfl, _, hπ, ha, hR⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hA
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hA

theorem Kinding.inv_allT {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {κ₀ : Kind} {B : Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.allT κ₀ B) κ) :
    κ = .star ∧ Kinding Ψ Δ ((.mix, κ₀) :: Δb) m B .star := by
  generalize hA : Ty.allT κ₀ B = A at h
  induction h with
  | allT hB => cases hA; exact ⟨rfl, hB⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hA
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hA

theorem Kinding.inv_exT {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {κ₀ : Kind} {B : Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.exT κ₀ B) κ) :
    κ = .star ∧ Kinding Ψ Δ ((.mix, κ₀) :: Δb) m B .star := by
  generalize hA : Ty.exT κ₀ B = A at h
  induction h with
  | exT hB => cases hA; exact ⟨rfl, hB⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hA
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hA

theorem Kinding.inv_allS {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {a : Size} {B : Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.allS a B) κ) :
    κ = .star ∧ SizeWfAt Ψ m a ∧ Kinding Ψ Δ Δb (m + 1) B .star := by
  generalize hA : Ty.allS a B = A at h
  induction h with
  | allS ha hB => cases hA; exact ⟨rfl, ha, hB⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hA
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hA

theorem Kinding.inv_exS {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {a : Size} {B : Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.exS a B) κ) :
    κ = .star ∧ SizeWfAt Ψ m a ∧ Kinding Ψ Δ Δb (m + 1) B .star := by
  generalize hA : Ty.exS a B = A at h
  induction h with
  | exS ha hB => cases hA; exact ⟨rfl, ha, hB⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hA
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hA

theorem Kinding.inv_prod {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A B : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m (.prod A B) κ) :
    κ = .star ∧ Kinding Ψ Δ Δb m A .star ∧ Kinding Ψ Δ Δb m B .star := by
  generalize hT : Ty.prod A B = T at h
  induction h with
  | prod hA hB => cases hT; exact ⟨rfl, hA, hB⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hT
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hT

theorem Kinding.inv_arr {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A B : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m (.arr A B) κ) :
    κ = .star ∧ Kinding Ψ (Δ.inv .neg) (Δb.inv .neg) m A .star ∧ Kinding Ψ Δ Δb m B .star := by
  generalize hT : Ty.arr A B = T at h
  induction h with
  | arr hA hB => cases hT; exact ⟨rfl, hA, hB⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hT
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hT

theorem Kinding.inv_lam {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {ι : SKind} {F : Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.lam ι F) κ) :
    ∃ π κ₁ κ₂, κ₁.erase = ι ∧ Kinding Ψ Δ ((π, κ₁) :: Δb) m F κ₂ ∧
      SubKind (.arr π κ₁ κ₂) κ := by
  generalize hT : Ty.lam ι F = T at h
  induction h with
  | lam hι hF => cases hT; exact ⟨_, _, _, hι, hF, SubKind.refl _⟩
  | sub _ hsub ih =>
    obtain ⟨π, κ₁, κ₂, hι, hF, hs⟩ := ih hT
    exact ⟨π, κ₁, κ₂, hι, hF, hs.trans hsub⟩
  | _ => cases hT

theorem Kinding.inv_app {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {F G : Ty} {ι : SKind}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.app F G ι) κ) :
    ∃ π κ₁ κ₂, Kinding Ψ Δ Δb m F (.arr π κ₁ κ₂) ∧ Kinding Ψ (Δ.inv π) (Δb.inv π) m G κ₁ ∧
      κ₁.erase = ι ∧ SubKind κ₂ κ := by
  generalize hT : Ty.app F G ι = T at h
  induction h with
  | app hF hG hι => cases hT; exact ⟨_, _, _, hF, hG, hι, SubKind.refl _⟩
  | sub _ hsub ih =>
    obtain ⟨π, κ₁, κ₂, hF, hG, hι, hs⟩ := ih hT
    exact ⟨π, κ₁, κ₂, hF, hG, hι, hs.trans hsub⟩
  | _ => cases hT

theorem Kinding.inv_fvar {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m X : Nat} {κ : Kind}
    (h : Kinding Ψ Δ Δb m (.fvar X) κ) :
    ∃ π κ', Δ.lookup X = some (π, κ') ∧ π.Usable ∧ SubKind κ' κ := by
  generalize hT : Ty.fvar X = T at h
  induction h with
  | fvar hX hπ => cases hT; exact ⟨_, _, hX, hπ, SubKind.refl _⟩
  | sub _ hsub ih =>
    obtain ⟨π, κ', hX, hπ, hs⟩ := ih hT
    exact ⟨π, κ', hX, hπ, hs.trans hsub⟩
  | _ => cases hT

/-! ## Weakening -/

theorem Kinding.weaken {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m A κ) :
    ∀ {Ψ' : SizeCtx} {Δ' : KCtx} {Δb' : BCtx} {m' : Nat}, (∀ i ∈ Ψ.dom, i ∈ Ψ'.dom) →
      (∀ (X : Nat) (e : Pol × Kind), Δ.lookup X = some e → Δ'.lookup X = some e) →
      (∀ (k : Nat) (e : Pol × Kind), Δb[k]? = some e → Δb'[k]? = some e) → m ≤ m' →
      Kinding Ψ' Δ' Δb' m' A κ := by
  have invΔ : ∀ (π : Pol) {Δ Δ' : KCtx},
      (∀ (X : Nat) (e : Pol × Kind), Δ.lookup X = some e → Δ'.lookup X = some e) →
      ∀ (X : Nat) (e : Pol × Kind), (Δ.inv π).lookup X = some e → (Δ'.inv π).lookup X = some e := by
    intro π Δ Δ' hΔ X e hX
    rw [KCtx.lookup_inv] at hX ⊢
    obtain ⟨e', hX', rfl⟩ := Option.map_eq_some_iff.mp hX
    rw [hΔ X e' hX']
    rfl
  have invΔb : ∀ (π : Pol) {Δb Δb' : BCtx},
      (∀ (k : Nat) (e : Pol × Kind), Δb[k]? = some e → Δb'[k]? = some e) →
      ∀ (k : Nat) (e : Pol × Kind), (Δb.inv π)[k]? = some e → (Δb'.inv π)[k]? = some e := by
    intro π Δb Δb' hΔb k e hk
    rw [BCtx.getElem?_inv] at hk ⊢
    obtain ⟨e', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
    rw [hΔb k e' hk']
    rfl
  have consΔb : ∀ (e₀ : Pol × Kind) {Δb Δb' : BCtx},
      (∀ (k : Nat) (e : Pol × Kind), Δb[k]? = some e → Δb'[k]? = some e) →
      ∀ (k : Nat) (e : Pol × Kind), (e₀ :: Δb)[k]? = some e → (e₀ :: Δb')[k]? = some e := by
    intro e₀ Δb Δb' hΔb k e hk
    cases k with
    | zero => simpa using hk
    | succ k => simpa using hΔb k e (by simpa using hk)
  induction h with
  | unit => intros; exact .unit
  | prod _ _ ihA ihB =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .prod (ihA hΨ hΔ hΔb hm) (ihB hΨ hΔ hΔb hm)
  | arr _ _ ihA ihB =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .arr (ihA hΨ (invΔ _ hΔ) (invΔb _ hΔb) hm) (ihB hΨ hΔ hΔb hm)
  | var hk hπ =>
    intro Ψ' Δ' Δb' m' _ _ hΔb _
    exact .var (hΔb _ _ hk) hπ
  | fvar hX hπ =>
    intro Ψ' Δ' Δb' m' _ hΔ _ _
    exact .fvar (hΔ _ _ hX) hπ
  | lam hι _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .lam hι (ih hΨ hΔ (consΔb _ hΔb) hm)
  | app _ _ hι ihF ihG =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .app (ihF hΨ hΔ hΔb hm) (ihG hΨ (invΔ _ hΔ) (invΔb _ hΔb) hm) hι
  | mu hπ ha _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .mu hπ (ha.weaken hΨ hm)
      (fun T hT => ih T hT hΨ (invΔ _ hΔ) (consΔb _ (invΔb _ hΔb)) hm)
  | nu hπ ha _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .nu hπ (ha.weaken hΨ hm)
      (fun T hT => ih T hT hΨ (invΔ _ hΔ) (consΔb _ (invΔb _ hΔb)) hm)
  | allT _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .allT (ih hΨ hΔ (consΔb _ hΔb) hm)
  | exT _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .exT (ih hΨ hΔ (consΔb _ hΔb) hm)
  | allS ha _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .allS (ha.weaken hΨ hm) (ih hΨ hΔ hΔb (by omega))
  | exS ha _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .exS (ha.weaken hΨ hm) (ih hΨ hΔ hΔb (by omega))
  | sub _ hs ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .sub (ih hΨ hΔ hΔb hm) hs

/-- A locally closed type is kinded under any bound contexts. -/
theorem KindingC.weakenB {Ψ : SizeCtx} {Δ : KCtx} {T : Ty} {κ : Kind} (h : KindingC Ψ Δ T κ)
    (Δb : BCtx) (m : Nat) : Kinding Ψ Δ Δb m T κ :=
  Kinding.weaken h (fun _ h => h) (fun _ _ h => h) (fun _ _ h => by simp at h) (Nat.zero_le _)

/-- Extending the contexts by fresh variables. -/
theorem KindingC.mono {Ψ Ψ' : SizeCtx} {Δ Δ' : KCtx} {T : Ty} {κ : Kind} (h : KindingC Ψ Δ T κ)
    (hΨ : ∀ i ∈ Ψ.dom, i ∈ Ψ'.dom)
    (hΔ : ∀ (X : Nat) (e : Pol × Kind), Δ.lookup X = some e → Δ'.lookup X = some e) :
    KindingC Ψ' Δ' T κ :=
  Kinding.weaken h hΨ hΔ (fun _ _ h => h) le_rfl

theorem lookup_append_left {Δ Δ' : KCtx} {X : Nat} {e : Pol × Kind} (h : Δ.lookup X = some e) :
    (Δ ++ Δ').lookup X = some e := by
  induction Δ with
  | nil => simp [List.lookup] at h
  | cons p Δ ih =>
    obtain ⟨Y, e'⟩ := p
    by_cases hXY : X = Y
    · subst hXY; simpa [List.lookup] using h
    · have hb : (X == Y) = false := by simpa using hXY
      simp only [List.lookup, hb, List.cons_append] at h ⊢
      exact ih h

/-! ## Substitution of the outermost bound type variable -/

theorem Kinding.substTy_last {Ψ : SizeCtx} {Δ : KCtx} {Δb' : BCtx} {m : Nat} {A : Ty}
    {κA : Kind} (h : Kinding Ψ Δ Δb' m A κA) :
    ∀ {Δb : BCtx} {π : Pol} {κ : Kind} {T : Ty}, Δb' = Δb ++ [(π, κ)] → Δ.AllMix →
      KindingC Ψ Δ T κ → Kinding Ψ Δ Δb m (A.substTy Δb.length T) κA := by
  induction h with
  | unit => intros; exact .unit
  | prod _ _ ihA ihB =>
    intro Δb π κ T he hΔ hT
    exact .prod (ihA he hΔ hT) (ihB he hΔ hT)
  | @arr Δ Δb₀ m A B _ _ ihA ihB =>
    intro Δb π κ T he hΔ hT
    have hA := @ihA (Δb.inv .neg) (Pol.inv .neg π) κ T (by rw [he]; simp)
      (by rw [hΔ.inv]; exact hΔ) (by rw [hΔ.inv]; exact hT)
    rw [BCtx.length_inv] at hA
    exact .arr hA (ihB he hΔ hT)
  | @var Δ Δb₀ m k π' κ' hk hπ' =>
    intro Δb π κ T he hΔ hT
    subst he
    simp only [Ty.substTy]
    by_cases h1 : k = Δb.length
    · subst h1
      simp only [if_true]
      simp at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact hT.weakenB _ m
    · have hlt : k < Δb.length := by
        have := (List.getElem?_eq_some_iff.mp hk).1
        simp at this; omega
      have h2 : ¬ Δb.length < k := by omega
      simp only [h1, h2, if_false]
      refine .var ?_ hπ'
      rw [List.getElem?_append_left hlt] at hk
      exact hk
  | fvar hX hπ => intros; exact .fvar hX hπ
  | @lam Δ Δb₀ m ι F π' κ₁ κ₂ hι _ ih =>
    intro Δb π κ T he hΔ hT
    have := @ih ((π', κ₁) :: Δb) π κ T (by rw [he]; rfl) hΔ hT
    exact .lam hι (by simpa using this)
  | @app Δ Δb₀ m F G ι π' κ₁ κ₂ _ _ hι ihF ihG =>
    intro Δb π κ T he hΔ hT
    have hG := @ihG (Δb.inv π') (Pol.inv π' π) κ T (by rw [he]; simp)
      (by rw [hΔ.inv]; exact hΔ) (by rw [hΔ.inv]; exact hT)
    rw [BCtx.length_inv] at hG
    exact .app (ihF he hΔ hT) hG hι
  | @mu Δ Δb₀ m a S π' hπ' ha _ ih =>
    intro Δb π κ T he hΔ hT
    simp only [Ty.substTy]
    refine .mu hπ' ha fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    have := @ih B hB ((π', .star) :: Δb.inv π') (Pol.inv π' π) κ T (by rw [he]; simp)
      (by rw [hΔ.inv]; exact hΔ) (by rw [hΔ.inv]; exact hT)
    simpa using this
  | @nu Δ Δb₀ m a R π' hπ' ha _ ih =>
    intro Δb π κ T he hΔ hT
    simp only [Ty.substTy]
    refine .nu hπ' ha fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    have := @ih B hB ((π', .star) :: Δb.inv π') (Pol.inv π' π) κ T (by rw [he]; simp)
      (by rw [hΔ.inv]; exact hΔ) (by rw [hΔ.inv]; exact hT)
    simpa using this
  | @allT Δ Δb₀ m κ₀ B _ ih =>
    intro Δb π κ T he hΔ hT
    have := @ih ((.mix, κ₀) :: Δb) π κ T (by rw [he]; rfl) hΔ hT
    exact .allT (by simpa using this)
  | @exT Δ Δb₀ m κ₀ B _ ih =>
    intro Δb π κ T he hΔ hT
    have := @ih ((.mix, κ₀) :: Δb) π κ T (by rw [he]; rfl) hΔ hT
    exact .exT (by simpa using this)
  | allS ha _ ih =>
    intro Δb π κ T he hΔ hT
    exact .allS ha (ih he hΔ hT)
  | exS ha _ ih =>
    intro Δb π κ T he hΔ hT
    exact .exS ha (ih he hΔ hT)
  | sub _ hs ih =>
    intro Δb π κ T he hΔ hT
    exact .sub (ih he hΔ hT) hs

/-- Opening a type binder of a locally closed type. -/
theorem Kinding.open_ty {Ψ : SizeCtx} {Δ : KCtx} {π : Pol} {κ κB : Kind} {B T : Ty}
    (hB : Kinding Ψ Δ [(π, κ)] 0 B κB) (hΔ : Δ.AllMix) (hT : KindingC Ψ Δ T κ) :
    KindingC Ψ Δ (B.substTy 0 T) κB :=
  hB.substTy_last (Δb := []) rfl hΔ hT

/-! ## Opening the outermost bound size variable -/

theorem Kinding.openSz {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {n : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb n A κ) :
    ∀ (m : Nat) (c : Size), n = m + 1 → SizeWf Ψ c → Kinding Ψ Δ Δb m (A.openSz m c) κ := by
  induction h with
  | unit => intros; exact .unit
  | prod _ _ ihA ihB => intro m c hn hc; exact .prod (ihA m c hn hc) (ihB m c hn hc)
  | arr _ _ ihA ihB => intro m c hn hc; exact .arr (ihA m c hn hc) (ihB m c hn hc)
  | var hk hπ => intros; exact .var hk hπ
  | fvar hX hπ => intros; exact .fvar hX hπ
  | lam hι _ ih => intro m c hn hc; exact .lam hι (ih m c hn hc)
  | app _ _ hι ihF ihG => intro m c hn hc; exact .app (ihF m c hn hc) (ihG m c hn hc) hι
  | mu hπ ha _ ih =>
    intro m c hn hc
    simp only [Ty.openSz]
    refine .mu hπ (SizeWfAt.openAt m hn hc ha) fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_openSzList hT'
    exact ih B hB m c hn hc
  | nu hπ ha _ ih =>
    intro m c hn hc
    simp only [Ty.openSz]
    refine .nu hπ (SizeWfAt.openAt m hn hc ha) fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_openSzList hT'
    exact ih B hB m c hn hc
  | allT _ ih => intro m c hn hc; exact .allT (ih m c hn hc)
  | exT _ ih => intro m c hn hc; exact .exT (ih m c hn hc)
  | allS ha _ ih =>
    intro m c hn hc
    exact .allS (SizeWfAt.openAt m hn hc ha) (ih (m + 1) c (by omega) hc)
  | exS ha _ ih =>
    intro m c hn hc
    exact .exS (SizeWfAt.openAt m hn hc ha) (ih (m + 1) c (by omega) hc)
  | sub _ hs ih => intro m c hn hc; exact .sub (ih m c hn hc) hs

theorem Kinding.open_sz {Ψ : SizeCtx} {Δ : KCtx} {B : Ty} {c : Size} {κ : Kind}
    (hB : Kinding Ψ Δ [] 1 B κ) (hc : SizeWf Ψ c) : KindingC Ψ Δ (B.openSz 0 c) κ :=
  hB.openSz 0 c rfl hc

/-! ## Substitution of free size variables -/

theorem SizeWfAt.subst {Ψ Ψ' : SizeCtx} {m : Nat} {σ : List (Nat × Size)}
    (hσ : ∀ i ∈ Ψ.dom, SizeWf Ψ' ((Size.var i 0).subst σ)) :
    ∀ {a : Size}, SizeWfAt Ψ m a → SizeWfAt Ψ' m (a.subst σ)
  | .inf _, _ => trivial
  | .bvar _ _, h => h
  | .var i n, h => by
    have hi := hσ i h
    simp only [Size.subst] at hi ⊢
    cases hl : σ.lookup i with
    | none =>
      simp only [hl] at hi ⊢
      exact hi
    | some b =>
      simp only [hl, Size.shift_zero] at hi ⊢
      exact (SizeWfAt.shift n hi).weaken (fun _ h => h) (Nat.zero_le _)
  | .meet _ _, h => ⟨SizeWfAt.subst hσ h.1, SizeWfAt.subst hσ h.2⟩

theorem Kinding.substSize {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m A κ) {Ψ' : SizeCtx} {σ : List (Nat × Size)}
    (hσ : ∀ i ∈ Ψ.dom, SizeWf Ψ' ((Size.var i 0).subst σ)) :
    Kinding Ψ' Δ Δb m (A.substSize σ) κ := by
  induction h with
  | unit => exact .unit
  | prod _ _ ihA ihB => exact .prod ihA ihB
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | var hk hπ => exact .var hk hπ
  | fvar hX hπ => exact .fvar hX hπ
  | lam hι _ ih => exact .lam hι ih
  | app _ _ hι ihF ihG => exact .app ihF ihG hι
  | mu hπ ha _ ih =>
    simp only [Ty.substSize]
    refine .mu hπ (SizeWfAt.subst hσ ha) fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substSizeList hT'
    exact ih B hB
  | nu hπ ha _ ih =>
    simp only [Ty.substSize]
    refine .nu hπ (SizeWfAt.subst hσ ha) fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substSizeList hT'
    exact ih B hB
  | allT _ ih => exact .allT ih
  | exT _ ih => exact .exT ih
  | allS ha _ ih => exact .allS (SizeWfAt.subst hσ ha) ih
  | exS ha _ ih => exact .exS (SizeWfAt.subst hσ ha) ih
  | sub _ hs ih => exact .sub ih hs

/-! ## Substitution of free type variables (mixed contexts) -/

theorem Kinding.substFTy {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m A κ) :
    Δ.AllMix → ∀ {Δ' : KCtx} {τ : List (Nat × Ty)}, Δ'.AllMix →
      (∀ X π κ', Δ.lookup X = some (π, κ') →
        (∃ T, τ.lookup X = some T ∧ KindingC Ψ Δ' T κ') ∨
          (τ.lookup X = none ∧ Δ'.lookup X = some (π, κ'))) →
      Kinding Ψ Δ' Δb m (A.substFTy τ) κ := by
  induction h with
  | unit => intros; exact .unit
  | prod _ _ ihA ihB =>
    intro hΔ Δ' τ hΔ' hτ
    exact .prod (ihA hΔ hΔ' hτ) (ihB hΔ hΔ' hτ)
  | @arr Δ Δb m A B _ _ ihA ihB =>
    intro hΔ Δ' τ hΔ' hτ
    have hA := ihA (by rw [hΔ.inv]; exact hΔ) hΔ' (by rw [hΔ.inv]; exact hτ)
    exact .arr (by rw [hΔ'.inv]; exact hA) (ihB hΔ hΔ' hτ)
  | var hk hπ => intros; exact .var hk hπ
  | @fvar Δ Δb m X π κ' hX hπ =>
    intro hΔ Δ' τ hΔ' hτ
    simp only [Ty.substFTy]
    rcases hτ X π κ' hX with ⟨T, hT, hTk⟩ | ⟨hT, hX'⟩
    · rw [hT]; exact hTk.weakenB Δb m
    · rw [hT]; exact .fvar hX' hπ
  | lam hι _ ih =>
    intro hΔ Δ' τ hΔ' hτ
    exact .lam hι (ih hΔ hΔ' hτ)
  | @app Δ Δb m F G ι π κ₁ κ₂ _ _ hι ihF ihG =>
    intro hΔ Δ' τ hΔ' hτ
    have hG := ihG (by rw [hΔ.inv]; exact hΔ) hΔ' (by rw [hΔ.inv]; exact hτ)
    exact .app (ihF hΔ hΔ' hτ) (by rw [hΔ'.inv]; exact hG) hι
  | @mu Δ Δb m a S π hπ ha _ ih =>
    intro hΔ Δ' τ hΔ' hτ
    simp only [Ty.substFTy]
    refine .mu hπ ha fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substFTyList hT'
    have := ih B hB (by rw [hΔ.inv]; exact hΔ) hΔ' (by rw [hΔ.inv]; exact hτ)
    rw [hΔ'.inv]
    exact this
  | @nu Δ Δb m a R π hπ ha _ ih =>
    intro hΔ Δ' τ hΔ' hτ
    simp only [Ty.substFTy]
    refine .nu hπ ha fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substFTyList hT'
    have := ih B hB (by rw [hΔ.inv]; exact hΔ) hΔ' (by rw [hΔ.inv]; exact hτ)
    rw [hΔ'.inv]
    exact this
  | allT _ ih => intro hΔ Δ' τ hΔ' hτ; exact .allT (ih hΔ hΔ' hτ)
  | exT _ ih => intro hΔ Δ' τ hΔ' hτ; exact .exT (ih hΔ hΔ' hτ)
  | allS ha _ ih => intro hΔ Δ' τ hΔ' hτ; exact .allS ha (ih hΔ hΔ' hτ)
  | exS ha _ ih => intro hΔ Δ' τ hΔ' hτ; exact .exS ha (ih hΔ hΔ' hτ)
  | sub _ hs ih => intro hΔ Δ' τ hΔ' hτ; exact .sub (ih hΔ hΔ' hτ) hs

end NishtAbel2024V5
