import Solutions.V5.InfCompare
import Solutions.V5.Spine

/-! # V5 inference: rigid variables of (co)patterns (Theorems 8 and 9) -/

namespace NishtAbel2024V5

/-! ## Theorems 8 and 9 -/

/-- Theorem 8: pattern inference yields pattern typing. -/
theorem inferPat_sound {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} (h : InferPat Ψ Θ p A Γ Ψ' Θ') : PatTy Ψ Θ p A Γ Ψ' Θ' := by
  induction h with
  | var => exact .var _ _ _ _
  | unit => exact .unit _ _
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | cons hc _ hj _ ih => exact .cons hc hj ih
  | pack hX _ ih => exact .packT hX ih

/-- Theorem 9: copattern-spine inference yields spine typing. -/
theorem inferSpine_sound {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty} (h : InferSpine Ψ Θ qs A Γ Ψ' Θ' C) :
    SpineTy Ψ Θ qs A Γ Ψ' Θ' C := by
  induction h with
  | nil => exact .nil _ _ _
  | pat hp _ ih => exact .pat (inferPat_sound hp) ih
  | proj hd _ hj _ ih => exact .proj hd hj ih
  | inst hX _ ih => exact .instT hX ih

/-! ## Flexible substitutions -/

/-- The domain of a flexible substitution consists of flexible names. -/
def FlexDom (φ : FlexSubst) : Prop := ∀ p ∈ φ, FlexName p.1

theorem FlexDom.lookup_rigid {φ : FlexSubst} (hφ : FlexDom φ) {i : Nat} (hi : RigidName i) :
    φ.lookup i = none := by
  cases hl : φ.lookup i with
  | none => rfl
  | some b =>
    have := hφ _ (lookup_mem_gen hl)
    simp [FlexName] at this
    simp [RigidName] at hi
    omega

theorem FlexDom.subst_rigid {φ : FlexSubst} (hφ : FlexDom φ) {i : Nat} (hi : RigidName i)
    (n : Nat) : (Size.var i n).subst φ = .var i n := by
  simp [Size.subst, hφ.lookup_rigid hi]

/-- Substituting into the types of a term context. -/
def TermCtx.substSize (φ : FlexSubst) (Γ : TermCtx) : TermCtx :=
  Γ.map fun p => (p.1, p.2.substSize φ)

@[simp] theorem TermCtx.substSize_append (φ : FlexSubst) (Γ₁ Γ₂ : TermCtx) :
    (Γ₁ ++ Γ₂).substSize φ = Γ₁.substSize φ ++ Γ₂.substSize φ := by
  simp [TermCtx.substSize]

theorem TermCtx.lookup_substSize (φ : FlexSubst) :
    ∀ (Γ : TermCtx) (x : Nat), (Γ.substSize φ).lookup x = (Γ.lookup x).map (Ty.substSize φ)
  | [], _ => rfl
  | (y, B) :: Γ, x => by
    by_cases h : x = y
    · subst h; simp [TermCtx.substSize, List.lookup]
    · have hb : (x == y) = false := by simpa using h
      have := TermCtx.lookup_substSize φ Γ x
      simp only [TermCtx.substSize] at this
      simp only [TermCtx.substSize, List.map_cons, List.lookup, hb]
      exact this

@[simp] theorem SizeCtx.substBounds_append (φ : FlexSubst) (Ψ₁ Ψ₂ : SizeCtx) :
    (Ψ₁ ++ Ψ₂).substBounds φ = Ψ₁.substBounds φ ++ Ψ₂.substBounds φ := by
  simp [SizeCtx.substBounds]

@[simp] theorem SizeCtx.substBounds_cons (φ : FlexSubst) (p : Nat × Size) (Ψ : SizeCtx) :
    SizeCtx.substBounds φ (p :: Ψ) = (p.1, p.2.subst φ) :: Ψ.substBounds φ := rfl

@[simp] theorem SizeCtx.substBounds_nil (φ : FlexSubst) : SizeCtx.substBounds φ [] = [] := rfl

theorem Ty.substSizeList_getElem?_some {σ : List (Nat × Size)} {S : List Ty} {c : Nat} {T : Ty}
    (h : S[c]? = some T) : (Ty.substSizeList σ S)[c]? = some (T.substSize σ) := by
  rw [Ty.substSizeList_getElem?, h]; rfl

/-- Pattern inference under a flexible substitution yields pattern typing. -/
theorem inferPat_subst {φ : FlexSubst} (hφ : FlexDom φ) {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat}
    {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : TyCtx} (h : InferPat Ψ Θ p A Γ Ψ' Θ') :
    PatTy (Ψ.substBounds φ) Θ p (A.substSize φ) (Γ.substSize φ) (Ψ'.substBounds φ) Θ' := by
  induction h with
  | var Ψ Θ x A => exact .var _ _ _ _
  | unit Ψ Θ => exact .unit _ _
  | pair _ _ ih₁ ih₂ =>
    simp only [Ty.substSize, TermCtx.substSize_append, SizeCtx.substBounds_append]
    exact .pair ih₁ (by simpa using ih₂)
  | @cons Ψ Ψ' Θ Θ' c j p a S Sc Γ hc hrig hj _ ih =>
    simp only [Ty.substSize, SizeCtx.substBounds_cons]
    refine .cons (Ty.substSizeList_getElem?_some hc)
      (by rwa [SizeCtx.substBounds_dom]) ?_
    have := ih
    rw [SizeCtx.substBounds_append, Ty.substSize_substTy] at this
    simpa [SizeCtx.substBounds, Ty.substSize, hφ.subst_rigid hrig] using this
  | @pack Ψ Ψ' Θ Θ' X κ p B Γ hX _ ih =>
    simp only [Ty.substSize]
    refine .packT hX ?_
    have := ih
    rw [Ty.substSize_substTy] at this
    simpa [Ty.substSize] using this

/-- Spine inference under a flexible substitution yields spine typing. -/
theorem inferSpine_subst {φ : FlexSubst} (hφ : FlexDom φ) {Ψ : SizeCtx} {Θ : TyCtx}
    {qs : List Copat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty}
    (h : InferSpine Ψ Θ qs A Γ Ψ' Θ' C) :
    SpineTy (Ψ.substBounds φ) Θ qs (A.substSize φ) (Γ.substSize φ) (Ψ'.substBounds φ) Θ'
      (C.substSize φ) := by
  induction h with
  | nil => exact .nil _ _ _
  | pat hp _ ih =>
    simp only [Ty.substSize, TermCtx.substSize_append, SizeCtx.substBounds_append]
    exact .pat (inferPat_subst hφ hp) (by simpa using ih)
  | @proj Ψ Ψ' Θ Θ' d j qs a R Rd C Γ hd hrig hj _ ih =>
    simp only [Ty.substSize, SizeCtx.substBounds_cons]
    refine .proj (Ty.substSizeList_getElem?_some hd) (by rwa [SizeCtx.substBounds_dom]) ?_
    have := ih
    rw [SizeCtx.substBounds_append, Ty.substSize_substTy] at this
    simpa [SizeCtx.substBounds, Ty.substSize, hφ.subst_rigid hrig] using this
  | @inst Ψ Ψ' Θ Θ' X κ qs B C Γ hX _ ih =>
    simp only [Ty.substSize]
    refine .instT hX ?_
    have := ih
    rw [Ty.substSize_substTy] at this
    simpa [Ty.substSize] using this

/-! ## Kinding of the outputs of spine typing -/

theorem patTy_kinding {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} (h : PatTy Ψ Θ p A Γ Ψ' Θ') :
    KindingC Ψ Θ.toK A .star → TermCtxWf (Ψ ++ Ψ') (Θ ++ Θ') Γ := by
  induction h with
  | var Ψ Θ x A =>
    intro hA q hq
    simp at hq; subst hq; simpa using hA
  | unit => intro _ q hq; simp at hq
  | @pair Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p q A B Γ₁ Γ₂ _ _ ih₁ ih₂ =>
    intro hAB
    obtain ⟨_, hA, hB⟩ := Kinding.inv_prod hAB
    have hΓ₁ := ih₁ hA
    have hΓ₂ := ih₂ (by rw [TyCtx.toK_append]; exact KindingC.mono_append hB)
    exact TermCtxWf.merge hΓ₁ hΓ₂
  | @cons Ψ Ψ' Θ Θ' c j p a S Sc Γ hc hj _ ih =>
    intro hA
    have hA' : KindingC (Ψ ++ [(j, a)]) Θ.toK (.mu a S) .star := hA.mono_append_sz
    have := ih (hA'.unfold_mu (TyCtx.toK_allMix Θ) (b := .var j 0) hc (sizeWf_fresh_var _ _ _))
    simpa using this
  | @packT Ψ Ψ' Θ Θ' X κ p B Γ hX _ ih =>
    intro hA
    have := ih (KindingC.open_fresh_ty (Kinding.inv_exT hA).2 hX)
    simpa using this
  | @packS Ψ Ψ' Θ Θ' j p a B Γ hj _ ih =>
    intro hA
    obtain ⟨_, _, hB⟩ := Kinding.inv_exS hA
    have := ih (KindingC.open_fresh_sz hB j a)
    simpa using this

theorem spineTy_kinding {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty} (h : SpineTy Ψ Θ qs A Γ Ψ' Θ' C) :
    KindingC Ψ Θ.toK A .star →
      TermCtxWf (Ψ ++ Ψ') (Θ ++ Θ') Γ ∧ KindingC (Ψ ++ Ψ') (Θ ++ Θ').toK C .star := by
  induction h with
  | nil Ψ Θ A => intro hA; exact ⟨fun _ h => by simp at h, by simpa using hA⟩
  | @pat Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p qs A B C Γ₁ Γ₂ hp _ ih =>
    intro hAB
    obtain ⟨_, hA, hB⟩ := Kinding.inv_arr hAB
    rw [(TyCtx.toK_allMix Θ).inv] at hA
    have hA' : KindingC Ψ Θ.toK A .star := by simpa using hA
    have hΓ₁ := patTy_kinding hp hA'
    obtain ⟨hΓ₂, hC⟩ := ih (by rw [TyCtx.toK_append]; exact KindingC.mono_append hB)
    exact ⟨TermCtxWf.merge hΓ₁ hΓ₂, by simpa using hC⟩
  | @proj Ψ Ψ' Θ Θ' d j qs a R Rd C Γ hd hj _ ih =>
    intro hA
    have hA' : KindingC (Ψ ++ [(j, a)]) Θ.toK (.nu a R) .star := hA.mono_append_sz
    obtain ⟨hΓ, hC⟩ := ih (hA'.unfold_nu (TyCtx.toK_allMix Θ) (b := .var j 0) hd
      (sizeWf_fresh_var _ _ _))
    exact ⟨by simpa using hΓ, by simpa using hC⟩
  | @instT Ψ Ψ' Θ Θ' X κ qs B C Γ hX _ ih =>
    intro hA
    obtain ⟨hΓ, hC⟩ := ih (KindingC.open_fresh_ty (Kinding.inv_allT hA).2 hX)
    exact ⟨by simpa using hΓ, by simpa using hC⟩
  | @instS Ψ Ψ' Θ Θ' j qs a B C Γ hj _ ih =>
    intro hA
    obtain ⟨_, _, hB⟩ := Kinding.inv_allS hA
    obtain ⟨hΓ, hC⟩ := ih (KindingC.open_fresh_sz hB j a)
    exact ⟨by simpa using hΓ, by simpa using hC⟩

end NishtAbel2024V5
