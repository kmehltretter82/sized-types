import Solutions.V5.InfEncode

/-! # V5 inference: rigid variable classification (Lemmas 4–5) and constraint analysis
(Theorems 10–12) -/

namespace NishtAbel2024V5

/-! ## Fixpoint-index occurrences and `Ty.indexes` -/

theorem mem_indexesList_of_mem {fk : FixKind} {i : Nat} {S : List Ty} {T : Ty}
    (hT : T ∈ S) (hi : T.indexes fk i = true) : Ty.indexesList fk i S = true := by
  induction S with
  | nil => simp at hT
  | cons A S ih =>
    simp only [Ty.indexesList, Bool.or_eq_true]
    rcases List.mem_cons.mp hT with rfl | hT
    · exact Or.inl hi
    · exact Or.inr (ih hT)

theorem SizeOcc.indexes {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol} {A : Ty}
    (h : SizeOcc fk i Δ Δb π A) : A.indexes fk i = true := by
  induction h with
  | prodL _ ih | arrL _ ih | appF _ ih =>
    simp [Ty.indexes, ih]
  | prodR _ ih | arrR _ ih | appG _ _ ih =>
    simp [Ty.indexes, ih]
  | lam _ ih | allT _ ih | exT _ ih | allS _ ih | exS _ ih =>
    simpa [Ty.indexes] using ih
  | mu_here hfk hi =>
    subst hfk
    simp [Ty.indexes, hi]
  | nu_here hfk hi =>
    subst hfk
    simp [Ty.indexes, hi]
  | mu_body hT _ ih =>
    simp [Ty.indexes, mem_indexesList_of_mem hT ih]
  | nu_body hT _ ih =>
    simp [Ty.indexes, mem_indexesList_of_mem hT ih]

mutual

theorem Ty.indexes_substTy_sub (fk : FixKind) (i k : Nat) (U : Ty) :
    ∀ (A : Ty), (A.substTy k U).indexes fk i = true →
      A.indexes fk i = true ∨ U.indexes fk i = true
  | .unit, h => by simp [Ty.substTy, Ty.indexes] at h
  | .fvar _, h => by simp [Ty.substTy, Ty.indexes] at h
  | .var X, h => by
    simp only [Ty.substTy] at h
    split at h
    · exact Or.inr h
    · split at h <;> simp [Ty.indexes] at h
  | .prod A B, h => by
    simp only [Ty.substTy, Ty.indexes, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases Ty.indexes_substTy_sub fk i k U A h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases Ty.indexes_substTy_sub fk i k U B h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | .arr A B, h => by
    simp only [Ty.substTy, Ty.indexes, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases Ty.indexes_substTy_sub fk i k U A h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases Ty.indexes_substTy_sub fk i k U B h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | .app A B _, h => by
    simp only [Ty.substTy, Ty.indexes, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases Ty.indexes_substTy_sub fk i k U A h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases Ty.indexes_substTy_sub fk i k U B h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | .lam _ F, h => Ty.indexes_substTy_sub fk i (k + 1) U F h
  | .allT _ F, h => Ty.indexes_substTy_sub fk i (k + 1) U F h
  | .exT _ F, h => Ty.indexes_substTy_sub fk i (k + 1) U F h
  | .allS _ F, h => Ty.indexes_substTy_sub fk i k U F h
  | .exS _ F, h => Ty.indexes_substTy_sub fk i k U F h
  | .mu a S, h => by
    simp only [Ty.substTy, Ty.indexes, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · rcases Ty.indexesList_substTyList_sub fk i (k + 1) U S h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | .nu a S, h => by
    simp only [Ty.substTy, Ty.indexes, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · rcases Ty.indexesList_substTyList_sub fk i (k + 1) U S h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem Ty.indexesList_substTyList_sub (fk : FixKind) (i k : Nat) (U : Ty) :
    ∀ (S : List Ty), Ty.indexesList fk i (Ty.substTyList S k U) = true →
      Ty.indexesList fk i S = true ∨ U.indexes fk i = true
  | [], h => by simp [Ty.substTyList, Ty.indexesList] at h
  | A :: S, h => by
    simp only [Ty.substTyList, Ty.indexesList, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases Ty.indexes_substTy_sub fk i k U A h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases Ty.indexesList_substTyList_sub fk i k U S h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

end

/-! ## Lemmas 4 & 5: Rigid variables in patterns and copattern spines (Section 6.2) -/

theorem inferPat_rigid {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
    {Θ' : TyCtx} (h : InferPat Ψ Θ p A Γ Ψ' Θ') : ∀ q ∈ Ψ', RigidName q.1 := by
  induction h with
  | var => intro _ h; simp at h
  | unit => intro _ h; simp at h
  | pair _ _ ih₁ ih₂ =>
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ih₁ q hq
    · exact ih₂ q hq
  | cons _ hj _ _ ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hj
    · exact ih q hq
  | pack _ _ ih => exact ih

theorem inferPat_indexes {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} (h : InferPat Ψ Θ p A Γ Ψ' Θ') :
    ∀ {fk : FixKind} {i : Nat} {xB : Nat × Ty}, xB ∈ Γ → xB.2.indexes fk i = true →
      A.indexes fk i = true ∨ (fk = .mu ∧ i ∈ Ψ'.dom) := by
  induction h with
  | var =>
    intro fk i xB hxB hidx
    simp only [List.mem_singleton] at hxB
    subst hxB
    exact Or.inl hidx
  | unit =>
    intro _ _ _ hxB
    simp at hxB
  | pair _ _ ih₁ ih₂ =>
    intro fk i xB hxB hidx
    rcases List.mem_append.mp hxB with hxB | hxB
    · rcases ih₁ hxB hidx with hA | ⟨rfl, hi⟩
      · exact Or.inl (by simp [Ty.indexes, hA])
      · exact Or.inr ⟨rfl, by simp only [SizeCtx.dom_append, List.mem_append]; exact Or.inl hi⟩
    · rcases ih₂ hxB hidx with hB | ⟨rfl, hi⟩
      · exact Or.inl (by simp [Ty.indexes, hB])
      · exact Or.inr ⟨rfl, by simp only [SizeCtx.dom_append, List.mem_append]; exact Or.inr hi⟩
  | cons hc _ _ _ ih =>
    intro fk i xB hxB hidx
    rcases ih hxB hidx with hsub | ⟨rfl, hi⟩
    · rcases Ty.indexes_substTy_sub fk i 0 (.mu (.var _ 0) _) _ hsub with hSc | hmu
      · exact Or.inl (by simp [Ty.indexes, mem_indexesList_of_mem (List.mem_of_getElem? hc) hSc])
      · simp only [Ty.indexes, Size.fvars, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
          List.contains_iff_mem, List.mem_singleton] at hmu
        rcases hmu with ⟨rfl, rfl⟩ | hS
        · exact Or.inr ⟨rfl, by simp [SizeCtx.dom]⟩
        · exact Or.inl (by simp [Ty.indexes, hS])
    · exact Or.inr ⟨rfl, by simp only [SizeCtx.dom_cons, List.mem_cons]; exact Or.inr hi⟩
  | pack _ _ ih =>
    intro fk i xB hxB hidx
    rcases ih hxB hidx with hsub | ⟨rfl, hi⟩
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar _) _ hsub with hB | hfvar
      · exact Or.inl hB
      · simp [Ty.indexes] at hfvar
    · exact Or.inr ⟨rfl, hi⟩

/-- **Lemma 4** (Rigid variables of patterns, Section 6.2, pp. 45–46): in `Ψ; Θ ⊢_SCT p : A ⇒ Γ;
Ψ'; Θ'`, every variable in `Ψ'` has a rigid name, and every fixpoint occurrence `SizeOcc fk i Δ Δb
q B` in a pattern-bound variable `(x, B) ∈ Γ` either already indexes `fk` in `A` (`A.indexes fk i
= true`) or is one of the newly bound pattern variables `i ∈ Ψ'.dom` with `fk = .mu` (in
particular, fresh pattern variables `j ∈ Ψ'.dom` with `A.indexes .nu j = false` never occur as
`ν`-indices in `Γ`). -/
theorem lemma_4 {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
    {Θ' : TyCtx} (h : InferPat Ψ Θ p A Γ Ψ' Θ') :
    (∀ q ∈ Ψ', RigidName q.1) ∧
    (∀ {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol} {xB : Nat × Ty},
      xB ∈ Γ → SizeOcc fk i Δ Δb π xB.2 → A.indexes fk i = true ∨ (fk = .mu ∧ i ∈ Ψ'.dom)) ∧
    (∀ j ∈ Ψ'.dom, A.indexes .nu j = false →
      ∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .nu j Δ Δb π xB.2) := by
  refine ⟨inferPat_rigid h, fun hxB hocc => inferPat_indexes h hxB hocc.indexes, ?_⟩
  intro j _ hAnu xB hxB Δ Δb π hocc
  rcases inferPat_indexes h hxB hocc.indexes with hnu | ⟨hfk, _⟩
  · rw [hAnu] at hnu; cases hnu
  · cases hfk

theorem inferSpine_indexes {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty} (h : InferSpine Ψ Θ qs A Γ Ψ' Θ' C) :
    ∀ {fk : FixKind} {i : Nat},
      ((∃ xB ∈ Γ, xB.2.indexes fk i = true) ∨ C.indexes fk i = true) →
      A.indexes fk i = true ∨ i ∈ Ψ'.dom := by
  induction h with
  | nil =>
    intro fk i hocc
    rcases hocc with ⟨xB, hxB, _⟩ | hC
    · simp at hxB
    · exact Or.inl hC
  | pat hp _ ih =>
    intro fk i hocc
    rcases hocc with ⟨xB, hxB, hidx⟩ | hC
    · rcases List.mem_append.mp hxB with hxB | hxB
      · rcases inferPat_indexes hp hxB hidx with hA | ⟨_, hi⟩
        · exact Or.inl (by simp [Ty.indexes, hA])
        · exact Or.inr (by simp only [SizeCtx.dom_append, List.mem_append]; exact Or.inl hi)
      · rcases ih (Or.inl ⟨xB, hxB, hidx⟩) with hB | hi
        · exact Or.inl (by simp [Ty.indexes, hB])
        · exact Or.inr (by simp only [SizeCtx.dom_append, List.mem_append]; exact Or.inr hi)
    · rcases ih (Or.inr hC) with hB | hi
      · exact Or.inl (by simp [Ty.indexes, hB])
      · exact Or.inr (by simp only [SizeCtx.dom_append, List.mem_append]; exact Or.inr hi)
  | proj hd _ _ _ ih =>
    intro fk i hocc
    rcases ih hocc with hsub | hi
    · rcases Ty.indexes_substTy_sub fk i 0 (.nu (.var _ 0) _) _ hsub with hRd | hnu
      · exact Or.inl (by simp [Ty.indexes, mem_indexesList_of_mem (List.mem_of_getElem? hd) hRd])
      · simp only [Ty.indexes, Size.fvars, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
          List.contains_iff_mem, List.mem_singleton] at hnu
        rcases hnu with ⟨rfl, rfl⟩ | hR
        · exact Or.inr (by simp [SizeCtx.dom])
        · exact Or.inl (by simp [Ty.indexes, hR])
    · exact Or.inr (by simp only [SizeCtx.dom_cons, List.mem_cons]; exact Or.inr hi)
  | inst _ _ ih =>
    intro fk i hocc
    rcases ih hocc with hsub | hi
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar _) _ hsub with hB | hfvar
      · exact Or.inl hB
      · simp [Ty.indexes] at hfvar
    · exact Or.inr hi

/-- **Lemma 5** (Rigid variables of copattern spines, Section 6.2, pp. 46–47): in
`Ψ; Θ ⊢_SCT q⃗ : A ⇒ C; Γ; Ψ'; Θ'`, every variable in `Ψ'` has a rigid name, and every fixpoint
occurrence `SizeOcc fk i Δ Δb π B` in `(x, B) ∈ Γ` or `SizeOcc fk i Δ Δb π C` in `C` satisfies
`A.indexes fk i = true ∨ i ∈ Ψ'.dom`. In particular, when `A` is produced by signature encoding
`+; Δ₀ ⊢_SCT^− A₀ ⇒ Ψ; A` and `NamesDisjoint Ψ.dom Ψ'.dom`, every signature parameter `i ∈ Ψ.dom`
either has `paramPol A i = .pos` and never occurs as a `ν`-index in `Γ` or `C`, or has
`paramPol A i = .neg` and never occurs as a `μ`-index in `Γ` or `C`. -/
theorem lemma_5 {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty} (h : InferSpine Ψ Θ qs A Γ Ψ' Θ' C) :
    (∀ i ∈ Ψ'.dom, RigidName i) ∧
    (∀ {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol},
      ((∃ xB ∈ Γ, SizeOcc fk i Δ Δb π xB.2) ∨ SizeOcc fk i Δ Δb π C) →
      A.indexes fk i = true ∨ i ∈ Ψ'.dom) ∧
    (∀ {ok : Nat → Prop} {Δ₀ : KCtx} {Δb₀ : BCtx} {A₀ : Ty},
      Encode .neg ok .pos Δ₀ Δb₀ A₀ Ψ A →
      NamesDisjoint Ψ.dom Ψ'.dom →
      ∀ i ∈ Ψ.dom,
        (paramPol A i = .pos ∧
          (∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .nu i Δ Δb π xB.2) ∧
          (∀ Δ Δb π, ¬ SizeOcc .nu i Δ Δb π C)) ∨
        (paramPol A i = .neg ∧
          (∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .mu i Δ Δb π xB.2) ∧
          (∀ Δ Δb π, ¬ SizeOcc .mu i Δ Δb π C))) := by
  refine ⟨inferSpine_rigid h, ?_, ?_⟩
  · intro fk i Δ Δb π hocc
    rcases hocc with ⟨xB, hxB, ho⟩ | ho
    · exact inferSpine_indexes h (Or.inl ⟨xB, hxB, ho.indexes⟩)
    · exact inferSpine_indexes h (Or.inr ho.indexes)
  · intro ok Δ₀ Δb₀ A₀ henc hdisj i hi
    have hnotΨ' : i ∉ Ψ'.dom := hdisj i hi
    obtain ⟨fk, q, hq, hcomp, _, hidx, hno_idx, _⟩ := encode_occ_inv henc (Or.inr rfl) i hi
    cases fk with
    | mu =>
      refine Or.inl ⟨by simp [paramPol, hidx], ?_, ?_⟩
      · intro xB hxB Δ Δb π ho
        rcases inferSpine_indexes h (Or.inl ⟨xB, hxB, ho.indexes⟩) with hnu | hi'
        · rw [show A.indexes .nu i = false from hno_idx] at hnu; cases hnu
        · exact hnotΨ' hi'
      · intro Δ Δb π ho
        rcases inferSpine_indexes h (Or.inr ho.indexes) with hnu | hi'
        · rw [show A.indexes .nu i = false from hno_idx] at hnu; cases hnu
        · exact hnotΨ' hi'
    | nu =>
      have hmu_false : A.indexes .mu i = false := hno_idx
      refine Or.inr ⟨by simp [paramPol, hmu_false, hidx], ?_, ?_⟩
      · intro xB hxB Δ Δb π ho
        rcases inferSpine_indexes h (Or.inl ⟨xB, hxB, ho.indexes⟩) with hmu | hi'
        · rw [hmu_false] at hmu; cases hmu
        · exact hnotΨ' hi'
      · intro Δ Δb π ho
        rcases inferSpine_indexes h (Or.inr ho.indexes) with hmu | hi'
        · rw [hmu_false] at hmu; cases hmu
        · exact hnotΨ' hi'

/-! ## Theorem 10: Constraints generated by type comparison (`Compare`) -/

def CompareConstrOrigin (Ψ : SizeCtx) (A B : Ty) (c : SConstr) : Prop :=
  c.ctx = Ψ ∧ c.strict = false ∧ c.up = true ∧
  ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars, A.indexes .mu i = true ∨ B.indexes .mu i = true) ∨
   (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars, A.indexes .nu i = true ∨ B.indexes .nu i = true))

def CompareListConstrOrigin (Ψ : SizeCtx) (S S' : List Ty) (c : SConstr) : Prop :=
  c.ctx = Ψ ∧ c.strict = false ∧ c.up = true ∧
  ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
      Ty.indexesList .mu i S = true ∨ Ty.indexesList .mu i S' = true) ∨
   (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
      Ty.indexesList .nu i S = true ∨ Ty.indexesList .nu i S' = true))

theorem CompareConstrOrigin.symm {Ψ : SizeCtx} {A B : Ty} {c : SConstr}
    (h : CompareConstrOrigin Ψ A B c) : CompareConstrOrigin Ψ B A c := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rcases h.2.2.2 with hmu | hnu
  · exact Or.inl fun i hi => (hmu i hi).symm
  · exact Or.inr fun i hi => (hnu i hi).symm

theorem CompareConstrOrigin.mono {Ψ : SizeCtx} {A B A' B' : Ty} {c : SConstr}
    (h : CompareConstrOrigin Ψ A B c)
    (hAB : ∀ fk i, A.indexes fk i = true ∨ B.indexes fk i = true →
      A'.indexes fk i = true ∨ B'.indexes fk i = true) :
    CompareConstrOrigin Ψ A' B' c := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rcases h.2.2.2 with hmu | hnu
  · exact Or.inl fun i hi => hAB .mu i (hmu i hi)
  · exact Or.inr fun i hi => hAB .nu i (hnu i hi)

theorem CompareListConstrOrigin.symm {Ψ : SizeCtx} {S S' : List Ty} {c : SConstr}
    (h : CompareListConstrOrigin Ψ S S' c) : CompareListConstrOrigin Ψ S' S c := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rcases h.2.2.2 with hmu | hnu
  · exact Or.inl fun i hi => (hmu i hi).symm
  · exact Or.inr fun i hi => (hnu i hi).symm

/-- **Theorem 10** (Constraints in type comparison, Section 6.3.3, pp. 52–53): in
`Ψ; Δ ⊢_SCT A ≤ B : κ ⇒ C`, every emitted constraint `c ∈ C` is a non-strict upper-bound-normalized
constraint `lhs ≤ rhs^↑` in context `Ψ`, and all size variables in `c.lhs` and `c.rhs` come either
from `μ`-indices of `A` and `B` or from `ν`-indices of `A` and `B`. -/
theorem theorem_10 {Ψ : SizeCtx} {Δ : KCtx} {A B : Ty} {κ : Kind} {C : List SConstr}
    (h : Compare Ψ Δ A B κ C) : ∀ c ∈ C, CompareConstrOrigin Ψ A B c := by
  refine Compare.rec
    (motive_1 := fun _ A B _ C _ => ∀ c ∈ C, CompareConstrOrigin Ψ A B c)
    (motive_2 := fun _ _ S S' C _ => ∀ c ∈ C, CompareListConstrOrigin Ψ S S' c)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro _ _ _ _ _ hp; simp at hp
  · intro Δ F G B ι κ C _ _ ih c hc
    refine (ih c hc).mono fun fk i hi => ?_
    rcases hi with hFG | hB
    · rcases Ty.indexes_substTy_sub fk i 0 G F hFG with hF | hG
      · exact Or.inl (by simp [Ty.indexes, hF])
      · exact Or.inl (by simp [Ty.indexes, hG])
    · exact Or.inr hB
  · intro Δ F G A ι κ C _ _ ih c hc
    refine (ih c hc).mono fun fk i hi => ?_
    rcases hi with hA | hFG
    · exact Or.inl hA
    · rcases Ty.indexes_substTy_sub fk i 0 G F hFG with hF | hG
      · exact Or.inr (by simp [Ty.indexes, hF])
      · exact Or.inr (by simp [Ty.indexes, hG])
  · intro Δ A A' B B' C₁ C₂ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · refine (ih₁ c hc).mono fun fk i hi => ?_
      rcases hi with hA | hA'
      · exact Or.inl (by simp [Ty.indexes, hA])
      · exact Or.inr (by simp [Ty.indexes, hA'])
    · refine (ih₂ c hc).mono fun fk i hi => ?_
      rcases hi with hB | hB'
      · exact Or.inl (by simp [Ty.indexes, hB])
      · exact Or.inr (by simp [Ty.indexes, hB'])
  · intro Δ A A' B B' C₁ C₂ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · refine (ih₁ c hc).symm.mono fun fk i hi => ?_
      rcases hi with hA | hA'
      · exact Or.inl (by simp [Ty.indexes, hA])
      · exact Or.inr (by simp [Ty.indexes, hA'])
    · refine (ih₂ c hc).mono fun fk i hi => ?_
      rcases hi with hB | hB'
      · exact Or.inl (by simp [Ty.indexes, hB])
      · exact Or.inr (by simp [Ty.indexes, hB'])
  · intro Δ F F' G G' ι κ₁ κ₂ C₁ C₂ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · refine (ih₁ c hc).mono fun fk i hi => ?_
      rcases hi with hF | hF'
      · exact Or.inl (by simp [Ty.indexes, hF])
      · exact Or.inr (by simp [Ty.indexes, hF'])
    · refine (ih₂ c hc).mono fun fk i hi => ?_
      rcases hi with hG | hG'
      · exact Or.inl (by simp [Ty.indexes, hG])
      · exact Or.inr (by simp [Ty.indexes, hG'])
  · intro Δ F F' G G' ι κ₁ κ₂ C₁ C₂ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · refine (ih₁ c hc).mono fun fk i hi => ?_
      rcases hi with hF | hF'
      · exact Or.inl (by simp [Ty.indexes, hF])
      · exact Or.inr (by simp [Ty.indexes, hF'])
    · refine (ih₂ c hc).symm.mono fun fk i hi => ?_
      rcases hi with hG | hG'
      · exact Or.inl (by simp [Ty.indexes, hG])
      · exact Or.inr (by simp [Ty.indexes, hG'])
  · intro Δ F F' G G' ι κ₁ κ₂ C₁ C₂ C₃ _ _ _ _ _ _ ih₁ ih₂ ih₃ c hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · refine (ih₁ c hc).mono fun fk i hi => ?_
        rcases hi with hF | hF'
        · exact Or.inl (by simp [Ty.indexes, hF])
        · exact Or.inr (by simp [Ty.indexes, hF'])
      · refine (ih₂ c hc).mono fun fk i hi => ?_
        rcases hi with hG | hG'
        · exact Or.inl (by simp [Ty.indexes, hG])
        · exact Or.inr (by simp [Ty.indexes, hG'])
    · refine (ih₃ c hc).symm.mono fun fk i hi => ?_
      rcases hi with hG | hG'
      · exact Or.inl (by simp [Ty.indexes, hG])
      · exact Or.inr (by simp [Ty.indexes, hG'])
  · intro Δ F F' G G' ι κ₁ κ₂ C₁ _ _ _ _ ih₁ c hc
    refine (ih₁ c hc).mono fun fk i hi => ?_
    rcases hi with hF | hF'
    · exact Or.inl (by simp [Ty.indexes, hF])
    · exact Or.inr (by simp [Ty.indexes, hF'])
  · intro Δ F F' ι ι' π κ₁ κ₂ X C _ _ _ _ ih c hc
    refine (ih c hc).mono fun fk i hi => ?_
    rcases hi with hF | hF'
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar X) F hF with hF | hf
      · exact Or.inl hF
      · simp [Ty.indexes] at hf
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar X) F' hF' with hF' | hf
      · exact Or.inr hF'
      · simp [Ty.indexes] at hf
  · intro Δ κ B B' X C _ _ _ _ ih c hc
    refine (ih c hc).mono fun fk i hi => ?_
    rcases hi with hB | hB'
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar X) B hB with hB | hf
      · exact Or.inl hB
      · simp [Ty.indexes] at hf
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar X) B' hB' with hB' | hf
      · exact Or.inr hB'
      · simp [Ty.indexes] at hf
  · intro Δ κ B B' X C _ _ _ _ ih c hc
    refine (ih c hc).mono fun fk i hi => ?_
    rcases hi with hB | hB'
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar X) B hB with hB | hf
      · exact Or.inl hB
      · simp [Ty.indexes] at hf
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar X) B' hB' with hB' | hf
      · exact Or.inr hB'
      · simp [Ty.indexes] at hf
  · intro Δ a b S S' X C _ _ _ _ _ ih c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨rfl, rfl, rfl, Or.inl fun i hi => ?_⟩
      rcases List.mem_append.mp hi with ha | hb
      · exact Or.inl (by simp [Ty.indexes, ha])
      · exact Or.inr (by simp [Ty.indexes, hb])
    · obtain ⟨hctx, hstr, hup, hvars⟩ := ih c hc
      refine ⟨hctx, hstr, hup, ?_⟩
      rcases hvars with hmu | hnu
      · exact Or.inl fun i hi => (hmu i hi).imp
          (fun hS => by simp [Ty.indexes, hS]) (fun hS' => by simp [Ty.indexes, hS'])
      · exact Or.inr fun i hi => (hnu i hi).imp
          (fun hS => by simp [Ty.indexes, hS]) (fun hS' => by simp [Ty.indexes, hS'])
  · intro Δ a b S S' X C₁ C₂ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨rfl, rfl, rfl, Or.inl fun i hi => ?_⟩
      rcases List.mem_append.mp hi with ha | hb
      · exact Or.inl (by simp [Ty.indexes, ha])
      · exact Or.inr (by simp [Ty.indexes, hb])
    · have hcl : CompareListConstrOrigin Ψ S S' c := by
        rcases List.mem_append.mp hc with hc | hc
        · exact ih₁ c hc
        · exact (ih₂ c hc).symm
      obtain ⟨hctx, hstr, hup, hvars⟩ := hcl
      refine ⟨hctx, hstr, hup, ?_⟩
      rcases hvars with hmu | hnu
      · exact Or.inl fun i hi => (hmu i hi).imp
          (fun hS => by simp [Ty.indexes, hS]) (fun hS' => by simp [Ty.indexes, hS'])
      · exact Or.inr fun i hi => (hnu i hi).imp
          (fun hS => by simp [Ty.indexes, hS]) (fun hS' => by simp [Ty.indexes, hS'])
  · intro Δ a b R R' X C _ _ _ _ _ ih c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨rfl, rfl, rfl, Or.inr fun i hi => ?_⟩
      rcases List.mem_append.mp hi with hb | ha
      · exact Or.inr (by simp [Ty.indexes, hb])
      · exact Or.inl (by simp [Ty.indexes, ha])
    · obtain ⟨hctx, hstr, hup, hvars⟩ := ih c hc
      refine ⟨hctx, hstr, hup, ?_⟩
      rcases hvars with hmu | hnu
      · exact Or.inl fun i hi => (hmu i hi).imp
          (fun hR => by simp [Ty.indexes, hR]) (fun hR' => by simp [Ty.indexes, hR'])
      · exact Or.inr fun i hi => (hnu i hi).imp
          (fun hR => by simp [Ty.indexes, hR]) (fun hR' => by simp [Ty.indexes, hR'])
  · intro Δ a b R R' X C₁ C₂ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨rfl, rfl, rfl, Or.inr fun i hi => ?_⟩
      rcases List.mem_append.mp hi with hb | ha
      · exact Or.inr (by simp [Ty.indexes, hb])
      · exact Or.inl (by simp [Ty.indexes, ha])
    · have hcl : CompareListConstrOrigin Ψ R R' c := by
        rcases List.mem_append.mp hc with hc | hc
        · exact ih₁ c hc
        · exact (ih₂ c hc).symm
      obtain ⟨hctx, hstr, hup, hvars⟩ := hcl
      refine ⟨hctx, hstr, hup, ?_⟩
      rcases hvars with hmu | hnu
      · exact Or.inl fun i hi => (hmu i hi).imp
          (fun hR => by simp [Ty.indexes, hR]) (fun hR' => by simp [Ty.indexes, hR'])
      · exact Or.inr fun i hi => (hnu i hi).imp
          (fun hR => by simp [Ty.indexes, hR]) (fun hR' => by simp [Ty.indexes, hR'])
  · intro _ _ _ h; simp at h
  · intro Δ X T T' S S' C₁ C₂ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨hctx, hstr, hup, hvars⟩ := ih₁ c hc
      refine ⟨hctx, hstr, hup, ?_⟩
      rcases hvars with hmu | hnu
      · refine Or.inl fun i hi => ?_
        rcases hmu i hi with hT | hT'
        · rcases Ty.indexes_substTy_sub .mu i 0 (.fvar X) T hT with hT | hf
          · exact Or.inl (by simp [Ty.indexesList, hT])
          · simp [Ty.indexes] at hf
        · rcases Ty.indexes_substTy_sub .mu i 0 (.fvar X) T' hT' with hT' | hf
          · exact Or.inr (by simp [Ty.indexesList, hT'])
          · simp [Ty.indexes] at hf
      · refine Or.inr fun i hi => ?_
        rcases hnu i hi with hT | hT'
        · rcases Ty.indexes_substTy_sub .nu i 0 (.fvar X) T hT with hT | hf
          · exact Or.inl (by simp [Ty.indexesList, hT])
          · simp [Ty.indexes] at hf
        · rcases Ty.indexes_substTy_sub .nu i 0 (.fvar X) T' hT' with hT' | hf
          · exact Or.inr (by simp [Ty.indexesList, hT'])
          · simp [Ty.indexes] at hf
    · obtain ⟨hctx, hstr, hup, hvars⟩ := ih₂ c hc
      refine ⟨hctx, hstr, hup, ?_⟩
      rcases hvars with hmu | hnu
      · exact Or.inl fun i hi => (hmu i hi).imp
          (fun hS => by simp [Ty.indexesList, hS]) (fun hS' => by simp [Ty.indexesList, hS'])
      · exact Or.inr fun i hi => (hnu i hi).imp
          (fun hS => by simp [Ty.indexesList, hS]) (fun hS' => by simp [Ty.indexesList, hS'])

/-! ## Theorems 11 & 12: Constraints generated by call-site inference and clause checking -/

/-- Classification of every constraint generated during call-site inference and checking:
1. A strict step constraint `j < a^↑` from a constructor (`cons`) or projection (`proj`), with
   `FlexName j` and `(j, π, c.ctx) ∈ Φ`;
2. A call-bound constraint `k < b[a⃗/Ψ_g]` from `callBounds`, with `FlexName k`; or
3. A comparison constraint `lhs ≤ rhs^↑` from `Compare Ψ' Δ' A₁ B₁ .star C₂` satisfying
   `CompareConstrOrigin Ψ' A₁ B₁ c`. -/
def InfConstrOrigin (Φ : List FlexVar) (c : SConstr) : Prop :=
  (∃ j π, FlexName j ∧ ⟨j, π, c.ctx⟩ ∈ Φ ∧ (π = .pos ∨ π = .neg) ∧
    c.lhs = .var j 0 ∧ c.strict = true ∧ c.up = true) ∨
  (∃ k, FlexName k ∧ c.lhs = .var k 0 ∧ c.strict = true ∧ c.up = false) ∨
  (∃ A₁ B₁, CompareConstrOrigin c.ctx A₁ B₁ c)

theorem InfConstrOrigin.mono_flex {Φ Φ' : List FlexVar} {c : SConstr}
    (hsub : ∀ v ∈ Φ, v ∈ Φ') (h : InfConstrOrigin Φ c) : InfConstrOrigin Φ' c := by
  rcases h with ⟨j, π, hj, hv, hπ, hlhs, hstr, hup⟩ | hcall | hcmp
  · exact Or.inl ⟨j, π, hj, hsub _ hv, hπ, hlhs, hstr, hup⟩
  · exact Or.inr (Or.inl hcall)
  · exact Or.inr (Or.inr hcmp)

theorem callBounds_origin {Ψ : SizeCtx} {g : FunDecl} {as : List Nat}
    (hflex : ∀ k ∈ as, FlexName k) {Φ : List FlexVar} {c : SConstr}
    (hc : c ∈ callBounds Ψ g (as.map fun k => .var k 0)) : InfConstrOrigin Φ c := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  have hm := (List.of_mem_zip hp).2
  obtain ⟨k, hk, heq⟩ := List.mem_map.mp hm
  exact Or.inr (Or.inl ⟨k, hflex k hk, heq.symm, rfl, rfl⟩)

/-- **Theorems 11 & 12** (Structure of constraints in call-site inference, checking, and clauses,
Sections 6.3.4–6.3.5, pp. 53–56): every constraint `c ∈ C` emitted by `InferTm`, `CheckTm`, or
`CheckClause` satisfies `InfConstrOrigin Φ c`: strict constraints always have a fresh flexible
variable `.var j 0` (`FlexName j`) on the left-hand side (never a rigid variable), and non-strict
constraints come from `Compare` (`CompareConstrOrigin`). -/
theorem theorems_11_and_12 {Ω : InfEnv} :
    (∀ {Ψ Θ Γ r A Φ C T K},
      InferTm Ω Ψ Θ Γ r A Φ C T K → ∀ c ∈ C, InfConstrOrigin Φ c) ∧
    (∀ {Ψ Θ Γ A t Φ C T K},
      CheckTm Ω Ψ Θ Γ A t Φ C T K → ∀ c ∈ C, InfConstrOrigin Φ c) ∧
    (∀ {Ψ Θ Γ A cl Φ C T K},
      CheckClause Ω Ψ Θ Γ A cl Φ C T K → ∀ c ∈ C, InfConstrOrigin Φ c) := by
  let P₁ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (r : Tm) (A : Ty) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : InferTm Ω Ψ Θ Γ r A Φ C T K) => ∀ c ∈ C, InfConstrOrigin Φ c
  let P₂ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (t : Tm) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckTm Ω Ψ Θ Γ A t Φ C T K) => ∀ c ∈ C, InfConstrOrigin Φ c
  let P₃ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (D : List Clause)
      (Φ : List FlexVar) (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckClauses Ω Ψ Θ Γ A D Φ C T K) => ∀ c ∈ C, InfConstrOrigin Φ c
  let P₄ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (cl : Clause)
      (Φ : List FlexVar) (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckClause Ω Ψ Θ Γ A cl Φ C T K) => ∀ c ∈ C, InfConstrOrigin Φ c
  have sVar : ∀ {Ψ Θ Γ x A} (hx : Γ.lookup x = some A), P₁ Ψ Θ Γ (.var x) A [] [] [] []
      (.var hx) := by intro _ _ _ _ _ _ _ h; simp at h
  have sApp : ∀ {Ψ Θ Γ r s A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (hr : InferTm Ω Ψ Θ Γ r (.arr A B) Φ₁ C₁ T₁ K₁) (hs : CheckTm Ω Ψ Θ Γ A s Φ₂ C₂ T₂ K₂),
      P₁ Ψ Θ Γ r (.arr A B) Φ₁ C₁ T₁ K₁ hr → P₂ Ψ Θ Γ A s Φ₂ C₂ T₂ K₂ hs →
      P₁ Ψ Θ Γ (.app r (.term s)) B (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂) (.app hr hs) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (ih₁ c hc).mono_flex (fun v hv => List.mem_append_left _ hv)
    · exact (ih₂ c hc).mono_flex (fun v hv => List.mem_append_right _ hv)
  have sProj : ∀ {Ψ Θ Γ r a R d j Rd Φ C T K} (hr : InferTm Ω Ψ Θ Γ r (.nu a R) Φ C T K)
      (hd : R[d]? = some Rd) (hj : FlexName j),
      P₁ Ψ Θ Γ r (.nu a R) Φ C T K hr →
      P₁ Ψ Θ Γ (.app r (.proj d)) (Rd.substTy 0 (.nu (.var j 0) R))
        (⟨j, .neg, Ψ⟩ :: Φ) (⟨Ψ, .var j 0, a, true, true⟩ :: C)
        ((if Rd.hasBVar 0 then [] else [j]) ++ T) K (.proj hr hd hj) := by
    intro _ _ _ _ _ _ _ j _ _ _ _ _ _ _ hj ih c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl ⟨j, .neg, hj, by simp, Or.inr rfl, rfl, rfl, rfl⟩
    · exact (ih c hc).mono_flex (fun v hv => List.mem_cons_of_mem _ hv)
  have sInst : ∀ {Ψ Θ Γ r κ B G G' ΨG Φ C T K} (hr : InferTm Ω Ψ Θ Γ r (.allT κ B) Φ C T K)
      (hG : Unsized G) (hkG : EKinding Θ.toK [] G κ)
      (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G'),
      P₁ Ψ Θ Γ r (.allT κ B) Φ C T K hr →
      P₁ Ψ Θ Γ (.app r .inst) (B.substTy 0 G') (encFlex Ψ ΨG ++ Φ) C T K
        (.inst hr hG hkG henc) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih c hc
    exact (ih c hc).mono_flex (fun v hv => List.mem_append_right _ hv)
  have sGlobal : ∀ {Ψ Θ Γ g as} (hg : g ∈ Ω.sig) (hlen : as.length = g.sizeParams.length)
      (hflex : ∀ k ∈ as, FlexName k),
      P₁ Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) [] []
        (.global hg hlen hflex) := by
    intro _ _ _ _ _ _ _ hflex c hc
    exact callBounds_origin hflex hc
  have sLocal : ∀ {Ψ Θ Γ g as} (hg : g ∈ Ω.block) (hlen : as.length = g.sizeParams.length)
      (hflex : ∀ k ∈ as, FlexName k),
      P₁ Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) []
        [⟨Ψ, g.name, as.map fun k => .var k 0⟩] (.local hg hlen hflex) := by
    intro _ _ _ _ _ _ _ hflex c hc
    exact callBounds_origin hflex hc
  have sUnit : ∀ {Ψ Θ Γ}, P₂ Ψ Θ Γ .unit .unit [] [] [] [] .unit := by
    intro _ _ _ _ h; simp at h
  have sPair : ∀ {Ψ Θ Γ t u A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (ht : CheckTm Ω Ψ Θ Γ A t Φ₁ C₁ T₁ K₁) (hu : CheckTm Ω Ψ Θ Γ B u Φ₂ C₂ T₂ K₂),
      P₂ Ψ Θ Γ A t Φ₁ C₁ T₁ K₁ ht → P₂ Ψ Θ Γ B u Φ₂ C₂ T₂ K₂ hu →
      P₂ Ψ Θ Γ (.prod A B) (.pair t u) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂)
        (.pair ht hu) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (ih₁ c hc).mono_flex (fun v hv => List.mem_append_left _ hv)
    · exact (ih₂ c hc).mono_flex (fun v hv => List.mem_append_right _ hv)
  have sCons : ∀ {Ψ Θ Γ c j t a S Sc Φ C T K} (hc : S[c]? = some Sc) (hj : FlexName j)
      (ht : CheckTm Ω Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t Φ C T K),
      P₂ Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t Φ C T K ht →
      P₂ Ψ Θ Γ (.mu a S) (.cons c t) (⟨j, .pos, Ψ⟩ :: Φ)
        (⟨Ψ, .var j 0, a, true, true⟩ :: C) ((if Sc.hasBVar 0 then [] else [j]) ++ T) K
        (.cons hc hj ht) := by
    intro _ _ _ _ j _ _ _ _ _ _ _ _ _ hj _ ih c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl ⟨j, .pos, hj, by simp, Or.inl rfl, rfl, rfl, rfl⟩
    · exact (ih c hc).mono_flex (fun v hv => List.mem_cons_of_mem _ hv)
  have sPack : ∀ {Ψ Θ Γ t κ B G G' ΨG Φ C T K} (hG : Unsized G) (hkG : EKinding Θ.toK [] G κ)
      (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G')
      (ht : CheckTm Ω Ψ Θ Γ (B.substTy 0 G') t Φ C T K),
      P₂ Ψ Θ Γ (B.substTy 0 G') t Φ C T K ht →
      P₂ Ψ Θ Γ (.exT κ B) (.pack t) (encFlex Ψ ΨG ++ Φ) C T K (.pack hG hkG henc ht) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih c hc
    exact (ih c hc).mono_flex (fun v hv => List.mem_append_right _ hv)
  have sLam : ∀ {Ψ Θ Γ A D Φ C T K} (hD : CheckClauses Ω Ψ Θ Γ A D Φ C T K),
      P₃ Ψ Θ Γ A D Φ C T K hD → P₂ Ψ Θ Γ A (.lam D) Φ C T K (.lam hD) := by
    intro _ _ _ _ _ _ _ _ _ _ ih; exact ih
  have sSub : ∀ {Ψ Θ Γ r A B Φ C₁ C₂ T K} (hr : InferTm Ω Ψ Θ Γ r A Φ C₁ T K)
      (hcmp : Compare Ψ Θ.toK A B .star C₂),
      P₁ Ψ Θ Γ r A Φ C₁ T K hr → P₂ Ψ Θ Γ B r Φ (C₁ ++ C₂) T K (.sub hr hcmp) := by
    intro Ψ _ _ _ A B _ _ _ _ _ _ hcmp ih c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ih c hc
    · have h10 := theorem_10 hcmp c hc
      exact Or.inr (Or.inr ⟨A, B, h10.1.symm ▸ h10⟩)
  have sNil : ∀ {Ψ Θ Γ A}, P₃ Ψ Θ Γ A [] [] [] [] [] .nil := by
    intro _ _ _ _ _ h; simp at h
  have sConsCl : ∀ {Ψ Θ Γ A cl D Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (hcl : CheckClause Ω Ψ Θ Γ A cl Φ₁ C₁ T₁ K₁)
      (hD : CheckClauses Ω Ψ Θ Γ A D Φ₂ C₂ T₂ K₂),
      P₄ Ψ Θ Γ A cl Φ₁ C₁ T₁ K₁ hcl → P₃ Ψ Θ Γ A D Φ₂ C₂ T₂ K₂ hD →
      P₃ Ψ Θ Γ A (cl :: D) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂) (.cons hcl hD) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (ih₁ c hc).mono_flex (fun v hv => List.mem_append_left _ hv)
    · exact (ih₂ c hc).mono_flex (fun v hv => List.mem_append_right _ hv)
  have sClause : ∀ {Ψ Ψ' Θ Θ' Γ Γ' A C qs t Φ Cs T K}
      (hsp : InferSpine Ψ Θ qs A Γ' Ψ' Θ' C)
      (ht : CheckTm Ω (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) C t Φ Cs T K),
      P₂ (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) C t Φ Cs T K ht →
      P₄ Ψ Θ Γ A (.mk qs t) Φ Cs T K (.mk hsp ht) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih; exact ih
  exact ⟨fun h => @InferTm.rec Ω P₁ P₂ P₃ P₄ @sVar @sApp @sProj @sInst @sGlobal @sLocal @sUnit
      @sPair @sCons @sPack @sLam @sSub @sNil @sConsCl @sClause _ _ _ _ _ _ _ _ _ h,
    fun h => @CheckTm.rec Ω P₁ P₂ P₃ P₄ @sVar @sApp @sProj @sInst @sGlobal @sLocal @sUnit
      @sPair @sCons @sPack @sLam @sSub @sNil @sConsCl @sClause _ _ _ _ _ _ _ _ _ h,
    fun h => @CheckClause.rec Ω P₁ P₂ P₃ P₄ @sVar @sApp @sProj @sInst @sGlobal @sLocal @sUnit
      @sPair @sCons @sPack @sLam @sSub @sNil @sConsCl @sClause _ _ _ _ _ _ _ _ _ h⟩

end NishtAbel2024V5
