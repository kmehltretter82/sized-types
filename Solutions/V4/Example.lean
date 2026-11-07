import Solutions.V4.Main

/-! # V4: the hypotheses of Theorem 15 hold for recursive programs using the new features

A block of four recursive functions, type-checked and size-change checked:

* `copy : ∀(i < ∞). Nat^i → Nat^∞` and `zeros : ∀(i < ∞). Stream^i`, as in V3.
* `len : ∀(i < ∞). ∀X. List^i X → Nat^∞`, polymorphic in the element type. Its clauses take a
  type instantiation copattern `·` and then a list pattern; the element `x : X` has a free type
  variable type, and the recursive call `len · ys` instantiates `len` at that type variable.
* `count : ∀(i < ∞). ∀(j < i). Nat^j → Nat^∞`, with a bounded size quantifier inside its type.
  Its clauses take a size instantiation copattern `·` (binding `j < i`), and the recursive call
  instantiates `count` at size `j` and then at the size `k < j` of the predecessor.

Every recursive call is labelled by a strictly decreasing invocation graph, so the block
satisfies `BlockTy`, and Theorem 15 applies. -/

namespace NishtAbel2024V4.Example

open NishtAbel2024V4
open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid InvGraphClosure ConformsToGraph)

/-- Natural numbers: constructor `0` (zero) with a unit payload, constructor `1` (suc). -/
abbrev NatS : List Ty := [.unit, .var 0]
abbrev natT (a : Size) : Ty := .mu a NatS

/-- Streams: projection `0` (head) of type `Nat^∞`, projection `1` (tail). -/
abbrev StreamR : List Ty := [natT .inf, .var 0]
abbrev streamT (a : Size) : Ty := .nu a StreamR

/-- Lists over the type variable bound just outside the `μ` (inside the `μ`, `var 1` is the
element type and `var 0` the recursion variable): constructor `0` (nil), `1` (cons). -/
abbrev ListS : List Ty := [.unit, .prod (.var 1) (.var 0)]

/-- The same lists over the free type variable `X`. -/
abbrev ListX (X : Nat) : List Ty := [.unit, .prod (.fvar X) (.var 0)]

abbrev Ψf : SizeCtx := [(1, .inf)]

abbrev copyDecl : FunDecl where
  name := 0
  sizeParams := Ψf
  ty := .arr (natT (.var 1 0)) (natT .inf)
  clauses :=
    [.mk [.pat (.cons 0 (.var 10))] (.cons 0 (.var 10)),
     .mk [.pat (.cons 1 (.var 11))] (.cons 1 (.app (.fn 0) (.term (.var 11))))]

abbrev zerosDecl : FunDecl where
  name := 1
  sizeParams := Ψf
  ty := streamT (.var 1 0)
  clauses :=
    [.mk [.proj 0] (.cons 0 .unit),
     .mk [.proj 1] (.fn 1)]

abbrev lenDecl : FunDecl where
  name := 2
  sizeParams := Ψf
  ty := .allT (.arr (.mu (.var 1 0) ListS) (natT .inf))
  clauses :=
    [.mk [.inst, .pat (.cons 0 (.var 10))] (.cons 0 .unit),
     .mk [.inst, .pat (.cons 1 (.pair (.var 11) (.var 12)))]
       (.cons 1 (.app (.app (.fn 2) .inst) (.term (.var 12))))]

abbrev countDecl : FunDecl where
  name := 3
  sizeParams := Ψf
  ty := .allS (.var 1 0) (.arr (natT (.bvar 0 0)) (natT .inf))
  clauses :=
    [.mk [.inst, .pat (.cons 0 (.var 10))] (.cons 0 (.var 10)),
     .mk [.inst, .pat (.cons 1 (.var 11))]
       (.cons 1 (.app (.app (.fn 3) .inst) (.term (.var 11))))]

abbrev block : List FunDecl := [copyDecl, zerosDecl, lenDecl, countDecl]

/-- A single strictly decreasing edge from the callee's parameter to the caller's. -/
abbrev G : InvGraph := ⟨1, 1, [(0, 0, .lt)]⟩

abbrev 𝒢 : InvGraphFamily := ⟨fun _ => 1, fun f g => if f = g ∧ f ≤ 3 then [G] else []⟩

/-! ## Size-change termination of the graph family -/

theorem G_normalize : G.normalize = G := by decide
theorem G_comp : G.comp G = G := by decide
theorem G_edge : G.edgeAt 0 0 = some .lt := by decide

theorem mem_graphs {f g : Nat} {H : InvGraph} (h : H ∈ 𝒢.graphs f g) : H = G ∧ f = g ∧ f ≤ 3 := by
  simp only [𝒢] at h
  split at h
  · simp at h; rename_i hc; exact ⟨h, hc⟩
  · simp at h

theorem closure_eq {f g : Nat} {H : InvGraph} (h : InvGraphClosure 𝒢 f g H) : H = G := by
  induction h with
  | base hm => rw [(mem_graphs hm).1]; exact G_normalize
  | comp _ _ ih₁ ih₂ => rw [ih₁, ih₂]; exact G_comp

theorem sct : SCTValid 𝒢 := by
  refine ⟨⟨⟨[0, 1, 2, 3], ?_⟩, ?_⟩, ?_⟩
  · intro f g h
    have : ∃ H, H ∈ 𝒢.graphs f g := List.exists_mem_of_ne_nil _ h
    obtain ⟨H, hH⟩ := this
    obtain ⟨_, rfl, hf⟩ := mem_graphs hH
    have key : ∀ n : Nat, n ≤ 3 → n ∈ [0, 1, 2, 3] := by decide
    exact ⟨key f hf, key f hf⟩
  · intro f g H hH
    obtain ⟨rfl, _, _⟩ := mem_graphs hH
    exact ⟨rfl, rfl, G_normalize.symm⟩
  · intro f H hc _
    rw [closure_eq hc]
    exact ⟨0, by decide, G_edge⟩

/-! ## Well-formedness -/

theorem natT_wf (Ψ : SizeCtx) (Θ : List Nat) (k m : Nat) {a : Size} (ha : SizeWfAt Ψ m a) :
    TyWf Ψ Θ k m (natT a) := by
  refine .mu ha ?_ ?_
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact .unit _ _
    · exact .var (by omega)
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact .unit _ _
    · exact .var_self 0

theorem streamT_wf (Ψ : SizeCtx) (Θ : List Nat) {a : Size} (ha : SizeWf Ψ a) :
    TyWf Ψ Θ 0 0 (streamT a) := by
  refine .nu ha ?_ ?_
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact natT_wf Ψ Θ 1 0 trivial
    · exact .var (by omega)
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · refine .mu fun T hT => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl
      · exact .unit _ _
      · exact .var_other (by omega)
    · exact .var_self 0

theorem listT_wf (Ψ : SizeCtx) (Θ : List Nat) {a : Size} (ha : SizeWf Ψ a) :
    TyWf Ψ Θ 1 0 (.mu a ListS) := by
  refine .mu ha ?_ ?_
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact .unit _ _
    · exact .prod (.var (by omega)) (.var (by omega))
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact .unit _ _
    · exact .prod (.var_other (by omega)) (.var_self 0)

/-- The type of `len` at the size `a`. -/
theorem lenTy_wf (Ψ : SizeCtx) (Θ : List Nat) {a : Size} (ha : SizeWf Ψ a) :
    TyWf Ψ Θ 0 0 (.allT (.arr (.mu a ListS) (natT .inf))) :=
  .allT (.arr (listT_wf Ψ Θ ha) (natT_wf Ψ Θ 1 0 trivial))

/-- The type of `count` at the size `a`. -/
theorem countTy_wf (Ψ : SizeCtx) (Θ : List Nat) {a : Size} (ha : SizeWf Ψ a) :
    TyWf Ψ Θ 0 0 (.allS a (.arr (natT (.bvar 0 0)) (natT .inf))) :=
  .allS ha (.arr (natT_wf Ψ Θ 0 1 (show 0 < 1 by omega)) (natT_wf Ψ Θ 0 1 trivial))

theorem Ψf_wf : SizeCtxWf Ψf := SizeCtxWf.snoc SizeCtxWf.nil (by simp [SizeCtx.dom]) trivial

theorem one_wf : SizeWf Ψf (.var 1 0) := by simp [SizeWf, SizeWfAt, SizeCtx.dom]

/-- Recursive calls instantiate the parameter `1 < ∞` with the size `2`. -/
theorem subst_ok {Ψ : SizeCtx} (h : 2 ∈ Ψ.dom) : SizeSubstWf Ψ [.var 2 0] Ψf := by
  refine ⟨rfl, fun k hk ha => ?_⟩
  have hk0 : k = 0 := by simpa using hk
  subst hk0
  exact SizeLt.var_inf h

theorem conforms_ok {Ψ : SizeCtx} (h : (2, Size.var 1 0) ∈ Ψ) :
    ConformsToGraph (SizeLt Ψ) (SizeLe Ψ) G [.var 2 0] (Ψf.map (fun p => Size.var p.1 0)) := by
  refine ⟨rfl, rfl, fun i j hi hj => ?_⟩
  have hi0 : i = 0 := by simpa using hi
  have hj0 : j = 0 := by simpa using hj
  subst hi0; subst hj0
  refine ⟨fun _ => SizeLt.bound (i := 2) (n := 0) (a := .var 1 0) h, fun h' => ?_⟩
  rw [G_edge] at h'; cases h'

/-! ## Typing of `copy` -/

abbrev Ωc : TypingEnv := ⟨[], block, 𝒢, 0, Ψf⟩

theorem copy_clause_zero :
    ClauseTy Ωc Ψf [] [] (.mk [.pat (.cons 0 (.var 10))] (.cons 0 (.var 10))) copyDecl.ty := by
  have hp : PatTy Ψf [] (.cons 0 (.var 10)) (natT (.var 1 0)) [(10, .unit)] [(2, .var 1 0)] [] :=
    PatTy.cons (c := 0) (j := 2) (Sc := .unit) rfl (by simp [SizeCtx.dom])
      (PatTy.var _ _ 10 _)
  refine ClauseTy.mk (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp
    (SpineTy.nil _ _ (natT .inf))) ?_
  exact ExprTy.cons (c := 0) (b := .inf) (Sc := .unit) rfl (Or.inr ⟨rfl, rfl⟩)
    (natT_wf _ _ 0 0 trivial) (ExprTy.var rfl)

theorem copy_clause_suc :
    ClauseTy Ωc Ψf [] [] (.mk [.pat (.cons 1 (.var 11))] (.cons 1 (.app (.fn 0) (.term (.var 11)))))
      copyDecl.ty := by
  have hp : PatTy Ψf [] (.cons 1 (.var 11)) (natT (.var 1 0)) [(11, natT (.var 2 0))]
      [(2, .var 1 0)] [] :=
    PatTy.cons (c := 1) (j := 2) (Sc := .var 0) rfl (by simp [SizeCtx.dom]) (PatTy.var _ _ 11 _)
  refine ClauseTy.mk (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp
    (SpineTy.nil _ _ (natT .inf))) ?_
  exact ExprTy.cons (c := 1) (b := .inf) (Sc := .var 0) rfl (Or.inr ⟨rfl, rfl⟩)
    (natT_wf _ _ 0 0 trivial)
    (ExprTy.app
      (ExprTy.localFun (g := copyDecl) (as := [.var 2 0]) (G := G) (by simp) Ψf_wf
        (.arr (natT_wf _ _ 0 0 one_wf) (natT_wf _ _ 0 0 trivial))
        (subst_ok (by simp [SizeCtx.dom]))
        (.arr (natT_wf _ _ 0 0 (by simp [SizeWfAt, SizeCtx.dom, Size.subst, Size.shift]))
          (natT_wf _ _ 0 0 trivial)) (by decide) (conforms_ok (by simp)))
      (ExprTy.var rfl))

/-! ## Typing of `zeros` -/

abbrev Ωz : TypingEnv := ⟨[], block, 𝒢, 1, Ψf⟩

theorem zeros_clause_head :
    ClauseTy Ωz Ψf [] [] (.mk [.proj 0] (.cons 0 .unit)) zerosDecl.ty := by
  refine ClauseTy.mk (SpineTy.proj (d := 0) (j := 2) (Rd := natT .inf) rfl
    (by simp [SizeCtx.dom]) (SpineTy.nil _ _ _)) ?_
  exact ExprTy.cons (c := 0) (b := .inf) (Sc := .unit) rfl (Or.inr ⟨rfl, rfl⟩)
    (natT_wf _ _ 0 0 trivial) (ExprTy.unit _ _ _)

theorem zeros_clause_tail :
    ClauseTy Ωz Ψf [] [] (.mk [.proj 1] (.fn 1)) zerosDecl.ty := by
  refine ClauseTy.mk (SpineTy.proj (d := 1) (j := 2) (Rd := .var 0) rfl
    (by simp [SizeCtx.dom]) (SpineTy.nil _ _ _)) ?_
  exact ExprTy.localFun (g := zerosDecl) (as := [.var 2 0]) (G := G) (by simp) Ψf_wf
    (streamT_wf _ _ one_wf) (subst_ok (by simp [SizeCtx.dom]))
    (streamT_wf _ _ (by simp [SizeWf, SizeWfAt, SizeCtx.dom, Size.subst, Size.shift])) (by decide)
    (conforms_ok (by simp))

/-! ## Typing of `len` -/

abbrev Ωl : TypingEnv := ⟨[], block, 𝒢, 2, Ψf⟩

theorem len_clause_nil :
    ClauseTy Ωl Ψf [] [] (.mk [.inst, .pat (.cons 0 (.var 10))] (.cons 0 .unit)) lenDecl.ty := by
  have hp : PatTy Ψf ([] ++ [0]) (.cons 0 (.var 10)) (.mu (.var 1 0) (ListX 0)) [(10, .unit)]
      [(2, .var 1 0)] [] :=
    PatTy.cons (c := 0) (j := 2) (Sc := .unit) rfl (by simp [SizeCtx.dom]) (PatTy.var _ _ 10 _)
  refine ClauseTy.mk (SpineTy.instT (X := 0) (by simp)
    (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp (SpineTy.nil _ _ (natT .inf)))) ?_
  exact ExprTy.cons (c := 0) (b := .inf) (Sc := .unit) rfl (Or.inr ⟨rfl, rfl⟩)
    (natT_wf _ _ 0 0 trivial) (ExprTy.unit _ _ _)

theorem len_clause_cons :
    ClauseTy Ωl Ψf [] [] (.mk [.inst, .pat (.cons 1 (.pair (.var 11) (.var 12)))]
      (.cons 1 (.app (.app (.fn 2) .inst) (.term (.var 12))))) lenDecl.ty := by
  have hp : PatTy Ψf ([] ++ [0]) (.cons 1 (.pair (.var 11) (.var 12))) (.mu (.var 1 0) (ListX 0))
      ([(11, .fvar 0)] ++ [(12, .mu (.var 2 0) (ListX 0))]) ((2, .var 1 0) :: ([] ++ []))
      ([] ++ []) :=
    PatTy.cons (c := 1) (j := 2) (Sc := .prod (.fvar 0) (.var 0)) rfl (by simp [SizeCtx.dom])
      (PatTy.pair (PatTy.var _ _ 11 _) (PatTy.var _ _ 12 _))
  refine ClauseTy.mk (SpineTy.instT (X := 0) (by simp)
    (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp (SpineTy.nil _ _ (natT .inf)))) ?_
  exact ExprTy.cons (c := 1) (b := .inf) (Sc := .var 0) rfl (Or.inr ⟨rfl, rfl⟩)
    (natT_wf _ _ 0 0 trivial)
    (ExprTy.app
      (ExprTy.instT (T := .fvar 0)
        (ExprTy.localFun (g := lenDecl) (as := [.var 2 0]) (G := G) (by simp) Ψf_wf
          (lenTy_wf _ _ one_wf) (subst_ok (by simp [SizeCtx.dom]))
          (lenTy_wf _ _ (by simp [SizeWf, SizeWfAt, SizeCtx.dom, Size.subst, Size.shift])) (by decide)
          (conforms_ok (by simp)))
        (.fvar (by simp)))
      (ExprTy.var rfl))

/-! ## Typing of `count` -/

abbrev Ωn : TypingEnv := ⟨[], block, 𝒢, 3, Ψf⟩

theorem count_clause_zero :
    ClauseTy Ωn Ψf [] [] (.mk [.inst, .pat (.cons 0 (.var 10))] (.cons 0 (.var 10)))
      countDecl.ty := by
  have hp : PatTy (Ψf ++ [(2, .var 1 0)]) [] (.cons 0 (.var 10)) (natT (.var 2 0))
      [(10, .unit)] [(3, .var 2 0)] [] :=
    PatTy.cons (c := 0) (j := 3) (Sc := .unit) rfl (by simp [SizeCtx.dom]) (PatTy.var _ _ 10 _)
  refine ClauseTy.mk (SpineTy.instS (j := 2) (by simp [SizeCtx.dom])
    (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp (SpineTy.nil _ _ (natT .inf)))) ?_
  exact ExprTy.cons (c := 0) (b := .inf) (Sc := .unit) rfl (Or.inr ⟨rfl, rfl⟩)
    (natT_wf _ _ 0 0 trivial) (ExprTy.var rfl)

theorem count_clause_suc :
    ClauseTy Ωn Ψf [] [] (.mk [.inst, .pat (.cons 1 (.var 11))]
      (.cons 1 (.app (.app (.fn 3) .inst) (.term (.var 11))))) countDecl.ty := by
  have hp : PatTy (Ψf ++ [(2, .var 1 0)]) [] (.cons 1 (.var 11)) (natT (.var 2 0))
      [(11, natT (.var 3 0))] [(3, .var 2 0)] [] :=
    PatTy.cons (c := 1) (j := 3) (Sc := .var 0) rfl (by simp [SizeCtx.dom]) (PatTy.var _ _ 11 _)
  refine ClauseTy.mk (SpineTy.instS (j := 2) (by simp [SizeCtx.dom])
    (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp (SpineTy.nil _ _ (natT .inf)))) ?_
  exact ExprTy.cons (c := 1) (b := .inf) (Sc := .var 0) rfl (Or.inr ⟨rfl, rfl⟩)
    (natT_wf _ _ 0 0 trivial)
    (ExprTy.app
      (ExprTy.instS (b := .var 3 0)
        (ExprTy.localFun (g := countDecl) (as := [.var 2 0]) (G := G) (by simp) Ψf_wf
          (countTy_wf _ _ one_wf) (subst_ok (by simp [SizeCtx.dom]))
          (countTy_wf _ _ (by simp [SizeWf, SizeWfAt, SizeCtx.dom, Size.subst, Size.shift])) (by decide)
          (conforms_ok (by simp)))
        (SizeLt.bound (i := 3) (n := 0) (a := .var 2 0) (by simp)))
      (ExprTy.var rfl))

/-! ## The block satisfies the hypotheses of Theorem 15 -/

theorem block_typed : BlockTy [] block := by
  refine ⟨𝒢, sct, ?_, ?_⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> rfl
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · refine ⟨Ψf_wf, .arr (natT_wf _ _ 0 0 one_wf) (natT_wf _ _ 0 0 trivial), ?_⟩
      intro cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact copy_clause_zero
      · exact copy_clause_suc
    · refine ⟨Ψf_wf, streamT_wf _ _ one_wf, ?_⟩
      intro cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact zeros_clause_head
      · exact zeros_clause_tail
    · refine ⟨Ψf_wf, lenTy_wf _ _ one_wf, ?_⟩
      intro cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact len_clause_nil
      · exact len_clause_cons
    · refine ⟨Ψf_wf, countTy_wf _ _ one_wf, ?_⟩
      intro cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact count_clause_zero
      · exact count_clause_suc

/-- Theorem 15 applied to the example block: all four functions are semantically valid. -/
theorem block_valid (ramsey : RamseyPairs) : SemValid block block := by
  apply theorem_15_proof ramsey block [] block (by simp) (by decide) _ block_typed
  · intro d hd; simp at hd
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> rfl

end NishtAbel2024V4.Example
