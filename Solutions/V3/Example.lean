import Solutions.V3.Main

/-! # V3: the hypotheses of Theorem 15 hold for genuinely recursive programs

A block with two recursive functions, type-checked and size-change checked:

* `copy : ∀(i < ∞). Nat^i → Nat^∞` with `copy (zero x) = zero x` and
  `copy (suc y) = suc (copy y)`. The recursive call is at the size `j < i` bound by the
  constructor pattern.
* `zeros : ∀(i < ∞). Stream^i` with `zeros .head = zero ()` and `zeros .tail = zeros`. The
  self-call is at the size `j < i` bound by the projection copattern.

Both calls are labelled by a strictly decreasing invocation graph, so the block satisfies
`BlockTy`, and Theorem 15 applies. -/

namespace NishtAbel2024V3.Example

open NishtAbel2024V3
open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid InvGraphClosure ConformsToGraph)

/-- Natural numbers: constructor `0` (zero) with a unit payload, constructor `1` (suc). -/
abbrev NatS : List Ty := [.unit, .var 0]
abbrev natT (a : Size) : Ty := .mu a NatS

/-- Streams: projection `0` (head) of type `Nat^∞`, projection `1` (tail). -/
abbrev StreamR : List Ty := [natT .inf, .var 0]
abbrev streamT (a : Size) : Ty := .nu a StreamR

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

abbrev block : List FunDecl := [copyDecl, zerosDecl]

/-- A single strictly decreasing edge from the callee's parameter to the caller's. -/
abbrev G : InvGraph := ⟨1, 1, [(0, 0, .lt)]⟩

abbrev 𝒢 : InvGraphFamily := ⟨fun _ => 1, fun f g => if f = g ∧ f ≤ 1 then [G] else []⟩

/-! ## Size-change termination of the graph family -/

theorem G_normalize : G.normalize = G := by decide
theorem G_comp : G.comp G = G := by decide
theorem G_edge : G.edgeAt 0 0 = some .lt := by decide

theorem mem_graphs {f g : Nat} {H : InvGraph} (h : H ∈ 𝒢.graphs f g) : H = G ∧ f = g ∧ f ≤ 1 := by
  simp only [𝒢] at h
  split at h
  · simp at h; rename_i hc; exact ⟨h, hc⟩
  · simp at h

theorem closure_eq {f g : Nat} {H : InvGraph} (h : InvGraphClosure 𝒢 f g H) : H = G := by
  induction h with
  | base hm => rw [(mem_graphs hm).1]; exact G_normalize
  | comp _ _ ih₁ ih₂ => rw [ih₁, ih₂]; exact G_comp

theorem sct : SCTValid 𝒢 := by
  refine ⟨⟨⟨[0, 1], ?_⟩, ?_⟩, ?_⟩
  · intro f g h
    have : ∃ H, H ∈ 𝒢.graphs f g := List.exists_mem_of_ne_nil _ h
    obtain ⟨H, hH⟩ := this
    obtain ⟨_, rfl, hf⟩ := mem_graphs hH
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hf with rfl | rfl <;> simp
  · intro f g H hH
    obtain ⟨rfl, _, _⟩ := mem_graphs hH
    exact ⟨rfl, rfl, G_normalize.symm⟩
  · intro f H hc _
    rw [closure_eq hc]
    exact ⟨0, by decide, G_edge⟩

/-! ## Well-formedness -/

theorem natT_wf (Ψ : SizeCtx) (k : Nat) {a : Size} (ha : SizeWf Ψ a) : TyWf Ψ k (natT a) := by
  refine .mu ha ?_ ?_
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact .unit _
    · exact .var (by omega)
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact .unit _ _
    · exact .var_self 0

theorem streamT_wf (Ψ : SizeCtx) {a : Size} (ha : SizeWf Ψ a) : TyWf Ψ 0 (streamT a) := by
  refine .nu ha ?_ ?_
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact natT_wf Ψ 1 trivial
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

theorem Ψf_wf : SizeCtxWf Ψf := SizeCtxWf.snoc SizeCtxWf.nil (by simp [SizeCtx.dom]) trivial

/-- The clause context: the parameter `1 < ∞` and the size `2 < 1` bound by a pattern. -/
abbrev Ψc : SizeCtx := Ψf ++ ([(2, .var 1 0)] ++ [])

theorem two_lt_one : SizeLt Ψc (.var 2 0) (.var 1 0) :=
  SizeLt.bound (i := 2) (n := 0) (a := .var 1 0) (by simp)

theorem subst_ok : SizeSubstWf Ψc [.var 2 0] Ψf := by
  refine ⟨rfl, fun k hk ha => ?_⟩
  have hk0 : k = 0 := by simpa using hk
  subst hk0
  exact SizeLt.var_inf (by simp [SizeCtx.dom])

theorem conforms_ok :
    ConformsToGraph (SizeLt Ψc) (SizeLe Ψc) G [.var 2 0] (Ψf.map (fun p => Size.var p.1 0)) := by
  refine ⟨rfl, rfl, fun i j hi hj => ?_⟩
  have hi0 : i = 0 := by simpa using hi
  have hj0 : j = 0 := by simpa using hj
  subst hi0; subst hj0
  refine ⟨fun _ => two_lt_one, fun h => ?_⟩
  rw [G_edge] at h; cases h

/-! ## Typing of `copy` -/

abbrev Ωc : TypingEnv := ⟨[], block, 𝒢, 0, Ψf⟩

theorem copy_clause_zero :
    ClauseTy Ωc Ψf [] (.mk [.pat (.cons 0 (.var 10))] (.cons 0 (.var 10))) copyDecl.ty := by
  have hp : PatTy Ψf (.cons 0 (.var 10)) (natT (.var 1 0)) [(10, .unit)] [(2, .var 1 0)] :=
    PatTy.cons (c := 0) (j := 2) (Sc := .unit) rfl (by simp [SizeCtx.dom])
      (PatTy.var _ 10 _)
  refine ClauseTy.mk (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) hp (SpineTy.nil _ (natT .inf))) ?_
  exact ExprTy.cons (c := 0) (b := .inf) (Sc := .unit) rfl (Or.inr ⟨rfl, rfl⟩)
    (natT_wf _ 0 trivial) (ExprTy.var rfl)

theorem copy_clause_suc :
    ClauseTy Ωc Ψf [] (.mk [.pat (.cons 1 (.var 11))] (.cons 1 (.app (.fn 0) (.term (.var 11)))))
      copyDecl.ty := by
  have hp : PatTy Ψf (.cons 1 (.var 11)) (natT (.var 1 0)) [(11, natT (.var 2 0))]
      [(2, .var 1 0)] :=
    PatTy.cons (c := 1) (j := 2) (Sc := .var 0) rfl (by simp [SizeCtx.dom]) (PatTy.var _ 11 _)
  refine ClauseTy.mk (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) hp (SpineTy.nil _ (natT .inf))) ?_
  have hfun : ExprTy Ωc Ψc ([(11, natT (.var 2 0))] ++ [] ++ []) (.fn 0)
      (.arr (natT (.var 2 0)) (natT .inf)) :=
    ExprTy.localFun (g := copyDecl) (as := [.var 2 0]) (G := G) (by simp) Ψf_wf subst_ok
      (.arr (natT_wf _ 0 (by simp [SizeWf, SizeCtx.dom, Size.subst, Size.shift]))
        (natT_wf _ 0 trivial)) (by decide) conforms_ok
  exact ExprTy.cons (c := 1) (b := .inf) (Sc := .var 0) rfl (Or.inr ⟨rfl, rfl⟩)
    (natT_wf _ 0 trivial) (ExprTy.app hfun (ExprTy.var rfl))

/-! ## Typing of `zeros` -/

abbrev Ωz : TypingEnv := ⟨[], block, 𝒢, 1, Ψf⟩

theorem zeros_clause_head :
    ClauseTy Ωz Ψf [] (.mk [.proj 0] (.cons 0 .unit)) zerosDecl.ty := by
  refine ClauseTy.mk (SpineTy.proj (d := 0) (j := 2) (Rd := natT .inf) rfl
    (by simp [SizeCtx.dom]) (SpineTy.nil _ _)) ?_
  exact ExprTy.cons (c := 0) (b := .inf) (Sc := .unit) rfl (Or.inr ⟨rfl, rfl⟩)
    (natT_wf _ 0 trivial) (ExprTy.unit _ _)

theorem zeros_clause_tail :
    ClauseTy Ωz Ψf [] (.mk [.proj 1] (.fn 1)) zerosDecl.ty := by
  refine ClauseTy.mk (SpineTy.proj (d := 1) (j := 2) (Rd := .var 0) rfl
    (by simp [SizeCtx.dom]) (SpineTy.nil _ _)) ?_
  exact ExprTy.localFun (g := zerosDecl) (as := [.var 2 0]) (G := G) (by simp) Ψf_wf subst_ok
    (streamT_wf _ (by simp [SizeWf, SizeCtx.dom, Size.subst, Size.shift])) (by decide) conforms_ok

/-! ## The block satisfies the hypotheses of Theorem 15 -/

theorem block_typed : BlockTy [] block := by
  refine ⟨𝒢, sct, ?_, ?_⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> rfl
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · refine ⟨Ψf_wf, .arr (natT_wf _ 0 (by simp [SizeWf, SizeCtx.dom])) (natT_wf _ 0 trivial), ?_⟩
      intro cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact copy_clause_zero
      · exact copy_clause_suc
    · refine ⟨Ψf_wf, streamT_wf _ (by simp [SizeWf, SizeCtx.dom]), ?_⟩
      intro cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact zeros_clause_head
      · exact zeros_clause_tail

/-- Theorem 15 applied to the example block: both functions are semantically valid. -/
theorem block_valid (ramsey : RamseyPairs) : SemValid block block := by
  apply theorem_15_proof ramsey block [] block (by simp) (by decide) _ block_typed
  · intro d hd; simp at hd
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> rfl

end NishtAbel2024V3.Example
