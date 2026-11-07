import Solutions.V5.Main

/-! # V5: the hypotheses of Theorem 4 / Theorem 15 hold for recursive programs using V5's features

A block of five recursive functions in System `F_ω^{cop,SCT}`, type-checked and size-change checked:

* `copy : ∀(i < ∞). Nat^i → Nat^∞` and `zeros : ∀(i < ∞). Stream^i`, exercising inductive and
  coinductive types.
* `len : ∀(i < ∞). ∀(X : *). List^i X → Nat^∞`, polymorphic in the element type.
* `count : ∀(i < ∞). ∀(j < i). Nat^j → Nat^∞`, with a bounded size quantifier inside its type.
* `evalT : ∀(i < ∞). Bush^i → (λ(X : *). X) Nat^∞`, exercising a **mixed-variance functor**
  `Bush^a = μ^a (1, (X → 1) × X)` (where the recursion variable `X` occurs both contravariantly and
  covariantly, checked at polarity `π = .mix`) and a **type operator** `IdOp = λ(X : *). X` of kind
  `+* → *` applied to `Nat^∞` and converted via type-level β-subtyping (`SubTy.beta_r`).

Every recursive call is labelled by a strictly decreasing invocation graph, so the block
satisfies `BlockTy`, and `theorem_4_core` yields `SemValid block block`. -/

namespace NishtAbel2024V5.Example

open NishtAbel2024V5
open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid InvGraphClosure ConformsToGraph)

/-- Natural numbers: constructor `0` (zero) with a unit payload, constructor `1` (suc). -/
abbrev NatS : List Ty := [.unit, .var 0]
abbrev natT (a : Size) : Ty := .mu a NatS

/-- Streams: projection `0` (head) of type `Nat^∞`, projection `1` (tail). -/
abbrev StreamR : List Ty := [natT (.inf 0), .var 0]
abbrev streamT (a : Size) : Ty := .nu a StreamR

/-- Lists over the type variable bound just outside the `μ` (inside the `μ`, `var 1` is the
element type and `var 0` the recursion variable): constructor `0` (nil), `1` (cons). -/
abbrev ListS : List Ty := [.unit, .prod (.var 1) (.var 0)]

/-- The same lists over the free type variable `X`. -/
abbrev ListX (X : Nat) : List Ty := [.unit, .prod (.fvar X) (.var 0)]

/-- Mixed-variance functor `(1, (X → 1) × X)` where the recursion variable `var 0` occurs both
negatively and positively. -/
abbrev BushS : List Ty := [.unit, .prod (.arr (.var 0) .unit) (.var 0)]
abbrev bushT (a : Size) : Ty := .mu a BushS

/-- Identity type operator `λ(X : *). X` of kind `+* → *`. -/
abbrev IdOp : Ty := .lam .star (.var 0)

abbrev Ψf : SizeCtx := [(1, .inf 0)]

abbrev copyDecl : FunDecl where
  name := 0
  sizeParams := Ψf
  ty := .arr (natT (.var 1 0)) (natT (.inf 0))
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
  ty := .allT .star (.arr (.mu (.var 1 0) ListS) (natT (.inf 0)))
  clauses :=
    [.mk [.inst, .pat (.cons 0 (.var 10))] (.cons 0 .unit),
     .mk [.inst, .pat (.cons 1 (.pair (.var 11) (.var 12)))]
       (.cons 1 (.app (.app (.fn 2) .inst) (.term (.var 12))))]

abbrev countDecl : FunDecl where
  name := 3
  sizeParams := Ψf
  ty := .allS (.var 1 0) (.arr (natT (.bvar 0 0)) (natT (.inf 0)))
  clauses :=
    [.mk [.inst, .pat (.cons 0 (.var 10))] (.cons 0 (.var 10)),
     .mk [.inst, .pat (.cons 1 (.var 11))]
       (.cons 1 (.app (.app (.fn 3) .inst) (.term (.var 11))))]

abbrev evalTDecl : FunDecl where
  name := 4
  sizeParams := Ψf
  ty := .arr (bushT (.var 1 0)) (.app IdOp (natT (.inf 0)) .star)
  clauses :=
    [.mk [.pat (.cons 0 (.var 10))] (.cons 0 (.var 10)),
     .mk [.pat (.cons 1 (.pair (.var 11) (.var 12)))] (.app (.fn 4) (.term (.var 12)))]

abbrev block : List FunDecl := [copyDecl, zerosDecl, lenDecl, countDecl, evalTDecl]

/-- A single strictly decreasing edge from the callee's parameter to the caller's. -/
abbrev G : InvGraph := ⟨1, 1, [(0, 0, .lt)]⟩

abbrev 𝒢 : InvGraphFamily := ⟨fun _ => 1, fun f g => if f = g ∧ f ≤ 4 then [G] else []⟩

/-! ## Size-change termination of the graph family -/

theorem G_normalize : G.normalize = G := by decide
theorem G_comp : G.comp G = G := by decide
theorem G_edge : G.edgeAt 0 0 = some .lt := by decide

theorem mem_graphs {f g : Nat} {H : InvGraph} (h : H ∈ 𝒢.graphs f g) : H = G ∧ f = g ∧ f ≤ 4 := by
  simp only at h
  split at h
  · simp at h; rename_i hc; exact ⟨h, hc⟩
  · simp at h

theorem closure_eq {f g : Nat} {H : InvGraph} (h : InvGraphClosure 𝒢 f g H) : H = G := by
  induction h with
  | base hm => rw [(mem_graphs hm).1]; exact G_normalize
  | comp _ _ ih₁ ih₂ => rw [ih₁, ih₂]; exact G_comp

theorem sct : SCTValid 𝒢 := by
  refine ⟨⟨⟨[0, 1, 2, 3, 4], ?_⟩, ?_⟩, ?_⟩
  · intro f g h
    have : ∃ H, H ∈ 𝒢.graphs f g := List.exists_mem_of_ne_nil _ h
    obtain ⟨H, hH⟩ := this
    obtain ⟨_, rfl, hf⟩ := mem_graphs hH
    have key : ∀ n : Nat, n ≤ 4 → n ∈ [0, 1, 2, 3, 4] := by decide
    exact ⟨key f hf, key f hf⟩
  · intro f g H hH
    obtain ⟨rfl, _, _⟩ := mem_graphs hH
    exact ⟨rfl, rfl, G_normalize.symm⟩
  · intro f H hc _
    rw [closure_eq hc]
    exact ⟨0, by decide, G_edge⟩

/-! ## Kinding and size helpers -/

theorem natT_kinding (Ψ : SizeCtx) (Δ : KCtx) (Δb : BCtx) (m : Nat) {a : Size}
    (ha : SizeWfAt Ψ m a) : Kinding Ψ Δ Δb m (natT a) .star := by
  refine .mu (Or.inl rfl) ha fun T hT => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl
  · exact .unit
  · exact .var rfl trivial

theorem streamT_kinding (Ψ : SizeCtx) (Δ : KCtx) {a : Size} (ha : SizeWf Ψ a) :
    KindingC Ψ Δ (streamT a) .star := by
  refine .nu (Or.inl rfl) ha fun T hT => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl
  · exact natT_kinding Ψ (Δ.inv .pos) [(.pos, .star)] 0 trivial
  · exact .var rfl trivial

theorem listT_kinding (Ψ : SizeCtx) (Δ : KCtx) {a : Size} (ha : SizeWf Ψ a) :
    Kinding Ψ Δ [(.mix, .star)] 0 (.mu a ListS) .star := by
  refine .mu (Or.inl rfl) ha fun T hT => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl
  · exact .unit
  · exact .prod (.var rfl trivial) (.var rfl trivial)

theorem lenTy_kinding (Ψ : SizeCtx) (Δ : KCtx) {a : Size} (ha : SizeWf Ψ a) :
    KindingC Ψ Δ (.allT .star (.arr (.mu a ListS) (natT (.inf 0)))) .star :=
  .allT (.arr (listT_kinding Ψ (Δ.inv .neg) ha) (natT_kinding Ψ Δ [(.mix, .star)] 0 trivial))

theorem countTy_kinding (Ψ : SizeCtx) (Δ : KCtx) {a : Size} (ha : SizeWf Ψ a) :
    KindingC Ψ Δ (.allS a (.arr (natT (.bvar 0 0)) (natT (.inf 0)))) .star :=
  .allS ha (.arr (natT_kinding Ψ (Δ.inv .neg) [] 1 (show 0 < 1 by omega))
    (natT_kinding Ψ Δ [] 1 trivial))

theorem bushT_kinding (Ψ : SizeCtx) (Δ : KCtx) {a : Size} (ha : SizeWf Ψ a) :
    KindingC Ψ Δ (bushT a) .star := by
  refine .mu (Or.inr rfl) ha fun T hT => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl
  · exact .unit
  · exact .prod (.arr (.var rfl trivial) .unit) (.var rfl trivial)

theorem idNat_kinding (Ψ : SizeCtx) (Δ : KCtx) :
    KindingC Ψ Δ (.app IdOp (natT (.inf 0)) .star) .star :=
  .app (.lam (π := .pos) rfl (.var rfl trivial)) (natT_kinding Ψ (Δ.inv .pos) [] 0 trivial) rfl

theorem evalTTy_kinding (Ψ : SizeCtx) (Δ : KCtx) {a : Size} (ha : SizeWf Ψ a) :
    KindingC Ψ Δ (.arr (bushT a) (.app IdOp (natT (.inf 0)) .star)) .star :=
  .arr (bushT_kinding Ψ (Δ.inv .neg) ha) (idNat_kinding Ψ Δ)

theorem Ψf_wf : SizeCtxWf Ψf := SizeCtxWf.snoc SizeCtxWf.nil (by simp [SizeCtx.dom]) trivial

theorem one_wf : SizeWf Ψf (.var 1 0) := by simp [SizeWf, SizeWfAt, SizeCtx.dom]

theorem lt_two_one {Ψ : SizeCtx} (h1 : 1 ∈ Ψ.dom) (h2 : (2, Size.var 1 0) ∈ Ψ) :
    SizeLt Ψ (.var 2 0) (.var 1 0) :=
  SizeLt.bound h2 (SizeLt.var_var h1 (by omega))

theorem lt_two_inf {Ψ : SizeCtx} (h1 : (1, Size.inf 0) ∈ Ψ) (h2 : (2, Size.var 1 0) ∈ Ψ) :
    SizeLt Ψ (.var 2 0) (.inf 0) :=
  SizeLt.trans (lt_two_one (List.mem_map_of_mem h1) h2)
    (SizeLt.var_inf h1 (SizeLt.inf_inf (by omega)))

theorem subst_ok {Ψ : SizeCtx} (h1 : (1, Size.inf 0) ∈ Ψ) (h2 : (2, Size.var 1 0) ∈ Ψ) :
    SizeSubstWf Ψ [.var 2 0] Ψf := by
  refine ⟨rfl, fun k hk ha => ?_⟩
  have hk0 : k = 0 := by simpa using hk
  subst hk0
  exact lt_two_inf h1 h2

theorem conforms_ok {Ψ : SizeCtx} (h1 : 1 ∈ Ψ.dom) (h2 : (2, Size.var 1 0) ∈ Ψ) :
    ConformsToGraph (SizeLt Ψ) (SizeLe Ψ) G [.var 2 0] (Ψf.map (fun p => Size.var p.1 0)) := by
  refine ⟨rfl, rfl, fun i j hi hj => ?_⟩
  have hi0 : i = 0 := by simpa using hi
  have hj0 : j = 0 := by simpa using hj
  subst hi0; subst hj0
  refine ⟨fun _ => lt_two_one h1 h2, fun h' => ?_⟩
  rw [G_edge] at h'; cases h'

/-! ## Typing of `copy` -/

abbrev Ωc : TypingEnv := ⟨[], block, sctCallOK 𝒢 0 Ψf⟩

theorem copy_clause_zero :
    ClauseTy Ωc Ψf [] [] (.mk [.pat (.cons 0 (.var 10))] (.cons 0 (.var 10))) copyDecl.ty := by
  have hp : PatTy Ψf [] (.cons 0 (.var 10)) (natT (.var 1 0)) [(10, .unit)] [(2, .var 1 0)] [] :=
    PatTy.cons (c := 0) (j := 2) (Sc := .unit) rfl (by simp [SizeCtx.dom]) (PatTy.var _ _ 10 _)
  refine ClauseTy.mk (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp
    (SpineTy.nil _ _ (natT (.inf 0)))) ?_
  exact ExprTy.cons (c := 0) (b := .inf 0) (Sc := .unit) rfl (SizeLt.inf_inf (by decide))
    (natT_kinding _ _ [] 0 trivial) (ExprTy.var rfl)

theorem copy_clause_suc :
    ClauseTy Ωc Ψf [] [] (.mk [.pat (.cons 1 (.var 11))] (.cons 1 (.app (.fn 0) (.term (.var 11)))))
      copyDecl.ty := by
  have hp : PatTy Ψf [] (.cons 1 (.var 11)) (natT (.var 1 0)) [(11, natT (.var 2 0))]
      [(2, .var 1 0)] [] :=
    PatTy.cons (c := 1) (j := 2) (Sc := .var 0) rfl (by simp [SizeCtx.dom]) (PatTy.var _ _ 11 _)
  refine ClauseTy.mk (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp
    (SpineTy.nil _ _ (natT (.inf 0)))) ?_
  exact ExprTy.cons (c := 1) (b := .inf 0) (Sc := .var 0) rfl (SizeLt.inf_inf (by decide))
    (natT_kinding _ _ [] 0 trivial)
    (ExprTy.app
      (ExprTy.localFun (g := copyDecl) (as := [.var 2 0]) (by simp) Ψf_wf
        (.arr (natT_kinding _ _ [] 0 one_wf) (natT_kinding _ _ [] 0 trivial))
        (subst_ok (by simp) (by simp))
        (.arr (natT_kinding _ _ [] 0 (by simp [SizeWfAt, SizeCtx.dom, Size.subst, Size.shift]))
          (natT_kinding _ _ [] 0 trivial))
        ⟨G, by decide, conforms_ok (by simp [SizeCtx.dom]) (by simp)⟩)
      (ExprTy.var rfl))

/-! ## Typing of `zeros` -/

abbrev Ωz : TypingEnv := ⟨[], block, sctCallOK 𝒢 1 Ψf⟩

theorem zeros_clause_head :
    ClauseTy Ωz Ψf [] [] (.mk [.proj 0] (.cons 0 .unit)) zerosDecl.ty := by
  refine ClauseTy.mk (SpineTy.proj (d := 0) (j := 2) (Rd := natT (.inf 0)) rfl
    (by simp [SizeCtx.dom]) (SpineTy.nil _ _ _)) ?_
  exact ExprTy.cons (c := 0) (b := .inf 0) (Sc := .unit) rfl (SizeLt.inf_inf (by decide))
    (natT_kinding _ _ [] 0 trivial) (ExprTy.unit _ _ _)

theorem zeros_clause_tail :
    ClauseTy Ωz Ψf [] [] (.mk [.proj 1] (.fn 1)) zerosDecl.ty := by
  refine ClauseTy.mk (SpineTy.proj (d := 1) (j := 2) (Rd := .var 0) rfl
    (by simp [SizeCtx.dom]) (SpineTy.nil _ _ _)) ?_
  exact ExprTy.localFun (g := zerosDecl) (as := [.var 2 0]) (by simp) Ψf_wf
    (streamT_kinding _ _ one_wf) (subst_ok (by simp) (by simp))
    (streamT_kinding _ _ (by simp [SizeWf, SizeWfAt, SizeCtx.dom, Size.subst, Size.shift]))
    ⟨G, by decide, conforms_ok (by simp [SizeCtx.dom]) (by simp)⟩

/-! ## Typing of `len` -/

abbrev Ωl : TypingEnv := ⟨[], block, sctCallOK 𝒢 2 Ψf⟩

theorem len_clause_nil :
    ClauseTy Ωl Ψf [] [] (.mk [.inst, .pat (.cons 0 (.var 10))] (.cons 0 .unit)) lenDecl.ty := by
  have hp : PatTy Ψf ([] ++ [(0, .star)]) (.cons 0 (.var 10)) (.mu (.var 1 0) (ListX 0))
      [(10, .unit)] [(2, .var 1 0)] [] :=
    PatTy.cons (c := 0) (j := 2) (Sc := .unit) rfl (by simp [SizeCtx.dom]) (PatTy.var _ _ 10 _)
  refine ClauseTy.mk (SpineTy.instT (X := 0) (by simp)
    (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp (SpineTy.nil _ _ (natT (.inf 0))))) ?_
  exact ExprTy.cons (c := 0) (b := .inf 0) (Sc := .unit) rfl (SizeLt.inf_inf (by decide))
    (natT_kinding _ _ [] 0 trivial) (ExprTy.unit _ _ _)

theorem len_clause_cons :
    ClauseTy Ωl Ψf [] [] (.mk [.inst, .pat (.cons 1 (.pair (.var 11) (.var 12)))]
      (.cons 1 (.app (.app (.fn 2) .inst) (.term (.var 12))))) lenDecl.ty := by
  have hp : PatTy Ψf ([] ++ [(0, .star)]) (.cons 1 (.pair (.var 11) (.var 12)))
      (.mu (.var 1 0) (ListX 0)) ([(11, .fvar 0)] ++ [(12, .mu (.var 2 0) (ListX 0))])
      ((2, .var 1 0) :: ([] ++ [])) ([] ++ []) :=
    PatTy.cons (c := 1) (j := 2) (Sc := .prod (.fvar 0) (.var 0)) rfl (by simp [SizeCtx.dom])
      (PatTy.pair (PatTy.var _ _ 11 _) (PatTy.var _ _ 12 _))
  refine ClauseTy.mk (SpineTy.instT (X := 0) (by simp)
    (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp (SpineTy.nil _ _ (natT (.inf 0))))) ?_
  exact ExprTy.cons (c := 1) (b := .inf 0) (Sc := .var 0) rfl (SizeLt.inf_inf (by decide))
    (natT_kinding _ _ [] 0 trivial)
    (ExprTy.app
      (ExprTy.instT (T := .fvar 0)
        (ExprTy.localFun (Ω := Ωl) (g := lenDecl) (as := [.var 2 0]) (by simp) Ψf_wf
          (lenTy_kinding _ _ one_wf) (subst_ok (by simp) (by simp))
          (lenTy_kinding _ _ (by simp [SizeWf, SizeWfAt, SizeCtx.dom, Size.subst, Size.shift]))
          ⟨G, by decide, conforms_ok (by simp [SizeCtx.dom]) (by simp)⟩)
        (.fvar rfl trivial))
      (ExprTy.var rfl))

/-! ## Typing of `count` -/

abbrev Ωn : TypingEnv := ⟨[], block, sctCallOK 𝒢 3 Ψf⟩

theorem count_clause_zero :
    ClauseTy Ωn Ψf [] [] (.mk [.inst, .pat (.cons 0 (.var 10))] (.cons 0 (.var 10)))
      countDecl.ty := by
  have hp : PatTy (Ψf ++ [(2, .var 1 0)]) [] (.cons 0 (.var 10)) (natT (.var 2 0))
      [(10, .unit)] [(3, .var 2 0)] [] :=
    PatTy.cons (c := 0) (j := 3) (Sc := .unit) rfl (by simp [SizeCtx.dom]) (PatTy.var _ _ 10 _)
  refine ClauseTy.mk (SpineTy.instS (j := 2) (by simp [SizeCtx.dom])
    (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp (SpineTy.nil _ _ (natT (.inf 0))))) ?_
  exact ExprTy.cons (c := 0) (b := .inf 0) (Sc := .unit) rfl (SizeLt.inf_inf (by decide))
    (natT_kinding _ _ [] 0 trivial) (ExprTy.var rfl)

theorem count_clause_suc :
    ClauseTy Ωn Ψf [] [] (.mk [.inst, .pat (.cons 1 (.var 11))]
      (.cons 1 (.app (.app (.fn 3) .inst) (.term (.var 11))))) countDecl.ty := by
  have hp : PatTy (Ψf ++ [(2, .var 1 0)]) [] (.cons 1 (.var 11)) (natT (.var 2 0))
      [(11, natT (.var 3 0))] [(3, .var 2 0)] [] :=
    PatTy.cons (c := 1) (j := 3) (Sc := .var 0) rfl (by simp [SizeCtx.dom]) (PatTy.var _ _ 11 _)
  refine ClauseTy.mk (SpineTy.instS (j := 2) (by simp [SizeCtx.dom])
    (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp (SpineTy.nil _ _ (natT (.inf 0))))) ?_
  exact ExprTy.cons (c := 1) (b := .inf 0) (Sc := .var 0) rfl (SizeLt.inf_inf (by decide))
    (natT_kinding _ _ [] 0 trivial)
    (ExprTy.app
      (ExprTy.instS (b := .var 3 0)
        (ExprTy.localFun (Ω := Ωn) (g := countDecl) (as := [.var 2 0]) (by simp) Ψf_wf
          (countTy_kinding _ _ one_wf) (subst_ok (by simp) (by simp))
          (countTy_kinding _ _ (by simp [SizeWf, SizeWfAt, SizeCtx.dom, Size.subst, Size.shift]))
          ⟨G, by decide, conforms_ok (by simp [SizeCtx.dom]) (by simp)⟩)
        (SizeLt.bound (i := 3) (n := 0) (a := .var 2 0) (by simp)
          (SizeLt.var_var (by simp [SizeCtx.dom]) (by omega))))
      (ExprTy.var rfl))

/-! ## Typing of `evalT` (mixed-variance functor + type operator β-subtyping) -/

abbrev Ωe : TypingEnv := ⟨[], block, sctCallOK 𝒢 4 Ψf⟩

theorem evalT_clause_leaf :
    ClauseTy Ωe Ψf [] [] (.mk [.pat (.cons 0 (.var 10))] (.cons 0 (.var 10))) evalTDecl.ty := by
  have hp : PatTy Ψf [] (.cons 0 (.var 10)) (bushT (.var 1 0)) [(10, .unit)] [(2, .var 1 0)] [] :=
    PatTy.cons (c := 0) (j := 2) (Sc := .unit) rfl (by simp [SizeCtx.dom]) (PatTy.var _ _ 10 _)
  refine ClauseTy.mk (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp
    (SpineTy.nil _ _ (.app IdOp (natT (.inf 0)) .star))) ?_
  have hcons : ExprTy Ωe (Ψf ++ [(2, .var 1 0)]) [] [(10, .unit)] (.cons 0 (.var 10))
      (natT (.inf 0)) :=
    ExprTy.cons (c := 0) (b := .inf 0) (Sc := .unit) rfl (SizeLt.inf_inf (by decide))
      (natT_kinding _ _ [] 0 trivial) (ExprTy.var rfl)
  exact ExprTy.sub hcons
    (SubTy.beta_r (idNat_kinding _ _) (SubTy.refl (natT_kinding _ _ [] 0 trivial)))
    (idNat_kinding _ _)

theorem evalT_clause_node :
    ClauseTy Ωe Ψf [] [] (.mk [.pat (.cons 1 (.pair (.var 11) (.var 12)))]
      (.app (.fn 4) (.term (.var 12)))) evalTDecl.ty := by
  have hp : PatTy Ψf [] (.cons 1 (.pair (.var 11) (.var 12))) (bushT (.var 1 0))
      ([(11, .arr (bushT (.var 2 0)) .unit)] ++ [(12, bushT (.var 2 0))])
      ((2, .var 1 0) :: ([] ++ [])) ([] ++ []) :=
    PatTy.cons (c := 1) (j := 2) (Sc := .prod (.arr (.var 0) .unit) (.var 0)) rfl
      (by simp [SizeCtx.dom]) (PatTy.pair (PatTy.var _ _ 11 _) (PatTy.var _ _ 12 _))
  refine ClauseTy.mk (SpineTy.pat (Γ₂ := []) (Ψ₂ := []) (Θ₂ := []) hp
    (SpineTy.nil _ _ (.app IdOp (natT (.inf 0)) .star))) ?_
  exact ExprTy.app
    (ExprTy.localFun (g := evalTDecl) (as := [.var 2 0]) (by simp) Ψf_wf
      (evalTTy_kinding _ _ one_wf) (subst_ok (by simp) (by simp))
      (evalTTy_kinding _ _ (by simp [SizeWf, SizeWfAt, SizeCtx.dom, Size.subst, Size.shift]))
      ⟨G, by decide, conforms_ok (by simp [SizeCtx.dom]) (by simp)⟩)
    (ExprTy.var rfl)

/-! ## The block satisfies `BlockTy` and is semantically valid -/

theorem block_typed : BlockTy [] block := by
  refine ⟨𝒢, sct, ?_, ?_⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · refine ⟨Ψf_wf, .arr (natT_kinding _ _ [] 0 one_wf) (natT_kinding _ _ [] 0 trivial), ?_⟩
      intro cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact copy_clause_zero
      · exact copy_clause_suc
    · refine ⟨Ψf_wf, streamT_kinding _ _ one_wf, ?_⟩
      intro cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact zeros_clause_head
      · exact zeros_clause_tail
    · refine ⟨Ψf_wf, lenTy_kinding _ _ one_wf, ?_⟩
      intro cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact len_clause_nil
      · exact len_clause_cons
    · refine ⟨Ψf_wf, countTy_kinding _ _ one_wf, ?_⟩
      intro cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact count_clause_zero
      · exact count_clause_suc
    · refine ⟨Ψf_wf, evalTTy_kinding _ _ one_wf, ?_⟩
      intro cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact evalT_clause_leaf
      · exact evalT_clause_node

/-- Theorem 4 applied to the V5 example block: all five functions are semantically valid. -/
theorem block_valid (ramsey : RamseyPairs) : SemValid block block := by
  apply theorem_4_proof ramsey block [] block (by simp) (by decide) _ block_typed
  · intro d hd; simp at hd
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> rfl

end NishtAbel2024V5.Example
