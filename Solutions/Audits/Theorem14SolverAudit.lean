import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024.Theorem14SolverAudit

def arrowAt (a : SizeExp) : TypeExpr := .arrTy (.mu a []) .unitTy
def g : FunDecl := ⟨1, [], arrowAt .infty, []⟩
def h : FunDecl := ⟨2, [], .arrTy (arrowAt (.inf 2)) .unitTy, []⟩
def sig : GlobalSig := [g, h]
def caller : FunDecl := ⟨0, [], .unitTy,
  [.mk [] (.app (.funRef 2 []) (.term (.funRef 1 []))) ]⟩
def block : MutualBlock := [caller]
def delta : KindingCtx := KindingCtx.empty
def input : Term := .app (.funRef 2 []) (.term (.funRef 1 []))
def constraints : List SizeConstraint := [⟨.inf 2, .le, .infty⟩]

theorem inf_h : InferTerm sig block [] [] delta (.funRef 2 [])
    (.arrTy (arrowAt (.inf 2)) .unitTy) [] [] [] (.funRef 2 []) := by
  have hi := InferTerm.funCall (sig := sig) (Ξ := block) (Φ := []) (Γ := [])
    (Δ := delta) (decl := h) (flexVars := []) (as := [])
  simp [sig, block, caller, h, delta, FlexVars.dom, SizeCtx.dom] at hi
  simpa [sig, block, caller, h, delta, arrowAt, TypeExpr.arrTy, TypeExpr.unitTy,
    TypeExpr.substSizes, TypeExpr.substSizesBranches, SizeExp.infty, SizeExp.subst] using hi

theorem inf_g : InferTerm sig block [] [] delta (.funRef 1 [])
    (arrowAt .infty) [] [] [] (.funRef 1 []) := by
  have hi := InferTerm.funCall (sig := sig) (Ξ := block) (Φ := []) (Γ := [])
    (Δ := delta) (decl := g) (flexVars := []) (as := [])
  simp [sig, block, caller, g, delta, FlexVars.dom, SizeCtx.dom] at hi
  simpa [sig, block, caller, g, delta, arrowAt, TypeExpr.arrTy, TypeExpr.unitTy,
    TypeExpr.substSizes, TypeExpr.substSizesBranches, SizeExp.infty, SizeExp.subst] using hi

theorem comp_g : CompareTypes [] delta .star .pos
    (arrowAt .infty) (arrowAt (.inf 2)) constraints := by
  have hmu : CompareTypes [] (delta.invScalePol .neg) .star .neg
      (.mu .infty []) (.mu (.inf 2) []) constraints := by
    have hm := CompareTypes.mu (Φ := []) (Δ := delta.invScalePol .neg)
      (π := .neg) (π₁ := .pos) (π₂ := .pos) (a := .infty) (b := .inf 2)
      (S := []) (S' := []) (C := [])
      (by decide) (by decide) (CompareBranches.nil _ _)
    simpa [constraints, SizeConstraint.ofPol, Polarity.infoMax, Polarity.comp] using hm
  have hleft : CompareTypes [] delta (.arr .pos .star .star) .pos
      (.app (.atom .arr) (.mu .infty []))
      (.app (.atom .arr) (.mu (.inf 2) [])) constraints := by
    have hs := CompareTypes.app (Φ := []) (Δ := delta) (π₁ := .neg)
      (π := .pos) (ι₁ := .star) (ι₂ := .arr .pos .star .star)
      (C₁ := []) (C₂ := constraints)
      (KindInfer.arr delta) (CompareTypes.atom _ _ _ _) hmu
    simpa [Polarity.comp] using hs
  have hk : KindInfer delta (.app (.atom .arr) (.mu (.inf 2) []))
      (.arr .pos .star .star) := by
    apply KindInfer.app (π := .neg) (κ := .star)
    · exact KindInfer.arr delta
    · have hm : KindInfer (delta.invScalePol .neg) (.mu (.inf 2) []) .star := by
        apply KindInfer.mu
        · simp [SizeWf]
        · simp
      exact KindCheck.sub hm (SubKind.star _)
  have hs := CompareTypes.app (Φ := []) (Δ := delta) (π₁ := .pos)
    (π := .pos) (ι₁ := .star) (ι₂ := .star) (C₁ := constraints) (C₂ := [])
    hk hleft (CompareTypes.atom _ _ _ .unit)
  simpa [arrowAt, TypeExpr.arrTy, TypeExpr.unitTy, Polarity.comp] using hs

theorem empty_hygiene (A B : TypeExpr) : FlexPolHygiene [] delta A B := by
  simp [FlexPolHygiene, FlexVars.lookupSizePol, FlexVars.lookupPol, SizeExp.var, SizeMin.single]

theorem body_check : CheckTerm sig block [] [] delta .unitTy input [] constraints [] input := by
  have hg : CheckTerm sig block [] [] delta (arrowAt (.inf 2)) (.funRef 1 [])
      [] constraints [] (.funRef 1 []) := by
    simpa using (CheckTerm.sub inf_g (empty_hygiene _ _) comp_g)
  have hi := InferTerm.appTerm inf_h hg
  have hc := CompareTypes.atom (Φ := []) delta .star .pos .unit
  simpa [input, TypeExpr.unitTy] using (CheckTerm.sub hi (empty_hygiene _ _) hc)

theorem strict_irreflexive_inf (n : Nat) : ¬ SizeLt [] (.inf n) (.inf n) := by
  intro h
  cases h with
  | inf_lt_inf hn => omega

theorem no_coherent (φ : FlexSubst) : ¬ CoherentSubst [] constraints φ := by
  intro h
  have hc := h.2 ⟨.inf 2, .le, .infty⟩ (by simp [constraints])
  change SizeLt [] (.inf 2) (.inf 2) at hc
  exact strict_irreflexive_inf 2 hc

theorem unit_hygiene : SignatureFixpointHygiene delta .unitTy := by
  simp [SignatureFixpointHygiene, NegFixpointPolClean, TypeExpr.allMuBranchLists,
    TypeExpr.allNuFieldLists, TypeExpr.unitTy, SizeOccursIn, TypeExpr.allSizeVars]

def noGraphs : InvGraphFamily := ⟨fun _ => 0, fun _ _ => []⟩

theorem noGraphs_sct : SCTValid noGraphs := by
  constructor
  · constructor
    · exact ⟨[], by simp [noGraphs]⟩
    · simp [noGraphs]
  · have noClosure : ∀ f g G, InvGraphClosure noGraphs f g G → False := by
      intro f g G hc
      induction hc with
      | base hm => simp [noGraphs] at hm
      | comp _ _ ih _ => exact ih
    intro f G hc _
    exact (noClosure f f G hc).elim

theorem clause_run : Nonempty (Algorithm2ClauseRun sig block noGraphs 0 [] .unitTy [] input
    (.mk [] input)) := by
  apply Nonempty.intro
  refine ⟨.unitTy, [], [], [], [], [], constraints, [], input, ?_, ?_, ?_, ?_, ?_⟩
  · exact InferSpine.nil _ _
  · constructor
    · exact KindingCtxExtWf.nil _
    · simp
  · exact SizeCtxWf.nil
  · simpa [delta, KindingCtx.empty, KindingCtx.extSizes, KindingCtx.append] using body_check
  · constructor
    · rfl
    · simp [LocalCallsConform, LocalCallsConformElim, Term.applyFlex, Elim.applyFlex,
        input, block, caller]

/-- The original formal Algorithm 2 accepts this derivation despite its
unsatisfiable constraints; the global environment is not source-encoded. -/
theorem algorithm_accepts : Algorithm2Accepts sig block block := by
  refine ⟨noGraphs, noGraphs_sct, ?_, ?_⟩
  · simp [block, caller, noGraphs]
  · constructor
    · refine ⟨rfl, ?_, ?_, SizeCtxWf.nil, ?_, ?_⟩
      · exact EncodeType.unit _ _
      · simpa [caller, KindingCtx.extSizes, delta, KindingCtx.empty] using unit_hygiene
      · exact KindCheck.sub (KindInfer.unit _) (SubKind.star _)
      · constructor
        · exact ⟨[], input, rfl, clause_run⟩
        · constructor
    · constructor

/-- Exact second conjunct of the saved original Theorems 13/14 bundle. -/
def FrozenMiddle : Prop :=
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (Δ₀ : KindingCtx)
       (Ψ₁ Ψ₂ : SizeCtx) (A A₀ A'' : TypeExpr) (qs qs' : PatSpine)
       (Γ : TermCtx) (Δ : List TyDecl) (t t' : Term)
       (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar),
      SizeCtxWf (Ψ₁ ++ Ψ₂) →
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ A'' Γ Δ Ψ₂ qs' →
      CheckTerm sig Ξ ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) A'' t Φ Cs T t' →
      CoherentSubst (Ψ₁ ++ Ψ₂) Cs (solveConstraintGraph (Ψ₁ ++ Ψ₂) Cs T))

theorem frozen_middle_false : ¬ FrozenMiddle := by
  intro hall
  apply no_coherent (solveConstraintGraph [] constraints [])
  have hc := hall sig block delta [] [] .unitTy .unitTy .unitTy [] [] [] []
    input input [] constraints [] SizeCtxWf.nil (EncodeType.unit _ _)
    (by simpa [delta, KindingCtx.empty, KindingCtx.extSizes] using unit_hygiene)
    (by simpa [delta, KindingCtx.empty, KindingCtx.extSizes] using InferSpine.nil delta .unitTy)
    (by simpa [delta, KindingCtx.empty, KindingCtx.extSizes, KindingCtx.append] using body_check)
  simpa using hc

#print axioms body_check
#print axioms no_coherent
#print axioms frozen_middle_false
#print axioms algorithm_accepts

end NishtAbel2024.Theorem14SolverAudit
