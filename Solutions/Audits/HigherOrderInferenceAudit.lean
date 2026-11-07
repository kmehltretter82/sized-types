import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024.HigherOrderInferenceAudit

/-- The input type arguments and source signature are individually
unannotated, higher-kinded, and beta-normal. -/
def k : SKind := .arr .mixed .star .star
def arg : TypeExpr := .lam 2 .star .unitTy
def body : TypeExpr := .lam 0 k (.app (.atom (.var 0)) .unitTy)
def signature : TypeExpr := .allTy (Kind.ofSKind k) body
def result : TypeExpr := .app arg .unitTy
def Γ : TermCtx := [(0, signature)]
def bctx : KindingCtx := KindingCtx.empty.extType 0 .mixed (Kind.ofSKind k)

mutual
/-- Syntactic beta-normality of types, including fixpoint branch bodies.
This predicate is used only to describe the concrete input and result. -/
def BetaNormal : TypeExpr → Prop
  | .atom _ => True
  | .lam _ _ F => BetaNormal F
  | .app F G => (∀ X ι body, F ≠ .lam X ι body) ∧ BetaNormal F ∧ BetaNormal G
  | .mu _ S | .nu _ S => BetaNormalBranches S

def BetaNormalBranches : List (Nat × TypeExpr) → Prop
  | [] => True
  | (_, F) :: S => BetaNormal F ∧ BetaNormalBranches S
end

theorem arg_unannotated : arg.isUnannotated := by trivial
theorem signature_unannotated : signature.isUnannotated := by trivial
theorem arg_beta_normal : BetaNormal arg := by simp [arg, BetaNormal, TypeExpr.unitTy]
theorem signature_beta_normal : BetaNormal signature := by
  simp [signature, body, TypeExpr.allTy, TypeExpr.unitTy, BetaNormal]
theorem result_not_beta_normal : ¬ BetaNormal result := by
  simp [result, arg, BetaNormal]

theorem arg_fw_kind : FwKindCheck KindingCtx.empty arg k := by
  apply FwKindCheck.lam
  exact .infer (.unit _)

theorem arg_kind : KindCheck KindingCtx.empty arg (Kind.ofSKind k) := by
  apply KindCheck.lam
  · exact .star _
  · exact .sub (.unit _) (.star _)

theorem body_infer : KindInfer bctx (.app (.atom (.var 0)) .unitTy) .star := by
  apply KindInfer.app (π := .mixed) (κ := .star)
  · apply KindInfer.var (π := .mixed)
    · simp [bctx, k, KindingCtx.extType, KindingCtx.empty, Kind.ofSKind]
    · rfl
  · exact .sub (.unit _) (.star _)

theorem body_fw_infer : FwKindInfer bctx (.app (.atom (.var 0)) .unitTy) .star := by
  apply FwKindInfer.app (π := .mixed) (ι := .star)
  · apply FwKindInfer.var (π := .mixed) (ι := k)
    · simp [bctx, k, KindingCtx.extType, KindingCtx.empty, Kind.ofSKind]
    · rfl
  · exact .infer (.unit _)

theorem body_fw_kind : FwKindCheck KindingCtx.empty body (.arr .mixed k .star) := by
  apply FwKindCheck.lam
  exact .infer body_fw_infer

theorem body_kind : KindCheck KindingCtx.empty body (Kind.ofSKind (.arr .mixed k .star)) := by
  apply KindCheck.lam
  · exact .arr (.star _) (.star _)
  · exact .sub body_infer (.star _)

theorem signature_fw_kind : FwKindCheck KindingCtx.empty signature .star := by
  unfold signature TypeExpr.allTy
  apply FwKindCheck.infer
  apply FwKindInfer.app (π := .pos) (ι := .arr .mixed k .star)
  · exact FwKindInfer.all
  · exact body_fw_kind

theorem signature_kind : KindCheck KindingCtx.empty signature .star := by
  unfold signature TypeExpr.allTy
  apply KindCheck.sub (κ := .star)
  · apply KindInfer.app (π := .pos) (κ := Kind.ofSKind (.arr .mixed k .star))
    · apply KindInfer.all
      exact .arr (.star _) (.star _)
    · exact body_kind
  · exact .star _

theorem term_context_wf : TermCtxWf KindingCtx.empty Γ := by
  simpa [Γ] using (TermCtxWf.snoc (x := 0) TermCtxWf.nil signature_kind)

theorem arg_encoded : EncodeType .mixed .mixed KindingCtx.empty arg [] arg := by
  apply EncodeType.lam
  · simp [SizeCtx.dom]
  · exact EncodeType.unit _ _

/-- Encoding application helper for the no-generated-size special case. -/
theorem encode_app_empty {πstar π π' : Polarity} {Δ : KindingCtx}
    {F G : TypeExpr} {ι ι' : SKind}
    (hfw : FwKindInfer Δ F (.arr π' ι ι'))
    (hk : KindInfer Δ F (.arr π' (Kind.ofSKind ι) (Kind.ofSKind ι')))
    (ha : KindCheck (Δ.invScalePol π') G (Kind.ofSKind ι))
    (hf : EncodeType πstar π Δ F [] F)
    (hg : EncodeType πstar (Polarity.comp π' π) (Δ.invScalePol π') G [] G) :
    EncodeType πstar π Δ (.app F G) [] (.app F G) := by
  apply EncodeType.app (π' := π') (ι := ι) (ι' := ι') (Ψ₁ := []) (Ψ₂ := [])
  · exact hfw
  · simpa [KindingCtx.extSizes] using hk
  · simpa [KindingCtx.extSizes] using ha
  · exact hf
  · exact hg
  · simp [SizeCtx.dom, List.Disjoint]
  · simp [SizeCtx.dom, List.Disjoint]
  · simp [SizeCtx.dom, List.Disjoint]

theorem body_encoded {πstar π : Polarity} :
    EncodeType πstar π KindingCtx.empty body [] body := by
  unfold body
  apply EncodeType.lam
  · simp [SizeCtx.dom]
  · change EncodeType πstar π bctx (.app (.atom (.var 0)) .unitTy) []
      (.app (.atom (.var 0)) .unitTy)
    apply encode_app_empty (π' := .mixed) (ι := .star) (ι' := .star)
    · apply FwKindInfer.var (π := .mixed) (ι := k)
      · simp [bctx, k, KindingCtx.extType, KindingCtx.empty, Kind.ofSKind]
      · rfl
    · apply KindInfer.var (π := .mixed)
      · simp [bctx, k, KindingCtx.extType, KindingCtx.empty, Kind.ofSKind]
      · rfl
    · exact .sub (.unit _) (.star _)
    · apply EncodeType.var (π' := .mixed) (ι := k)
      · simp [bctx, k, KindingCtx.extType, KindingCtx.empty, Kind.ofSKind]
      · rfl
    · exact EncodeType.unit _ _

/-- The full higher-order signature is an actual source encoding, not
merely an arbitrary well-kinded target type. -/
theorem signature_encoded : EncodeType .neg .pos KindingCtx.empty signature [] signature := by
  unfold signature TypeExpr.allTy
  apply encode_app_empty (π' := .pos) (ι := .arr .mixed k .star) (ι' := .star)
  · exact FwKindInfer.all
  · apply KindInfer.all
    exact .arr (.star _) (.star _)
  · exact body_kind
  · exact EncodeType.all _ _ _
  · exact body_encoded

/-- The actual original inference rule produces the uncontracted inner
application, although the encoded argument and signature are kinded. -/
theorem actual_appTy : InferTerm [] [] [] Γ KindingCtx.empty
    (.app (.var 0) (.tyArg arg)) result [] [] [] (.app (.var 0) (.tyArg arg)) := by
  change InferTerm [] [] [] Γ KindingCtx.empty
    (.app (.var 0) (.tyArg arg)) (body.normApp arg)
    ([] ++ []) [] [] (.app (.var 0) (.tyArg arg))
  apply InferTerm.appTy (ι := k) (Ψ := [])
  · exact arg_encoded
  · simp [SizeCtx.dom, List.Disjoint, FlexVars.dom]
  · exact InferTerm.var (by simp [Γ, signature])

theorem result_not_kinded : ¬ KindCheck KindingCtx.empty result .star := by
  intro h
  cases h with
  | sub hi hs =>
    cases hi with
    | app hhead harg => cases hhead

theorem result_not_fw_kinded : ¬ FwKindCheck KindingCtx.empty result .star := by
  intro h
  cases h with
  | infer hi =>
    cases hi with
    | app hhead harg => cases hhead

/-- The original declarative application rule also returns the same raw
result for this example, independently of the global typing environment. -/
theorem declarative_appTy (Ω : TypingEnv) : ExprInfer Ω KindingCtx.empty Γ
    (.app (.var 0) (.tyArg arg)) result := by
  change ExprInfer Ω KindingCtx.empty Γ (.app (.var 0) (.tyArg arg)) (body.normApp arg)
  apply ExprInfer.appTy (κ := Kind.ofSKind k)
  · exact .var (by simp [Γ, signature])
  · exact arg_kind

/-- Contracting the newly exposed inner type-level beta-redex gives the
well-kinded type expected for this particular example. -/
theorem inner_beta : arg.normApp .unitTy = .unitTy := rfl
theorem repaired_example_kinded : KindCheck KindingCtx.empty .unitTy .star :=
  .sub (.unit _) (.star _)

/-- A single kernel-checked conjunction records actual encoding,
well-formed term context, actual inference, and failure of result kinding. -/
theorem wellformed_encoded_appTy_failure :
    TermCtxWf KindingCtx.empty Γ ∧
    EncodeType .neg .pos KindingCtx.empty signature [] signature ∧
    FwKindCheck KindingCtx.empty signature .star ∧
    FwKindCheck KindingCtx.empty arg k ∧
    EncodeType .mixed .mixed KindingCtx.empty arg [] arg ∧
    InferTerm [] [] [] Γ KindingCtx.empty (.app (.var 0) (.tyArg arg))
      result [] [] [] (.app (.var 0) (.tyArg arg)) ∧
    ¬ KindCheck KindingCtx.empty result .star :=
  ⟨term_context_wf, signature_encoded, signature_fw_kind, arg_fw_kind,
    arg_encoded, actual_appTy, result_not_kinded⟩

#print axioms signature_fw_kind
#print axioms signature_kind
#print axioms arg_fw_kind
#print axioms arg_encoded
#print axioms signature_encoded
#print axioms actual_appTy
#print axioms result_not_kinded
#print axioms result_not_fw_kinded
#print axioms declarative_appTy
#print axioms term_context_wf
#print axioms wellformed_encoded_appTy_failure
end NishtAbel2024.HigherOrderInferenceAudit
