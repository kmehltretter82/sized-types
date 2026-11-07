import Solutions.V5.InfEncode
import Solutions.V5.Theorem6
import Solutions.V5.Main

/-! # V5 inference: solver post-check soundness (Theorem 14) and Algorithm 2 soundness (Theorem 15) -/

namespace NishtAbel2024V5

open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid ConformsToGraph FunName EdgeRel)

/-! ## Flexible domain of Algorithm 1 (`solve`) and Theorem 14 -/

theorem foldl_preserves {α β : Type} {P : α → Prop} {f : α → β → α}
    (hf : ∀ a b, P a → P (f a b)) : ∀ (L : List β) {a : α}, P a → P (L.foldl f a)
  | [], _, ha => ha
  | b :: L, _, ha => foldl_preserves hf L (hf _ b ha)

theorem solveRound_flexDom (fuel : Nat) (Φ : List FlexVar) (C : List SConstr) (T : List Nat)
    (hΦ : ∀ v ∈ Φ, FlexName v.name) {φ : FlexSubst} (hφ : FlexDom φ) :
    FlexDom (solveRound fuel Φ C T φ) := by
  unfold solveRound
  refine foldl_preserves (fun ψ v hψ => ?_) Φ hφ
  split
  · exact hψ
  · dsimp only
    split
    · exact hψ
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
        have hm' : m ∈ Φ.map FlexVar.name := (List.mem_filter.mp hm).1
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm'
        exact hΦ w hw
      · exact hψ p hp

theorem solve_flexDom (fuel : Nat) (Φ : List FlexVar) (C : List SConstr) (T : List Nat)
    (hΦ : ∀ v ∈ Φ, FlexName v.name) : FlexDom (solve fuel Φ C T) := by
  unfold solve
  have hfold : FlexDom ((List.range (Φ.length + 1)).foldl
      (fun φ _ => solveRound fuel Φ C T φ) []) :=
    foldl_preserves (fun φ _ hφ => solveRound_flexDom fuel Φ C T hΦ hφ)
      (List.range (Φ.length + 1)) (fun _ h => by simp at h)
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hfold p hp
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    exact hΦ v hv

/-- **Theorem 14** (Soundness of the post-checked constraint solver, Section 6.4): if all flexible
variables in `Φ` have odd names and the solution `φ* = solve fuel Φ C T` passes `checkScope` and
`checkCoherent`, then `φ*` has flexible domain, satisfies `ScopeOK φ* Φ`, and is coherent with `C`
(`Coherent φ* C`). -/
theorem theorem_14 (fuel : Nat) (Φ : List FlexVar) (C : List SConstr) (T : List Nat)
    (hΦ : ∀ v ∈ Φ, FlexName v.name)
    (hscope : checkScope (solve fuel Φ C T) Φ = true)
    (hcoh : checkCoherent fuel (solve fuel Φ C T) C = true) :
    FlexDom (solve fuel Φ C T) ∧
      ScopeOK (solve fuel Φ C T) Φ ∧
      Coherent (solve fuel Φ C T) C :=
  ⟨solve_flexDom fuel Φ C T hΦ, checkScope_sound hscope, checkCoherent_sound hcoh⟩

/-! ## Inference only generates flexible variable names -/

theorem encFlex_flex {Ψ ΨG : SizeCtx} (h : ∀ i ∈ ΨG.dom, FlexName i) :
    ∀ v ∈ encFlex Ψ ΨG, FlexName v.name := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  exact h p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)

theorem callFlex_flex {Ψ : SizeCtx} {g : FunDecl} {as : List Nat} (h : ∀ k ∈ as, FlexName k) :
    ∀ v ∈ callFlex Ψ g as, FlexName v.name := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  exact h p.2 (List.of_mem_zip hp).2

theorem inference_flex {Ω : InfEnv} :
    (∀ {Ψ Θ Γ r A Φ C T K}, InferTm Ω Ψ Θ Γ r A Φ C T K → ∀ v ∈ Φ, FlexName v.name) ∧
    (∀ {Ψ Θ Γ A t Φ C T K}, CheckTm Ω Ψ Θ Γ A t Φ C T K → ∀ v ∈ Φ, FlexName v.name) ∧
    (∀ {Ψ Θ Γ A cl Φ C T K}, CheckClause Ω Ψ Θ Γ A cl Φ C T K → ∀ v ∈ Φ, FlexName v.name) := by
  let P₁ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (r : Tm) (A : Ty) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : InferTm Ω Ψ Θ Γ r A Φ C T K) => ∀ v ∈ Φ, FlexName v.name
  let P₂ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (t : Tm) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckTm Ω Ψ Θ Γ A t Φ C T K) => ∀ v ∈ Φ, FlexName v.name
  let P₃ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (D : List Clause)
      (Φ : List FlexVar) (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckClauses Ω Ψ Θ Γ A D Φ C T K) => ∀ v ∈ Φ, FlexName v.name
  let P₄ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (cl : Clause)
      (Φ : List FlexVar) (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckClause Ω Ψ Θ Γ A cl Φ C T K) => ∀ v ∈ Φ, FlexName v.name
  have sVar : ∀ {Ψ Θ Γ x A} (hx : Γ.lookup x = some A), P₁ Ψ Θ Γ (.var x) A [] [] [] []
      (.var hx) := by intro _ _ _ _ _ _ _ h; simp at h
  have sApp : ∀ {Ψ Θ Γ r s A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (hr : InferTm Ω Ψ Θ Γ r (.arr A B) Φ₁ C₁ T₁ K₁) (hs : CheckTm Ω Ψ Θ Γ A s Φ₂ C₂ T₂ K₂),
      P₁ Ψ Θ Γ r (.arr A B) Φ₁ C₁ T₁ K₁ hr → P₂ Ψ Θ Γ A s Φ₂ C₂ T₂ K₂ hs →
      P₁ Ψ Θ Γ (.app r (.term s)) B (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂) (.app hr hs) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ih₁ v hv
    · exact ih₂ v hv
  have sProj : ∀ {Ψ Θ Γ r a R d j Rd Φ C T K} (hr : InferTm Ω Ψ Θ Γ r (.nu a R) Φ C T K)
      (hd : R[d]? = some Rd) (hj : FlexName j),
      P₁ Ψ Θ Γ r (.nu a R) Φ C T K hr →
      P₁ Ψ Θ Γ (.app r (.proj d)) (Rd.substTy 0 (.nu (.var j 0) R))
        (⟨j, .neg, Ψ⟩ :: Φ) (⟨Ψ, .var j 0, a, true, true⟩ :: C)
        ((if Rd.hasBVar 0 then [] else [j]) ++ T) K (.proj hr hd hj) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj ih v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hj
    · exact ih v hv
  have sInst : ∀ {Ψ Θ Γ r κ B G G' ΨG Φ C T K} (hr : InferTm Ω Ψ Θ Γ r (.allT κ B) Φ C T K)
      (hG : Unsized G) (hkG : EKinding Θ.toK [] G κ)
      (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G'),
      P₁ Ψ Θ Γ r (.allT κ B) Φ C T K hr →
      P₁ Ψ Θ Γ (.app r .inst) (B.substTy 0 G') (encFlex Ψ ΨG ++ Φ) C T K
        (.inst hr hG hkG henc) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ henc ih v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact encFlex_flex (encode_facts henc).2.2.1 v hv
    · exact ih v hv
  have sGlobal : ∀ {Ψ Θ Γ g as} (hg : g ∈ Ω.sig) (hlen : as.length = g.sizeParams.length)
      (hflex : ∀ k ∈ as, FlexName k),
      P₁ Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) [] []
        (.global hg hlen hflex) := by
    intro _ _ _ _ _ _ _ hflex v hv
    exact callFlex_flex hflex v hv
  have sLocal : ∀ {Ψ Θ Γ g as} (hg : g ∈ Ω.block) (hlen : as.length = g.sizeParams.length)
      (hflex : ∀ k ∈ as, FlexName k),
      P₁ Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) []
        [⟨Ψ, g.name, as.map fun k => .var k 0⟩] (.local hg hlen hflex) := by
    intro _ _ _ _ _ _ _ hflex v hv
    exact callFlex_flex hflex v hv
  have sUnit : ∀ {Ψ Θ Γ}, P₂ Ψ Θ Γ .unit .unit [] [] [] [] .unit := by
    intro _ _ _ _ h; simp at h
  have sPair : ∀ {Ψ Θ Γ t u A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (ht : CheckTm Ω Ψ Θ Γ A t Φ₁ C₁ T₁ K₁) (hu : CheckTm Ω Ψ Θ Γ B u Φ₂ C₂ T₂ K₂),
      P₂ Ψ Θ Γ A t Φ₁ C₁ T₁ K₁ ht → P₂ Ψ Θ Γ B u Φ₂ C₂ T₂ K₂ hu →
      P₂ Ψ Θ Γ (.prod A B) (.pair t u) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂)
        (.pair ht hu) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ih₁ v hv
    · exact ih₂ v hv
  have sCons : ∀ {Ψ Θ Γ c j t a S Sc Φ C T K} (hc : S[c]? = some Sc) (hj : FlexName j)
      (ht : CheckTm Ω Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t Φ C T K),
      P₂ Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t Φ C T K ht →
      P₂ Ψ Θ Γ (.mu a S) (.cons c t) (⟨j, .pos, Ψ⟩ :: Φ)
        (⟨Ψ, .var j 0, a, true, true⟩ :: C) ((if Sc.hasBVar 0 then [] else [j]) ++ T) K
        (.cons hc hj ht) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj _ ih v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hj
    · exact ih v hv
  have sPack : ∀ {Ψ Θ Γ t κ B G G' ΨG Φ C T K} (hG : Unsized G) (hkG : EKinding Θ.toK [] G κ)
      (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G')
      (ht : CheckTm Ω Ψ Θ Γ (B.substTy 0 G') t Φ C T K),
      P₂ Ψ Θ Γ (B.substTy 0 G') t Φ C T K ht →
      P₂ Ψ Θ Γ (.exT κ B) (.pack t) (encFlex Ψ ΨG ++ Φ) C T K (.pack hG hkG henc ht) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ henc _ ih v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact encFlex_flex (encode_facts henc).2.2.1 v hv
    · exact ih v hv
  have sLam : ∀ {Ψ Θ Γ A D Φ C T K} (hD : CheckClauses Ω Ψ Θ Γ A D Φ C T K),
      P₃ Ψ Θ Γ A D Φ C T K hD → P₂ Ψ Θ Γ A (.lam D) Φ C T K (.lam hD) := by
    intro _ _ _ _ _ _ _ _ _ _ ih; exact ih
  have sSub : ∀ {Ψ Θ Γ r A B Φ C₁ C₂ T K} (hr : InferTm Ω Ψ Θ Γ r A Φ C₁ T K)
      (hcmp : Compare Ψ Θ.toK A B .star C₂),
      P₁ Ψ Θ Γ r A Φ C₁ T K hr → P₂ Ψ Θ Γ B r Φ (C₁ ++ C₂) T K (.sub hr hcmp) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih; exact ih
  have sNil : ∀ {Ψ Θ Γ A}, P₃ Ψ Θ Γ A [] [] [] [] [] .nil := by
    intro _ _ _ _ _ h; simp at h
  have sConsCl : ∀ {Ψ Θ Γ A cl D Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (hcl : CheckClause Ω Ψ Θ Γ A cl Φ₁ C₁ T₁ K₁)
      (hD : CheckClauses Ω Ψ Θ Γ A D Φ₂ C₂ T₂ K₂),
      P₄ Ψ Θ Γ A cl Φ₁ C₁ T₁ K₁ hcl → P₃ Ψ Θ Γ A D Φ₂ C₂ T₂ K₂ hD →
      P₃ Ψ Θ Γ A (cl :: D) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂) (.cons hcl hD) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ih₁ v hv
    · exact ih₂ v hv
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

/-! ## Rigid types and contexts are invariant under flexible substitutions -/

theorem Size.subst_eq_self (φ : FlexSubst) :
    ∀ (a : Size), (∀ i ∈ a.fvars, φ.lookup i = none) → a.subst φ = a
  | .inf _, _ => rfl
  | .bvar _ _, _ => rfl
  | .var i n, h => by simp [Size.subst, h i (by simp [Size.fvars])]
  | .meet a b, h => by
    simp only [Size.fvars, List.mem_append] at h
    simp [Size.subst, Size.subst_eq_self φ a (fun i hi => h i (Or.inl hi)),
      Size.subst_eq_self φ b (fun i hi => h i (Or.inr hi))]

mutual

theorem Ty.substSize_eq_self (φ : FlexSubst) :
    ∀ (A : Ty), (∀ i ∈ A.sizeVars, φ.lookup i = none) → A.substSize φ = A
  | .unit, _ => rfl
  | .var _, _ => rfl
  | .fvar _, _ => rfl
  | .prod A B, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Ty.substSize_eq_self φ A (fun i hi => h i (Or.inl hi)),
      Ty.substSize_eq_self φ B (fun i hi => h i (Or.inr hi))]
  | .arr A B, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Ty.substSize_eq_self φ A (fun i hi => h i (Or.inl hi)),
      Ty.substSize_eq_self φ B (fun i hi => h i (Or.inr hi))]
  | .app F G _, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Ty.substSize_eq_self φ F (fun i hi => h i (Or.inl hi)),
      Ty.substSize_eq_self φ G (fun i hi => h i (Or.inr hi))]
  | .lam _ F, h => by simp [Ty.substSize, Ty.substSize_eq_self φ F h]
  | .allT _ B, h => by simp [Ty.substSize, Ty.substSize_eq_self φ B h]
  | .exT _ B, h => by simp [Ty.substSize, Ty.substSize_eq_self φ B h]
  | .allS a B, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Size.subst_eq_self φ a (fun i hi => h i (Or.inl hi)),
      Ty.substSize_eq_self φ B (fun i hi => h i (Or.inr hi))]
  | .exS a B, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Size.subst_eq_self φ a (fun i hi => h i (Or.inl hi)),
      Ty.substSize_eq_self φ B (fun i hi => h i (Or.inr hi))]
  | .mu a S, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Size.subst_eq_self φ a (fun i hi => h i (Or.inl hi)),
      Ty.substSizeList_eq_self φ S (fun i hi => h i (Or.inr hi))]
  | .nu a R, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Size.subst_eq_self φ a (fun i hi => h i (Or.inl hi)),
      Ty.substSizeList_eq_self φ R (fun i hi => h i (Or.inr hi))]

theorem Ty.substSizeList_eq_self (φ : FlexSubst) :
    ∀ (S : List Ty), (∀ i ∈ Ty.sizeVarsList S, φ.lookup i = none) → Ty.substSizeList φ S = S
  | [], _ => rfl
  | A :: S, h => by
    simp only [Ty.sizeVarsList, List.mem_append] at h
    simp [Ty.substSizeList, Ty.substSize_eq_self φ A (fun i hi => h i (Or.inl hi)),
      Ty.substSizeList_eq_self φ S (fun i hi => h i (Or.inr hi))]

end

theorem SizeCtx.substBounds_of_inf (φ : FlexSubst) :
    ∀ (Ψ : SizeCtx), (∀ p ∈ Ψ, p.2 = .inf 0) → Ψ.substBounds φ = Ψ
  | [], _ => rfl
  | (i, a) :: Ψ, hb => by
    have ha : a = .inf 0 := hb (i, a) (by simp)
    subst ha
    simp only [SizeCtx.substBounds_cons, Size.subst]
    rw [SizeCtx.substBounds_of_inf φ Ψ (fun p hp => hb p (List.mem_cons_of_mem _ hp))]

/-! ## Invocation graphs and Algorithm 2 -/

theorem callGraph_conforms (fuel : Nat) (Ψf : SizeCtx) (φ : FlexSubst) (k : CallRec) :
    ConformsToGraph (SizeLt (k.ctx.substBounds φ)) (SizeLe (k.ctx.substBounds φ))
      (callGraph fuel Ψf φ k) (k.args.map (Size.subst φ)) (Ψf.map fun p => Size.var p.1 0) := by
  refine ⟨rfl, by simp [callGraph], ?_⟩
  intro i j hi hj
  have hi' : i < (k.args.map (Size.subst φ)).length := hi
  have hj' : j < Ψf.length := by simpa [callGraph] using hj
  have hlook := NishtAbel2024V2.canonical_lookup (k.args.map (Size.subst φ)).length Ψf.length
    (fun i j =>
      match (k.args.map (Size.subst φ))[i]?, Ψf[j]? with
      | some a, some p =>
        if sizeLtB fuel (k.ctx.substBounds φ) a (.var p.1 0) then some .lt
        else if sizeLeB fuel (k.ctx.substBounds φ) a (.var p.1 0) then some .le
        else none
      | _, _ => none) i j hi' hj'
  have hlook' : (callGraph fuel Ψf φ k).edgeAt i j = _ := hlook
  rw [hlook', List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj']
  simp only [List.get_eq_getElem, List.getElem_map]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · split at h
    · rename_i hlt
      exact sizeLtB_sound _ _ _ _ hlt
    · split at h <;> simp at h
  · split at h
    · simp at h
    · split at h
      · rename_i hle
        exact sizeLeB_sound hle
      · simp at h

theorem blockGraphs_mem (fuel : Nat) (Ξ : List FunDecl) (runs : FunName → Clause → ClauseRun)
    {d : FunDecl} (hd : d ∈ Ξ) {cl : Clause} (hcl : cl ∈ d.clauses)
    {k : CallRec} (hk : k ∈ (runs d.name cl).calls) :
    callGraph fuel d.sizeParams ((runs d.name cl).solution fuel) k ∈
      (blockGraphs fuel Ξ runs).graphs d.name k.callee := by
  simp only [blockGraphs, List.mem_flatMap]
  refine ⟨d, hd, ?_⟩
  simp only [↓reduceIte, List.mem_flatMap, List.mem_map, List.mem_filter, beq_iff_eq]
  exact ⟨cl, hcl, k, ⟨hk, rfl⟩, rfl⟩

theorem blockGraphs_arity (fuel : Nat) (Ξ : List FunDecl) (runs : FunName → Clause → ClauseRun)
    (hnd : (Ξ.map FunDecl.name).Nodup) {d : FunDecl} (hd : d ∈ Ξ) :
    (blockGraphs fuel Ξ runs).arity d.name = d.sizeParams.length := by
  simp only [blockGraphs]
  cases hf : Ξ.find? (fun d' => d'.name == d.name) with
  | none =>
    have := List.find?_eq_none.mp hf d hd
    simp at this
  | some d' =>
    have hd' := List.mem_of_find?_eq_some hf
    have hname : d'.name = d.name := by simpa using List.find?_some hf
    have heq : d' = d := List.inj_on_of_nodup_map hnd hd' hd hname
    rw [heq]

theorem ListRel.mem_right {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : ListRel R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => simp at hb
  | cons hr _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, by simp, hr⟩
    · obtain ⟨a, ha, hab⟩ := ih hb
      exact ⟨a, by simp [ha], hab⟩

/-- **Corollary to Theorems 13 & 14** (Section 6.5, p. 59): if `Σ` is well-formed and Algorithm 2
accepts `Ξ` with annotated declarations `Ξannot`, then `Σ ⊢ Ξannot` (`BlockTy sig Ξannot`). -/
theorem algorithm2_typing {sig Ξ Ξannot : List FunDecl} (hsigwf : DeclsWf sig)
    (hacc : Algorithm2Accepts sig Ξ Ξannot) : BlockTy sig Ξannot := by
  obtain ⟨henc_rel, hnd, fuel, runs, hclauses, hsct⟩ := hacc
  have hblockwf : DeclsWf Ξannot := by
    intro d hd
    obtain ⟨d₀, _, hd_enc⟩ := henc_rel.mem_right hd
    exact hd_enc.wf
  refine ⟨blockGraphs fuel Ξannot runs, hsct,
    fun d hd => blockGraphs_arity fuel Ξannot runs hnd hd, ?_⟩
  intro d hd
  obtain ⟨d₀, _, hd_enc⟩ := henc_rel.mem_right hd
  obtain ⟨hwf_Ψ, hwf_ty⟩ := hd_enc.wf
  have henc := hd_enc.2.2.2.2.2
  have hfacts := encode_facts henc
  refine ⟨hwf_Ψ, hwf_ty, fun cl hcl => ?_⟩
  obtain ⟨hcheck, hscope, hcoh⟩ := hclauses d hd cl hcl
  let r := runs d.name cl
  let φ := solve fuel r.flex r.constraints r.nonrecVars
  have hflex : ∀ v ∈ r.flex, FlexName v.name := inference_flex.2.2 hcheck
  obtain ⟨hφ, hsc, hco⟩ := theorem_14 fuel r.flex r.constraints r.nonrecVars hflex hscope hcoh
  have hΨ_eq : d.sizeParams.substBounds φ = d.sizeParams :=
    SizeCtx.substBounds_of_inf φ d.sizeParams hfacts.2.2.2
  have hty_eq : d.ty.substSize φ = d.ty :=
    Ty.substSize_eq_self φ d.ty (fun i hi =>
      hφ.lookup_rigid (hfacts.2.2.1 i (encode_sizeVars_sub henc i hi)))
  have hK : ∀ k ∈ r.calls, sctCallOK (blockGraphs fuel Ξannot runs) d.name d.sizeParams
      (k.ctx.substBounds φ) k.callee (k.args.map (Size.subst φ)) := by
    intro k hk
    exact ⟨callGraph fuel d.sizeParams φ k,
      blockGraphs_mem fuel Ξannot runs hd hcl hk,
      callGraph_conforms fuel d.sizeParams φ k⟩
  have hcl_ty := (inference_sound (Ω := ⟨sig, Ξannot⟩)
    (Ωd := ⟨sig, Ξannot, sctCallOK (blockGraphs fuel Ξannot runs) d.name d.sizeParams⟩)
    (φ := φ) rfl rfl hsigwf hblockwf hφ).2.2 hcheck hco hsc hK
    (fun _ hp => by simp [TermCtx.substSize] at hp)
    (by change KindingC (d.sizeParams.substBounds φ) [] (d.ty.substSize φ) .star
        rw [hΨ_eq, hty_eq]; exact hwf_ty)
  have hΓ_eq : TermCtx.substSize φ [] = [] := rfl
  rw [hΨ_eq, hΓ_eq, hty_eq] at hcl_ty
  exact hcl_ty

/-- **Theorem 15** (Soundness of type-based termination checking, Section 6.5, p. 59): if a mutual
block `Ξ` is accepted by Algorithm 2 with size-annotated declarations `Ξannot` against a
well-formed and semantically valid signature `Σ` in a run-time world `W` with distinct names and
closed clauses, then `Ξannot` is well-typed in System `F_ω^{cop,SCT}` (`BlockTy sig Ξannot`) and is
semantically valid / strongly normalizing in `W` (`SemValid W Ξannot`). -/
theorem theorem_15_proof (ramsey : RamseyPairs) (W sig Ξ Ξannot : List FunDecl)
    (hsigwf : DeclsWf sig)
    (hacc : Algorithm2Accepts sig Ξ Ξannot)
    (hW : ∀ d ∈ sig ++ Ξannot, d ∈ W)
    (hnames : (W.map FunDecl.name).Nodup)
    (hclosed : ∀ d ∈ W, (Tm.lam d.clauses).Closed)
    (hsig : SemValid W sig) :
    BlockTy sig Ξannot ∧ SemValid W Ξannot := by
  have hbt := algorithm2_typing hsigwf hacc
  exact ⟨hbt, theorem_4_proof ramsey W sig Ξannot hW hnames hclosed hbt hsig⟩

end NishtAbel2024V5
