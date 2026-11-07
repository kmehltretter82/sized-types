import Solutions.V5.InfAux

/-! # V5 inference: Theorem 13 — coherent substitutions give typing derivations -/

namespace NishtAbel2024V5

/-- Well-formed signatures. -/
def DeclsWf (D : List FunDecl) : Prop :=
  ∀ g ∈ D, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star

/-- Recorded calls into the block are admitted by the declarative environment. -/
def CallsOK (Ωd : TypingEnv) (φ : FlexSubst) (K : List CallRec) : Prop :=
  ∀ k ∈ K, Ωd.localOK (k.ctx.substBounds φ) k.callee (k.args.map (Size.subst φ))

theorem CallsOK.left {Ωd : TypingEnv} {φ : FlexSubst} {K₁ K₂ : List CallRec}
    (h : CallsOK Ωd φ (K₁ ++ K₂)) : CallsOK Ωd φ K₁ := fun k hk => h k (List.mem_append_left _ hk)

theorem CallsOK.right {Ωd : TypingEnv} {φ : FlexSubst} {K₁ K₂ : List CallRec}
    (h : CallsOK Ωd φ (K₁ ++ K₂)) : CallsOK Ωd φ K₂ :=
  fun k hk => h k (List.mem_append_right _ hk)

/-! ## Calls -/

theorem callBounds_mem {Ψ : SizeCtx} {g : FunDecl} {as : List Size} {k : Nat}
    (hk : k < g.sizeParams.length) (ha : k < as.length) :
    (⟨Ψ, as[k], (g.sizeParams[k]).2.subst (g.sizeParams.dom.zip as), true, false⟩ : SConstr) ∈
      callBounds Ψ g as := by
  unfold callBounds
  apply List.mem_map.mpr
  refine ⟨(g.sizeParams[k], as[k]), ?_, rfl⟩
  rw [List.mem_iff_getElem]
  exact ⟨k, by simp [hk, ha], by simp⟩

/-- The facts about an inferred call `g a⃗` under a coherent substitution. -/
theorem call_facts {φ : FlexSubst} {Ψ : SizeCtx} {Θ : TyCtx} {g : FunDecl} {as : List Nat}
    (hg : SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star)
    (hlen : as.length = g.sizeParams.length) (hsc : ScopeOK φ (callFlex Ψ g as))
    (hcoh : Coherent φ (callBounds Ψ g (as.map fun k => .var k 0))) :
    let bs := (as.map fun k => Size.var k 0).map (Size.subst φ)
    (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0))).substSize φ =
        g.ty.substSize (g.sizeParams.dom.zip bs) ∧
      SizeSubstWf (Ψ.substBounds φ) bs g.sizeParams ∧
      KindingC (Ψ.substBounds φ) Θ.toK (g.ty.substSize (g.sizeParams.dom.zip bs)) .star := by
  intro bs
  obtain ⟨hwf, hk⟩ := hg
  have hdl : g.sizeParams.dom.length = g.sizeParams.length := by simp [SizeCtx.dom]
  have hlen' : (as.map fun k => Size.var k 0).length = g.sizeParams.length := by simp [hlen]
  have hsome : ∀ i ∈ g.sizeParams.dom,
      ((g.sizeParams.dom.zip (as.map fun k => Size.var k 0)).lookup i).isSome :=
    zip_lookup_isSome _ _ (by rw [hdl, hlen'])
  have hcomp : ∀ (σs : List Size), ((g.sizeParams.dom.zip (as.map fun k => Size.var k 0)).map
      fun p => (p.1, p.2.subst φ)) = g.sizeParams.dom.zip ((as.map fun k => Size.var k 0).map
        (Size.subst φ)) := fun _ => zip_map_snd _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [Ty.substSize_comp hk.sizesWf _ φ hsome, hcomp []]
  · refine ⟨by simp [bs, hlen], ?_⟩
    intro k hk' ha
    have hka : k < (as.map fun k => Size.var k 0).length := by simpa [hlen] using hk'
    have hc := hcoh _ (callBounds_mem (Ψ := Ψ) hk' hka)
    simp only [SConstr.Holds, if_true, Bool.false_eq_true, if_false] at hc
    have hbw : SizeWf g.sizeParams (g.sizeParams[k]).2 := hwf.bound_wf _ (List.getElem_mem hk')
    rw [Size.subst_comp _ φ _ (fun i hi => hsome i (SizeWfAt.fvars_dom hbw i hi)), hcomp []] at hc
    simpa [bs] using hc
  · have hσ : ∀ i ∈ g.sizeParams.dom, SizeWf (Ψ.substBounds φ)
        ((Size.var i 0).subst (g.sizeParams.dom.zip bs)) := by
      intro i hi
      obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hi
      have hkl : k < g.sizeParams.length := by simpa [SizeCtx.dom] using hk'
      have hkb : k < bs.length := by simp [bs, hlen, hkl]
      have hlk := lookup_zip_getElem' g.sizeParams.dom bs hwf.dom_nodup (by simp [bs, hdl, hlen]) k
        hk' hkb
      simp only [Size.subst, hlk, Size.shift_zero]
      have hka : k < as.length := by rw [hlen]; exact hkl
      have hmem : as[k] ∈ as := List.getElem_mem hka
      have := hsc.callFlex hlen as[k] hmem
      simpa [bs] using this
    have : KindingC (Ψ.substBounds φ) [] (g.ty.substSize (g.sizeParams.dom.zip bs)) .star :=
      Kinding.substSize hk hσ
    exact this.mono (fun _ h => h) (fun _ _ h => by simp at h)

/-! ## Theorem 13 -/

theorem inferSpine_rigid {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty} (h : InferSpine Ψ Θ qs A Γ Ψ' Θ' C) :
    ∀ i ∈ Ψ'.dom, RigidName i := by
  have hp : ∀ {Ψ Θ p A Γ Ψ' Θ'}, InferPat Ψ Θ p A Γ Ψ' Θ' → ∀ i ∈ Ψ'.dom, RigidName i := by
    intro Ψ Θ p A Γ Ψ' Θ' h
    induction h with
    | var => intro i hi; simp [SizeCtx.dom] at hi
    | unit => intro i hi; simp [SizeCtx.dom] at hi
    | pair _ _ ih₁ ih₂ =>
      intro i hi
      simp only [SizeCtx.dom_append, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ih₁ i hi
      · exact ih₂ i hi
    | cons _ hr _ _ ih =>
      intro i hi
      simp only [SizeCtx.dom_cons, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact hr
      · exact ih i hi
    | pack _ _ ih => exact ih
  induction h with
  | nil => intro i hi; simp [SizeCtx.dom] at hi
  | pat hpat _ ih =>
    intro i hi
    simp only [SizeCtx.dom_append, List.mem_append] at hi
    rcases hi with hi | hi
    · exact hp hpat i hi
    · exact ih i hi
  | proj _ hr _ _ ih =>
    intro i hi
    simp only [SizeCtx.dom_cons, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact hr
    · exact ih i hi
  | inst _ _ ih => exact ih

theorem TermCtxWf.substSize_lookup {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {φ : FlexSubst}
    (h : TermCtxWf Ψ Θ (Γ.substSize φ)) {x : Nat} {A : Ty} (hx : Γ.lookup x = some A) :
    KindingC Ψ Θ.toK (A.substSize φ) .star := by
  have hx' : (Γ.substSize φ).lookup x = some (A.substSize φ) := by
    rw [TermCtx.lookup_substSize, hx]; rfl
  exact h _ (lookup_mem_ctx hx')

theorem TermCtxWf.prepend {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {Γ Γ' : TermCtx}
    (hΓ' : TermCtxWf (Ψ ++ Ψ') (Θ ++ Θ') Γ') (hΓ : TermCtxWf Ψ Θ Γ) :
    TermCtxWf (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hΓ' p hp
  · rw [TyCtx.toK_append]
    exact (hΓ p hp).mono_append

/-- Encoded type arguments are well-kinded after the substitution. -/
theorem encoded_kinding {φ : FlexSubst} {Ψ : SizeCtx} {Θ : TyCtx} {G G' : Ty} {κ : Kind}
    {ΨG : SizeCtx} (hk : EKinding Θ.toK [] G κ)
    (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G') (hsc : ScopeOK φ (encFlex Ψ ΨG)) :
    KindingC (Ψ.substBounds φ) Θ.toK (G'.substSize φ) κ := by
  obtain ⟨herase, hsw, _, _⟩ := encode_facts henc
  refine kinding_of_erase hk ?_ (hsw.substSize hsc.encFlex)
  rw [Ty.eraseSz_substSize, herase]

/-- **Theorem 13** (soundness of coherent substitutions): a coherent, well-scoped flexible
substitution turns inference derivations into declarative typing derivations, provided the
recorded calls are admitted. -/
theorem inference_sound {Ω : InfEnv} {Ωd : TypingEnv} (hsig : Ωd.sig = Ω.sig)
    (hblock : Ωd.block = Ω.block) (hsigwf : DeclsWf Ω.sig) (hblockwf : DeclsWf Ω.block)
    {φ : FlexSubst} (hφ : FlexDom φ) :
    (∀ {Ψ Θ Γ t A Φ C T K}, InferTm Ω Ψ Θ Γ t A Φ C T K →
      Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star ∧
        ExprTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) t (A.substSize φ)) ∧
    (∀ {Ψ Θ Γ A t Φ C T K}, CheckTm Ω Ψ Θ Γ A t Φ C T K →
      Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star →
        ExprTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) t (A.substSize φ)) ∧
    (∀ {Ψ Θ Γ A cl Φ C T K}, CheckClause Ω Ψ Θ Γ A cl Φ C T K →
      Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star →
        ClauseTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) cl (A.substSize φ)) := by
  let P₁ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (t : Tm) (A : Ty) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec) (_ : InferTm Ω Ψ Θ Γ t A Φ C T K) =>
    Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star ∧
        ExprTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) t (A.substSize φ)
  let P₂ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (t : Tm) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec) (_ : CheckTm Ω Ψ Θ Γ A t Φ C T K) =>
    Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star →
        ExprTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) t (A.substSize φ)
  let P₃ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (D : List Clause)
      (Φ : List FlexVar) (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckClauses Ω Ψ Θ Γ A D Φ C T K) =>
    Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star →
        ∀ cl ∈ D, ClauseTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) cl (A.substSize φ)
  let P₄ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (cl : Clause) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckClause Ω Ψ Θ Γ A cl Φ C T K) =>
    Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star →
        ClauseTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) cl (A.substSize φ)
  have sVar : ∀ {Ψ Θ Γ x A} (hx : Γ.lookup x = some A), P₁ Ψ Θ Γ (.var x) A [] [] [] []
      (.var hx) := by
    intro Ψ Θ Γ x A hx _ _ _ hΓ
    refine ⟨hΓ.substSize_lookup hx, .var ?_⟩
    rw [TermCtx.lookup_substSize, hx]; rfl
  have sApp : ∀ {Ψ Θ Γ r s A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (hr : InferTm Ω Ψ Θ Γ r (.arr A B) Φ₁ C₁ T₁ K₁) (hs : CheckTm Ω Ψ Θ Γ A s Φ₂ C₂ T₂ K₂),
      P₁ Ψ Θ Γ r (.arr A B) Φ₁ C₁ T₁ K₁ hr → P₂ Ψ Θ Γ A s Φ₂ C₂ T₂ K₂ hs →
      P₁ Ψ Θ Γ (.app r (.term s)) B (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂)
        (.app hr hs) := by
    intro Ψ Θ Γ r s A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂ _ _ ihr ihs hcoh hsc hK hΓ
    obtain ⟨hkAB, hr⟩ := ihr hcoh.left hsc.left hK.left hΓ
    simp only [Ty.substSize] at hkAB hr
    obtain ⟨_, hA, hB⟩ := Kinding.inv_arr hkAB
    rw [(TyCtx.toK_allMix Θ).inv, BCtx.inv_nil] at hA
    exact ⟨hB, .app hr (ihs hcoh.right hsc.right hK.right hΓ hA)⟩
  have sProj : ∀ {Ψ Θ Γ r a R d j Rd Φ C T K} (hr : InferTm Ω Ψ Θ Γ r (.nu a R) Φ C T K)
      (hd : R[d]? = some Rd) (hj : FlexName j),
      P₁ Ψ Θ Γ r (.nu a R) Φ C T K hr →
      P₁ Ψ Θ Γ (.app r (.proj d)) (Rd.substTy 0 (.nu (.var j 0) R))
        (⟨j, .neg, Ψ⟩ :: Φ) (⟨Ψ, .var j 0, a, true, true⟩ :: C)
        ((if Rd.hasBVar 0 then [] else [j]) ++ T) K (.proj hr hd hj) := by
    intro Ψ Θ Γ r a R d j Rd Φ C T K _ hd _ ihr hcoh hsc hK hΓ
    obtain ⟨hkR, hr⟩ := ihr hcoh.tail hsc.tail hK hΓ
    simp only [Ty.substSize] at hkR hr
    have hhead : SizeLt (Ψ.substBounds φ) ((Size.var j 0).subst φ) (a.subst φ).up := by
      simpa [SConstr.Holds] using hcoh.head
    have hd' := Ty.substSizeList_getElem?_some (σ := φ) hd
    have hkRd := hkR.unfold_nu (TyCtx.toK_allMix Θ) hd' hhead.wf.1
    rw [Ty.substSize_substTy]
    exact ⟨hkRd, .proj hr hd' hhead⟩
  have sInst : ∀ {Ψ Θ Γ r κ B G G' ΨG Φ C T K} (hr : InferTm Ω Ψ Θ Γ r (.allT κ B) Φ C T K)
      (hG : Unsized G) (hkG : EKinding Θ.toK [] G κ)
      (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G'),
      P₁ Ψ Θ Γ r (.allT κ B) Φ C T K hr →
      P₁ Ψ Θ Γ (.app r .inst) (B.substTy 0 G') (encFlex Ψ ΨG ++ Φ) C T K
        (.inst hr hG hkG henc) := by
    intro Ψ Θ Γ r κ B G G' ΨG Φ C T K _ _ hkG henc ihr hcoh hsc hK hΓ
    obtain ⟨hkAll, hr⟩ := ihr hcoh hsc.right hK hΓ
    simp only [Ty.substSize] at hkAll hr
    have hkG' := encoded_kinding hkG henc hsc.left
    have hkB := Kinding.open_ty (Kinding.inv_allT hkAll).2 (TyCtx.toK_allMix Θ) hkG'
    rw [Ty.substSize_substTy]
    exact ⟨hkB, .instT hr hkG'⟩
  have sGlobal : ∀ {Ψ Θ Γ g as} (hg : g ∈ Ω.sig) (hlen : as.length = g.sizeParams.length)
      (hflex : ∀ k ∈ as, FlexName k),
      P₁ Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) [] []
        (.global hg hlen hflex) := by
    intro Ψ Θ Γ g as hg hlen _ hcoh hsc _ _
    obtain ⟨heq, hsub, hk⟩ := call_facts (Θ := Θ) (hsigwf g hg) hlen hsc hcoh
    rw [heq]
    exact ⟨hk, .globalFun (hsig ▸ hg) (hsigwf g hg).1 (hsigwf g hg).2 hsub hk⟩
  have sLocal : ∀ {Ψ Θ Γ g as} (hg : g ∈ Ω.block) (hlen : as.length = g.sizeParams.length)
      (hflex : ∀ k ∈ as, FlexName k),
      P₁ Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) []
        [⟨Ψ, g.name, as.map fun k => .var k 0⟩] (.local hg hlen hflex) := by
    intro Ψ Θ Γ g as hg hlen _ hcoh hsc hK _
    obtain ⟨heq, hsub, hk⟩ := call_facts (Θ := Θ) (hblockwf g hg) hlen hsc hcoh
    have hloc := hK ⟨Ψ, g.name, as.map fun k => .var k 0⟩ (by simp)
    rw [heq]
    exact ⟨hk, .localFun (hblock ▸ hg) (hblockwf g hg).1 (hblockwf g hg).2 hsub hk hloc⟩
  have sUnit : ∀ {Ψ Θ Γ}, P₂ Ψ Θ Γ .unit .unit [] [] [] [] .unit := by
    intro Ψ Θ Γ _ _ _ _ _
    exact .unit _ _ _
  have sPair : ∀ {Ψ Θ Γ t u A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (ht : CheckTm Ω Ψ Θ Γ A t Φ₁ C₁ T₁ K₁) (hu : CheckTm Ω Ψ Θ Γ B u Φ₂ C₂ T₂ K₂),
      P₂ Ψ Θ Γ A t Φ₁ C₁ T₁ K₁ ht → P₂ Ψ Θ Γ B u Φ₂ C₂ T₂ K₂ hu →
      P₂ Ψ Θ Γ (.prod A B) (.pair t u) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂)
        (.pair ht hu) := by
    intro Ψ Θ Γ t u A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂ _ _ iht ihu hcoh hsc hK hΓ hk
    simp only [Ty.substSize] at hk ⊢
    obtain ⟨_, hA, hB⟩ := Kinding.inv_prod hk
    exact .pair (iht hcoh.left hsc.left hK.left hΓ hA) (ihu hcoh.right hsc.right hK.right hΓ hB)
  have sCons : ∀ {Ψ Θ Γ c j t a S Sc Φ C T K} (hc : S[c]? = some Sc) (hj : FlexName j)
      (ht : CheckTm Ω Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t Φ C T K),
      P₂ Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t Φ C T K ht →
      P₂ Ψ Θ Γ (.mu a S) (.cons c t) (⟨j, .pos, Ψ⟩ :: Φ)
        (⟨Ψ, .var j 0, a, true, true⟩ :: C) ((if Sc.hasBVar 0 then [] else [j]) ++ T) K
        (.cons hc hj ht) := by
    intro Ψ Θ Γ c j t a S Sc Φ C T K hc _ _ iht hcoh hsc hK hΓ hk
    simp only [Ty.substSize] at hk ⊢
    have hhead : SizeLt (Ψ.substBounds φ) ((Size.var j 0).subst φ) (a.subst φ).up := by
      simpa [SConstr.Holds] using hcoh.head
    have hc' := Ty.substSizeList_getElem?_some (σ := φ) hc
    have hkSc := hk.unfold_mu (TyCtx.toK_allMix Θ) hc' hhead.wf.1
    have hkSc' : KindingC (Ψ.substBounds φ) Θ.toK
        ((Sc.substTy 0 (.mu (.var j 0) S)).substSize φ) .star := by
      simpa [Ty.substSize_substTy, Ty.substSize] using hkSc
    have ht := iht hcoh.tail hsc.tail hK hΓ hkSc'
    rw [Ty.substSize_substTy] at ht
    exact .cons hc' hhead hk (by simpa [Ty.substSize] using ht)
  have sPack : ∀ {Ψ Θ Γ t κ B G G' ΨG Φ C T K} (hG : Unsized G) (hkG : EKinding Θ.toK [] G κ)
      (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G')
      (ht : CheckTm Ω Ψ Θ Γ (B.substTy 0 G') t Φ C T K),
      P₂ Ψ Θ Γ (B.substTy 0 G') t Φ C T K ht →
      P₂ Ψ Θ Γ (.exT κ B) (.pack t) (encFlex Ψ ΨG ++ Φ) C T K (.pack hG hkG henc ht) := by
    intro Ψ Θ Γ t κ B G G' ΨG Φ C T K _ hkG henc _ iht hcoh hsc hK hΓ hk
    simp only [Ty.substSize] at hk ⊢
    have hkG' := encoded_kinding hkG henc hsc.left
    have hkB := Kinding.open_ty (Kinding.inv_exT hk).2 (TyCtx.toK_allMix Θ) hkG'
    rw [← Ty.substSize_substTy] at hkB
    have ht := iht hcoh hsc.right hK hΓ hkB
    rw [Ty.substSize_substTy] at ht
    exact .packT hk hkG' ht
  have sLam : ∀ {Ψ Θ Γ A D Φ C T K} (hD : CheckClauses Ω Ψ Θ Γ A D Φ C T K),
      P₃ Ψ Θ Γ A D Φ C T K hD → P₂ Ψ Θ Γ A (.lam D) Φ C T K (.lam hD) := by
    intro Ψ Θ Γ A D Φ C T K _ ih hcoh hsc hK hΓ hk
    exact .lam hk (ih hcoh hsc hK hΓ hk)
  have sSub : ∀ {Ψ Θ Γ r A B Φ C₁ C₂ T K} (hr : InferTm Ω Ψ Θ Γ r A Φ C₁ T K)
      (hcmp : Compare Ψ Θ.toK A B .star C₂),
      P₁ Ψ Θ Γ r A Φ C₁ T K hr → P₂ Ψ Θ Γ B r Φ (C₁ ++ C₂) T K (.sub hr hcmp) := by
    intro Ψ Θ Γ r A B Φ C₁ C₂ T K _ hcmp ihr hcoh hsc hK hΓ hkB
    obtain ⟨hkA, hr⟩ := ihr hcoh.left hsc hK hΓ
    have hsub := compare_sound hcmp hcoh.right hkA.sizesWf hkB.sizesWf
    exact .sub hr hsub hkB
  have sNil : ∀ {Ψ Θ Γ A}, P₃ Ψ Θ Γ A [] [] [] [] [] .nil := by
    intro Ψ Θ Γ A _ _ _ _ _ cl hcl
    simp at hcl
  have sConsCl : ∀ {Ψ Θ Γ A cl D Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (hcl : CheckClause Ω Ψ Θ Γ A cl Φ₁ C₁ T₁ K₁)
      (hD : CheckClauses Ω Ψ Θ Γ A D Φ₂ C₂ T₂ K₂),
      P₄ Ψ Θ Γ A cl Φ₁ C₁ T₁ K₁ hcl → P₃ Ψ Θ Γ A D Φ₂ C₂ T₂ K₂ hD →
      P₃ Ψ Θ Γ A (cl :: D) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂) (.cons hcl hD) := by
    intro Ψ Θ Γ A cl D Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂ _ _ ih₁ ih₂ hcoh hsc hK hΓ hk cl' hcl'
    rcases List.mem_cons.mp hcl' with rfl | hcl'
    · exact ih₁ hcoh.left hsc.left hK.left hΓ hk
    · exact ih₂ hcoh.right hsc.right hK.right hΓ hk cl' hcl'
  have sClause : ∀ {Ψ Ψ' Θ Θ' Γ Γ' A C qs t Φ Cs T K}
      (hsp : InferSpine Ψ Θ qs A Γ' Ψ' Θ' C)
      (ht : CheckTm Ω (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) C t Φ Cs T K),
      P₂ (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) C t Φ Cs T K ht →
      P₄ Ψ Θ Γ A (.mk qs t) Φ Cs T K (.mk hsp ht) := by
    intro Ψ Ψ' Θ Θ' Γ Γ' A C qs t Φ Cs T K hsp _ iht hcoh hsc hK hΓ hkA
    have hsp' := inferSpine_subst hφ hsp
    obtain ⟨hΓ', hkC⟩ := spineTy_kinding hsp' hkA
    have ht := iht hcoh hsc hK
      (by simpa [SizeCtx.substBounds_append, TermCtx.substSize_append] using hΓ'.prepend hΓ)
      (by simpa [SizeCtx.substBounds_append] using hkC)
    simp only [SizeCtx.substBounds_append, TermCtx.substSize_append] at ht
    exact .mk hsp' ht
  exact ⟨fun h => @InferTm.rec Ω P₁ P₂ P₃ P₄ sVar sApp sProj sInst sGlobal sLocal sUnit sPair
      sCons sPack sLam sSub sNil sConsCl sClause _ _ _ _ _ _ _ _ _ h,
    fun h => @CheckTm.rec Ω P₁ P₂ P₃ P₄ sVar sApp sProj sInst sGlobal sLocal sUnit sPair
      sCons sPack sLam sSub sNil sConsCl sClause _ _ _ _ _ _ _ _ _ h,
    fun h => @CheckClause.rec Ω P₁ P₂ P₃ P₄ sVar sApp sProj sInst sGlobal sLocal sUnit sPair
      sCons sPack sLam sSub sNil sConsCl sClause _ _ _ _ _ _ _ _ _ h⟩

end NishtAbel2024V5
