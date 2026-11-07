import Solutions.V5.FundAux

/-! # V5: the fundamental lemma (Theorem 3) -/

namespace NishtAbel2024V5

open NishtAbel2024V2 (InvGraph ConformsToGraph)

/-! ## Callee valuations -/

theorem SizeCtxWf.nodup {Ψ : SizeCtx} (h : SizeCtxWf Ψ) : Ψ.dom.Nodup := by
  induction h with
  | nil => simp [SizeCtx.dom]
  | @snoc Ψ i a _ hi _ ih =>
    simp only [SizeCtx.dom, List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro x hx y hy
    simp at hy; subst hy
    exact fun h => hi (h ▸ hx)

theorem SizeCtxWf.bounds {Ψ : SizeCtx} (h : SizeCtxWf Ψ) : CtxBoundsWf Ψ := by
  induction h with
  | nil => intro p hp; simp at hp
  | snoc _ _ ha ih => exact ih.extend ha

theorem lookup_zip_getElem : ∀ (l : List Nat) (as : List Size), l.Nodup → l.length = as.length →
    ∀ k (hk : k < l.length) (ha : k < as.length), (l.zip as).lookup (l[k]'hk) = some (as[k]'ha)
  | [], _, _, _, k, hk, _ => by simp at hk
  | _ :: _, [], _, h, _, _, _ => by simp at h
  | x :: l, a :: as, hnd, hlen, 0, _, _ => by simp
  | x :: l, a :: as, hnd, hlen, k + 1, hk, ha => by
    have hk' : k < l.length := by simp at hk; omega
    have ha' : k < as.length := by simp at ha; omega
    have hne : l[k]'hk' ≠ x := by
      intro h
      have := (List.nodup_cons.mp hnd).1
      exact this (h ▸ List.getElem_mem hk')
    have hb : (l[k]'hk' == x) = false := beq_eq_false_iff_ne.mpr hne
    have := lookup_zip_getElem l as (List.nodup_cons.mp hnd).2 (by simpa using hlen) k hk' ha'
    simp only [List.zip_cons_cons, List.getElem_cons_succ, List.lookup_cons, hb]
    exact this

theorem lookup_mem_size {L : List (Nat × Size)} {i : Nat} {b : Size} (h : L.lookup i = some b) :
    (i, b) ∈ L := by
  induction L with
  | nil => simp at h
  | cons q r ih =>
    obtain ⟨y, c⟩ := q
    rw [lookup_size_cons] at h
    by_cases hiy : i = y
    · simp [hiy] at h; subst h; subst hiy; simp
    · simp [hiy] at h; exact List.mem_cons_of_mem _ (ih h)

theorem lookup_zip_mem {l : List Nat} {as : List Size} {i : Nat} {b : Size}
    (h : (l.zip as).lookup i = some b) : b ∈ as :=
  (List.of_mem_zip (lookup_mem_size h)).2

/-- Size arguments of a well-formed call give a valid callee valuation. -/
theorem callee_val {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {as : List Size}
    {Ψg : SizeCtx} (hwf : SizeCtxWf Ψg) (hsub : SizeSubstWf Ψ as Ψg) :
    LCSubst (Ψg.dom.zip as) ∧ ValidVal Ψg (substVal ρ (Ψg.dom.zip as)) ∧
      Ψg.map (fun p => substVal ρ (Ψg.dom.zip as) p.1) = as.map (sizeVal ρ SzEnv.zero) := by
  obtain ⟨hlen, hlt⟩ := hsub
  have hnd := hwf.nodup
  have hdlen : Ψg.dom.length = as.length := by simp [SizeCtx.dom, hlen]
  have hlc : LCSubst (Ψg.dom.zip as) := by
    intro i b hb
    have hbm := lookup_zip_mem hb
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hbm
    have hkΨ : k < Ψg.length := by rw [← hlen]; exact hk
    exact Size.LC.of_wf (hlt k hkΨ hk).wf.1
  have hval : ∀ k (hk : k < Ψg.length) (ha : k < as.length),
      substVal ρ (Ψg.dom.zip as) (Ψg[k]).1 = sizeVal ρ SzEnv.zero as[k] := by
    intro k hk ha
    have hkd : k < Ψg.dom.length := by simpa [SizeCtx.dom] using hk
    have := lookup_zip_getElem Ψg.dom as hnd hdlen k hkd ha
    have hdk : Ψg.dom[k]'hkd = (Ψg[k]).1 := by simp [SizeCtx.dom]
    rw [hdk] at this
    simp only [substVal, this]
  refine ⟨hlc, ?_, ?_⟩
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    have ha : k < as.length := by rw [hlen]; exact hk
    rw [hval k hk ha, ← sizeVal_subst hlc]
    exact sizeLt_sound hv (hlt k hk ha)
  · apply List.ext_getElem (by simp [hlen])
    intro k h1 h2
    simp only [List.getElem_map]
    exact hval k (by simpa using h1) (by simpa using h2)

/-! ## The guard on local calls -/

/-- Invariants of size contexts and valuations that are stable under extension. -/
def InvMono (Inv : SizeCtx → SizeVal → Prop) : Prop :=
  ∀ Ψ Ψ' ρ ρ', Inv Ψ ρ → (∀ i ∈ Ψ.dom, i ∈ Ψ'.dom) → (∀ i ∈ Ψ.dom, ρ' i = ρ i) → Inv Ψ' ρ'

/-- Calls into the current block admitted by `localOK` are semantically safe, in every valid
context satisfying the invariant `Inv`. -/
def GuardOK (W : World) (Ω : TypingEnv) (Inv : SizeCtx → SizeVal → Prop) : Prop :=
  ∀ (Ψ : SizeCtx) (ρ : SizeVal) (g : FunDecl) (as : List Size), g ∈ Ω.block →
    Ω.localOK Ψ g.name as → ValidVal Ψ ρ → Inv Ψ ρ →
    ∀ ρg : SizeVal, ValidVal g.sizeParams ρg →
      g.sizeParams.map (fun p => ρg p.1) = as.map (sizeVal ρ SzEnv.zero) →
      Tm.fn g.name ∈ interpT W ρg TEnv.empty g.ty SzEnv.zero Env.empty

/-- Semantic soundness of a clause under an outer substitution. -/
def ClauseSound (W : World) (c : SCtx) (A : Ty) (σ : TmSubst) : Clause → Prop
  | .mk qs t => ∀ es σm c' C', SemSpine W c A es c' C' → matchSpine qs es = .yes σm →
      Tm.appSpine ((t.subst (σ.filter (fun p => decide (p.1 ∉ spineVars qs)))).subst σm)
        (es.drop qs.length) ∈ c'.den W C'

/-- Hypotheses shared by every case of the fundamental lemma. -/
structure FundEnv (W : World) (Ω : TypingEnv) (Inv : SizeCtx → SizeVal → Prop) : Prop where
  closed : WorldClosed W
  sig : SemValid W Ω.sig
  guard : GuardOK W Ω Inv
  mono : InvMono Inv

/-- Invariants of a context in which a term is interpreted. -/
structure CtxOK (W : World) (Inv : SizeCtx → SizeVal → Prop) (Ψ : SizeCtx) (Θ : TyCtx)
    (Γ : TermCtx) (ρ : SizeVal) (θ : TEnv) (σ : TmSubst) : Prop where
  val : ValidVal Ψ ρ
  bounds : CtxBoundsWf Ψ
  tenv : TEnvOK W Θ θ
  types : TermCtxWf Ψ Θ Γ
  sem : SemCtx W ρ θ Γ σ
  inv : Inv Ψ ρ

theorem lookup_first {Γ : TermCtx} {y : Nat} {B : Ty} (hm : (y, B) ∈ Γ) :
    ∃ B', Γ.lookup y = some B' := by
  induction Γ with
  | nil => simp at hm
  | cons q Γ ih =>
    obtain ⟨z, C⟩ := q
    rw [List.lookup_cons]
    by_cases hyz : y = z
    · subst hyz; exact ⟨C, by simp⟩
    · have : (y == z) = false := beq_eq_false_iff_ne.mpr hyz
      simp only [this]
      rcases List.mem_cons.mp hm with hm | hm
      · simp at hm; exact absurd hm.1 hyz
      · exact ih hm

/-- A function type closed in type variables does not depend on the type environment. -/
theorem interp_fun_ty {W : World} {g : FunDecl} (hcl : KindingC g.sizeParams [] g.ty .star)
    (ρ : SizeVal) (θ : TEnv) :
    interpT W ρ θ g.ty SzEnv.zero Env.empty = interpT W ρ TEnv.empty g.ty SzEnv.zero Env.empty :=
  interp_agree (hcl.tyWf) ρ ρ θ TEnv.empty _ _ _ _ (fun _ _ => rfl)
    (fun X hX => by simp [KCtx.dom] at hX) (fun _ _ => rfl) (fun _ _ => rfl) _

theorem TEnvOK.trel {W : World} {Θ : TyCtx} {θ : TEnv} (h : TEnvOK W Θ θ) : TRel W Θ.toK θ θ := h

theorem BRel.nil (W : World) (η η' : Env) : BRel W [] η η' := fun _ _ _ hk => by simp at hk

/-- The value of a well-kinded type is good. -/
theorem good_of_kinding {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Θ : TyCtx} {T : Ty}
    {κ : Kind} (hT : KindingC Ψ Θ.toK T κ) (ρ : SizeVal) {θ : TEnv} (hθ : TEnvOK W Θ θ) :
    Good W κ (interp W ρ θ T κ.erase SzEnv.zero Env.empty) :=
  (kinding_sound hW hT ρ θ θ SzEnv.zero Env.empty Env.empty hθ (BRel.nil W _ _)).1

/-- Instantiating a type binder with the denotation of a type. -/
theorem interp_inst_ty {W : World} {Ψ : SizeCtx} {Θ : TyCtx} {κ : Kind} {B T : Ty}
    (hB : Kinding Ψ Θ.toK [(.mix, κ)] 0 B .star) (hT : KindingC Ψ Θ.toK T κ) (ρ : SizeVal)
    (θ : TEnv) :
    interpT W ρ θ (B.substTy 0 T) SzEnv.zero Env.empty =
      interpT W ρ θ B SzEnv.zero
        (Env.cons (PSem.ofSem κ.erase (interp W ρ θ T κ.erase SzEnv.zero Env.empty)) Env.empty) := by
  have hTw : TyWf Ψ (Θ.toK.dom) 0 0 T := hT.tyWf
  unfold interpT
  rw [interp_openTy (envFree_of_closed hTw ρ θ)]
  apply interp_agree_kinded hB ρ θ θ SzEnv.zero
  · intros; rfl
  · intro k π κ' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      simp [tyVal]
    | succ k => simp at hk

/-- The fundamental lemma: expressions and clauses. -/
theorem fundamental {W : World} {Ω : TypingEnv} {Inv : SizeCtx → SizeVal → Prop}
    (E : FundEnv W Ω Inv) {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {t : Tm} {A : Ty}
    (h : ExprTy Ω Ψ Θ Γ t A) :
    ∀ ρ θ σ, CtxOK W Inv Ψ Θ Γ ρ θ σ →
      KindingC Ψ Θ.toK A .star ∧ t.subst σ ∈ interpT W ρ θ A SzEnv.zero Env.empty := by
  have hW := E.closed
  refine ExprTy.rec
    (motive_1 := fun Ψ Θ Γ t A _ => ∀ ρ θ σ, CtxOK W Inv Ψ Θ Γ ρ θ σ →
      KindingC Ψ Θ.toK A .star ∧ t.subst σ ∈ interpT W ρ θ A SzEnv.zero Env.empty)
    (motive_2 := fun Ψ Θ Γ cl A _ => ∀ ρ θ σ, CtxOK W Inv Ψ Θ Γ ρ θ σ →
      KindingC Ψ Θ.toK A .star → ClauseSound W ⟨Ψ, Θ, ρ, θ⟩ A σ cl)
    ?c_var ?c_unit ?c_pair ?c_cons ?c_app ?c_proj ?c_instT ?c_instS ?c_packT ?c_packS ?c_lam
    ?c_glob ?c_loc ?c_sub ?c_clause h
  case c_var =>
    intro Ψ Θ Γ x A hx ρ θ σ hok
    obtain ⟨v, hv, hmem⟩ := hok.sem.1 x A hx
    refine ⟨hok.types _ (lookup_mem_ctx hx), ?_⟩
    simp only [Tm.subst, hv, Option.getD_some]
    exact hmem
  case c_unit =>
    intro Ψ Θ Γ ρ θ σ hok
    exact ⟨.unit, ⟨⟨rfl, SN.unit W⟩, fun v hv _ => steps_unit_inv hv⟩⟩
  case c_pair =>
    intro Ψ Θ Γ t u A B _ _ ih₁ ih₂ ρ θ σ hok
    obtain ⟨hA, ht⟩ := ih₁ ρ θ σ hok
    obtain ⟨hB, hu⟩ := ih₂ ρ θ σ hok
    have cA := interp_cand_closed hW hA ρ hok.tenv
    have cB := interp_cand_closed hW hB ρ hok.tenv
    refine ⟨.prod hA hB, ?_⟩
    unfold interpT
    rw [interp_prod_star]
    refine ⟨⟨?_, SN.pair (cA.sn _ ht).2 (cB.sn _ hu).2⟩, ?_⟩
    · simp only [Tm.subst]
      unfold Tm.Closed; simp only [Tm.fv]
      rw [(cA.sn _ ht).1, (cB.sn _ hu).1]; rfl
    · intro v hv _
      simp only [Tm.subst] at hv
      obtain ⟨t', u', rfl, h1, h2⟩ := steps_pair_inv hv
      exact ⟨t', u', rfl, cA.red_steps ht h1, cB.red_steps hu h2⟩
  case c_cons =>
    intro Ψ Θ Γ c t a b S Sc hc hb hwf _ ih ρ θ σ hok
    obtain ⟨_, ht⟩ := ih ρ θ σ hok
    have hcl : c < S.length := (List.getElem?_eq_some_iff.mp hc).1
    have hScEq : S[c] = Sc := (List.getElem?_eq_some_iff.mp hc).2
    have hbwf : SizeWf Ψ b := hb.wf.1
    have hwfb := hwf.mu_size hbwf
    obtain ⟨_, π, _, _, hS⟩ := Kinding.inv_mu hwf
    have hwfbw : TyWf Ψ (Θ.toK.dom) 0 0 (.mu b S) := hwfb.tyWf
    unfold interpT at ht
    rw [← hScEq, interp_unfold_mu hcl hwfbw] at ht
    set F := fun c (𝒳 : Set Tm) =>
      interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty) with hF
    have hFc : ∀ β, Cand W (F c (MuSet W F β)) := fun β =>
      functor_cand hW hok.tenv.trel hS c hcl _ (muSet_cand hW F β)
    refine ⟨hwf, ?_⟩
    simp only [Tm.subst]
    unfold interpT
    rw [interp_mu_star, MuSet_eq]
    have hsn := (hFc _).sn _ ht
    refine ⟨⟨by unfold Tm.Closed; simp only [Tm.fv]; exact hsn.1, SN.cons hsn.2⟩, ?_⟩
    intro v hv _
    obtain ⟨t'', rfl, hst⟩ := steps_cons_inv hv
    have ht'' := (hFc _).red_steps ht hst
    have hlt := sizeLt_sound hok.val hb
    rcases lt_up_cases ρ SzEnv.zero a hlt with hlt' | hΩ
    · exact ⟨c, t'', sizeVal ρ SzEnv.zero b, hlt', rfl, ht''⟩
    · by_cases hba : sizeVal ρ SzEnv.zero b < sizeVal ρ SzEnv.zero a
      · exact ⟨c, t'', sizeVal ρ SzEnv.zero b, hba, rfl, ht''⟩
      · have hbΩ : Omega ≤ sizeVal ρ SzEnv.zero b := hΩ.trans (not_lt.mp hba)
        rw [muSet_ge_omega W F hbΩ] at ht''
        obtain ⟨β, hβ, hβm⟩ := muSet_omega_closed ht''
        exact ⟨c, t'', β, lt_of_lt_of_le hβ hΩ, rfl, hβm⟩
  case c_app =>
    intro Ψ Θ Γ r s A B _ _ ih₁ ih₂ ρ θ σ hok
    obtain ⟨hAB, hr⟩ := ih₁ ρ θ σ hok
    obtain ⟨_, hs⟩ := ih₂ ρ θ σ hok
    refine ⟨(Kinding.inv_arr hAB).2.2, ?_⟩
    simp only [Tm.subst, Elim.subst]
    unfold interpT at hr
    rw [interp_arr_star] at hr
    exact hr.2 _ hs
  case c_proj =>
    intro Ψ Θ Γ r a b R d Rd _ hd hb ih ρ θ σ hok
    obtain ⟨hwf, hr⟩ := ih ρ θ σ hok
    have hdl : d < R.length := (List.getElem?_eq_some_iff.mp hd).1
    have hRdEq : R[d] = Rd := (List.getElem?_eq_some_iff.mp hd).2
    have hbwf : SizeWf Ψ b := hb.wf.1
    have hwfb := hwf.nu_size hbwf
    refine ⟨hwf.unfold_nu (TyCtx.toK_allMix Θ) hd hbwf, ?_⟩
    simp only [Tm.subst, Elim.subst]
    unfold interpT
    rw [← hRdEq, interp_unfold_nu hdl hwfb.tyWf]
    unfold interpT at hr
    rw [interp_nu_star] at hr
    have hlt := sizeLt_sound hok.val hb
    rcases lt_up_cases ρ SzEnv.zero a hlt with hlt' | hΩ
    · rw [NuSet_eq] at hr
      exact hr.2 _ hlt' d hdl
    · by_cases hba : sizeVal ρ SzEnv.zero b < sizeVal ρ SzEnv.zero a
      · rw [NuSet_eq] at hr
        exact hr.2 _ hba d hdl
      · have hbΩ : Omega ≤ sizeVal ρ SzEnv.zero b := hΩ.trans (not_lt.mp hba)
        rw [nuSet_ge_omega W _ _ hΩ] at hr
        rw [nuSet_ge_omega W _ _ hbΩ]
        exact nuSet_omega_proj hr hdl
  case c_instT =>
    intro Ψ Θ Γ r κ B T _ hT ih ρ θ σ hok
    obtain ⟨hwf, hr⟩ := ih ρ θ σ hok
    have hB := (Kinding.inv_allT hwf).2
    refine ⟨Kinding.open_ty hB (TyCtx.toK_allMix Θ) hT, ?_⟩
    simp only [Tm.subst, Elim.subst]
    rw [interp_inst_ty hB hT]
    unfold interpT at hr
    rw [interp_allT_star] at hr
    exact hr.2 _ (good_of_kinding hW hT ρ hok.tenv)
  case c_instS =>
    intro Ψ Θ Γ r a b B _ hb ih ρ θ σ hok
    obtain ⟨hwf, hr⟩ := ih ρ θ σ hok
    obtain ⟨_, _, hB⟩ := Kinding.inv_allS hwf
    have hlt := sizeLt_sound hok.val hb
    have hbwf := hb.wf.1
    refine ⟨Kinding.open_sz hB hbwf, ?_⟩
    simp only [Tm.subst, Elim.subst]
    unfold interpT
    rw [interp_openSz0 W ρ θ (Size.LC.of_wf hbwf)]
    unfold interpT at hr
    rw [interp_allS_star] at hr
    exact hr.2 _ hlt
  case c_packT =>
    intro Ψ Θ Γ t κ B T hwf hT _ ih ρ θ σ hok
    obtain ⟨hwfBT, ht⟩ := ih ρ θ σ hok
    have hB := (Kinding.inv_exT hwf).2
    have hY := good_of_kinding hW hT ρ hok.tenv
    have hcB := interp_cand_closed hW hwfBT ρ hok.tenv
    have hsn := hcB.sn _ ht
    rw [interp_inst_ty hB hT] at ht
    have hcB' : Cand W (interpT W ρ θ B SzEnv.zero (Env.cons (PSem.ofSem κ.erase
        (interp W ρ θ T κ.erase SzEnv.zero Env.empty)) Env.empty)) := by
      rw [← interp_inst_ty hB hT]; exact hcB
    refine ⟨hwf, ?_⟩
    simp only [Tm.subst]
    unfold interpT
    rw [interp_exT_star]
    refine ⟨⟨by unfold Tm.Closed; simp only [Tm.fv]; exact hsn.1, SN.pack hsn.2⟩, ?_⟩
    intro v hv _
    obtain ⟨t'', rfl, hst⟩ := steps_pack_inv hv
    exact ⟨t'', _, rfl, hY, hcB'.red_steps ht hst⟩
  case c_packS =>
    intro Ψ Θ Γ t a b B hwf hb _ ih ρ θ σ hok
    obtain ⟨hwfBb, ht⟩ := ih ρ θ σ hok
    have hlt := sizeLt_sound hok.val hb
    have hbwf := hb.wf.1
    have hcB := interp_cand_closed hW hwfBb ρ hok.tenv
    have hsn := hcB.sn _ ht
    have hcB' : Cand W (interpT W ρ θ B (SzEnv.cons (sizeVal ρ SzEnv.zero b) SzEnv.zero)
        Env.empty) := by
      unfold interpT
      rw [← interp_openSz0 W ρ θ (Size.LC.of_wf hbwf)]
      exact hcB
    unfold interpT at ht
    rw [interp_openSz0 W ρ θ (Size.LC.of_wf hbwf)] at ht
    refine ⟨hwf, ?_⟩
    simp only [Tm.subst]
    unfold interpT
    rw [interp_exS_star]
    refine ⟨⟨by unfold Tm.Closed; simp only [Tm.fv]; exact hsn.1, SN.pack hsn.2⟩, ?_⟩
    intro v hv _
    obtain ⟨t'', rfl, hst⟩ := steps_pack_inv hv
    exact ⟨t'', _, rfl, hlt, hcB'.red_steps ht hst⟩
  case c_lam =>
    intro Ψ Θ Γ D A hwfA hD ih ρ θ σ hok
    refine ⟨hwfA, ?_⟩
    simp only [Tm.subst]
    have hpos : PosOK W ⟨Ψ, Θ, ρ, θ⟩ A := ⟨hok.val, hok.bounds, hok.tenv, hwfA⟩
    have hclosed : (Tm.lam (Clause.substList σ D)).Closed := by
      have := Tm.closed_subst (t := .lam D) hok.sem.2 (fun x hx => by
        have hxΓ := exprTy_fv (ExprTy.lam hwfA hD) x hx
        obtain ⟨⟨y, B⟩, hm, rfl⟩ := List.mem_map.mp hxΓ
        obtain ⟨B', hB'⟩ := lookup_first hm
        obtain ⟨v, hv, _⟩ := hok.sem.1 y B' hB'
        exact ⟨v, hv⟩)
      simpa [Tm.subst] using this
    have := clause_head hW (h := .lam (Clause.substList σ D)) (D := Clause.substList σ D)
      (by simp [IsHead]) hclosed (headStep_lam W _) hpos ?_ ?_ [] ⟨Ψ, Θ, ρ, θ⟩ A (.nil _ _)
    · simpa [SCtx.den] using this
    · intro es u c' C hs hsel
      obtain ⟨qs, t', σm, hmem, hm, rfl⟩ := selectClause_inv hsel
      obtain ⟨t₀, hmem₀, rfl⟩ := mem_substList hmem
      exact ih (.mk qs t₀) hmem₀ ρ θ σ hok hwfA es σm c' C hs hm
    · intro es c' C hs qs t' hmem hlt hne
      obtain ⟨t₀, hmem₀, rfl⟩ := mem_substList hmem
      cases hD (.mk qs t₀) hmem₀ with
      | mk hsp _ =>
        exact spine_shape hsp ⟨Ψ, Θ, ρ, θ⟩ A es c' C [] [] (by intro i b h; simp at h)
          (by intro X T h; simp at h) hpos (by rw [Ty.substSize_nil, Ty.substFTy_nil]) hs hlt hne
  case c_glob =>
    intro Ψ Θ Γ g as hg hwfg hclg hsub hwfT ρ θ σ hok
    refine ⟨hwfT, ?_⟩
    obtain ⟨hlc, hvg, _⟩ := callee_val hok.val hwfg hsub
    simp only [Tm.subst]
    unfold interpT
    rw [interp_substSize W ρ θ hlc]
    have := interp_fun_ty (W := W) hclg (substVal ρ (g.sizeParams.dom.zip as)) θ
    unfold interpT at this
    rw [this]
    exact E.sig g hg _ hvg
  case c_loc =>
    intro Ψ Θ Γ g as hg hwfg hclg hsub hwfT hloc ρ θ σ hok
    refine ⟨hwfT, ?_⟩
    obtain ⟨hlc, hvg, hmap⟩ := callee_val hok.val hwfg hsub
    simp only [Tm.subst]
    unfold interpT
    rw [interp_substSize W ρ θ hlc]
    have := interp_fun_ty (W := W) hclg (substVal ρ (g.sizeParams.dom.zip as)) θ
    unfold interpT at this
    rw [this]
    exact E.guard Ψ ρ g as hg hloc hok.val hok.inv _ hvg hmap
  case c_sub =>
    intro Ψ Θ Γ t A B _ hAB hwfB ih ρ θ σ hok
    obtain ⟨_, ht⟩ := ih ρ θ σ hok
    exact ⟨hwfB, (subTy_sound hW hAB ρ θ hok.val hok.bounds hok.tenv.trel).2.2 ht⟩
  case c_clause =>
    intro Ψ Ψ' Θ Θ' Γ Γ' qs t A C hsp _ ih ρ θ σ hok hwfA
    intro es σm ce Ce hs hm
    have hlenq := matchSpine_yes_length hm
    have hes : es = es.take qs.length ++ es.drop qs.length := (List.take_append_drop _ _).symm
    rw [hes] at hs
    obtain ⟨cm, Tm', hs₁, hs₂⟩ := semSpine_split hs
    have hm₁ := matchSpine_take hm
    have hpos : PosOK W ⟨Ψ, Θ, ρ, θ⟩ A := ⟨hok.val, hok.bounds, hok.tenv, hwfA⟩
    obtain ⟨ρc, θc, πS', πT', hv', hb', hθ', hag', hagθ', hctx', hΓ', hC, hren'⟩ :=
      spine_align hW hsp ρ θ ⟨Ψ, Θ, ρ, θ⟩ A _ cm Tm' σm [] [] hpos hpos
        (by rw [Ty.substSize_nil, Ty.substFTy_nil]) (Renaming.refl W _) hs₁ hm₁
        (by simp [List.length_take]; omega)
    have hokb : CtxOK W Inv (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) ρc θc (σm ++ σ) := by
      refine ⟨hv', hb', hθ', ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hΓ' p hp
        · have := hok.types p hp
          rw [TyCtx.toK_append]
          exact KindingC.mono_append this
      · apply hctx'.append (hok.sem.agree hok.types (fun i hi => (hag' i hi).symm)
          (fun X hX => (hagθ' X hX).symm))
        rw [(matchSpine_facts qs _ σm hm₁).1, spineTy_dom hsp]
      · exact E.mono Ψ (Ψ ++ Ψ') ρ ρc hok.inv dom_append_left hag'
    obtain ⟨_, hbody⟩ := ih ρc θc (σm ++ σ) hokb
    have hσc : ∀ x v, (σ.filter (fun p => decide (p.1 ∉ spineVars qs))).lookup x = some v →
        v.Closed := by
      intro x v hx
      rw [lookup_filter_not_mem] at hx
      by_cases hmx : x ∈ spineVars qs
      · simp [hmx] at hx
      · simp only [hmx, if_false] at hx; exact hok.sem.2 x v hx
    have hdomm : σm.map Prod.fst = spineVars qs := (matchSpine_facts qs _ σm hm₁).1
    have heq : (t.subst (σ.filter (fun p => decide (p.1 ∉ spineVars qs)))).subst σm =
        t.subst (σm ++ σ) := by
      rw [Tm.subst_subst hσc]
      apply Tm.subst_congr
      intro x
      rw [List.lookup_append, List.lookup_append, lookup_filter_not_mem]
      by_cases hmx : x ∈ spineVars qs
      · obtain ⟨v, hv⟩ := lookup_isSome_of_mem (σ := σm) (by rw [hdomm]; exact hmx)
        simp [hmx, hv]
      · have hn : σm.lookup x = none := lookup_none_of_not_mem (by rw [hdomm]; exact hmx)
        simp [hmx, hn]
    rw [heq]
    have hposm := semSpine_posOK hs₁ hpos
    have hmem : t.subst (σm ++ σ) ∈ cm.den W Tm' := by
      rw [← hren'.den_eq hposm.tyWf, ← hC]; exact hbody
    exact semSpine_app hs₂ hposm _ hmem

end NishtAbel2024V5
