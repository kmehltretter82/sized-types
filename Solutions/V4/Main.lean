import Solutions.V4.Fundamental
import Solutions.V3.SCT.SCTFiniteIntervals
import Solutions.V3.SCT.Intervals
import Solutions.V3.SCT.NoChain

/-! # V4: size-change termination on ordinals, and the main theorems -/

namespace NishtAbel2024V4

open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid FunName InvGraphClosure)
open NishtAbel2024V2.SCTPort

/-- Infinite Ramsey's theorem for pairs with finitely many colours. Proved in `SCT/Ramsey.lean`
and supplied in `Final.lean`; taken as a hypothesis here to keep this file's imports light. -/
def RamseyPairs : Prop :=
  ∀ {C : Type} [Finite C] (color : Finset Nat → C), ∃ (M : Set Nat) (b : C), M.Infinite ∧
    ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b

/-! ## Theorem 1: the semantic call relation is well-founded -/

/-- `(g, β⃗) ≺ (f, α⃗)`: some invocation graph from `f` to `g` relates the sizes. -/
def CallRel (𝒢 : InvGraphFamily) (callee caller : FunName × List Ordinal.{0}) : Prop :=
  ∃ G ∈ 𝒢.graphs caller.1 callee.1, OrdConforms G callee.2 caller.2

theorem ordConforms_iff {G : InvGraph} {βs αs : List Ordinal.{0}} :
    OrdConforms G βs αs ↔ ConformsU (· < ·) (· ≤ ·) G βs αs := by
  simp only [OrdConforms, ConformsU, List.get_eq_getElem]

theorem callRel_wf (ramsey : RamseyPairs) (𝒢 : InvGraphFamily) (valid : SCTValid 𝒢) :
    WellFounded (CallRel 𝒢) := by
  apply NishtAbel2024V3.wellFounded_of_no_descending_sequence
  intro states steps
  classical
  choose g hg hc using steps
  have hclosed : ∀ i, InvGraphClosure 𝒢 (states i).1 (states (i + 1)).1 (g i) := by
    intro i
    have hn := (valid.1.2 (states i).1 (states (i + 1)).1 (g i) (hg i)).2.2
    simpa only [← hn] using (InvGraphClosure.base (hg i))
  have hconf : ∀ i, ConformsU (· < ·) (· ≤ ·) (g i) (states (i + 1)).2 (states i).2 :=
    fun i => ordConforms_iff.mp (hc i)
  obtain ⟨dom, hsupport⟩ := valid.1.1
  have hnames : ∀ n, (states n).1 ∈ dom := fun n => (closure_support 𝒢 dom hsupport (hclosed n)).1
  apply no_chain_from_finite_intervals (· < ·) (· ≤ ·) Ordinal.lt_wf 𝒢 valid dom
    (fun n => (states n).1) hnames (interval g) (fun n => (states n).2)
  · exact interval_concat_of_conforms (fun x1 x2 : Ordinal.{0} => x1 < x2)
      (fun x1 x2 : Ordinal.{0} => x1 ≤ x2) g (fun n => (states n).2) hconf
  · exact interval_closed 𝒢 (fun n => (states n).1) g hclosed
  · exact interval_conforms (fun x1 x2 : Ordinal.{0} => x1 < x2)
      (fun x1 x2 : Ordinal.{0} => x1 ≤ x2) (fun _ _ h => h.le) (fun _ _ _ => le_trans)
      (fun _ _ _ => lt_of_lt_of_le) (fun _ _ _ => lt_of_le_of_lt) g (fun n => (states n).2) hconf
  · exact ramsey

/-! ## Auxiliary facts -/

theorem SizeCtxWf.bounds {Ψ : SizeCtx} (h : SizeCtxWf Ψ) : CtxBoundsWf Ψ := by
  induction h with
  | nil => intro p hp; simp at hp
  | snoc _ _ ha ih => exact ih.extend ha

theorem World.lookup_of_mem {W : World} (hn : (W.map FunDecl.name).Nodup) {d : FunDecl}
    (hd : d ∈ W) : W.lookup d.name = some d := by
  unfold World.lookup
  cases h : W.find? (fun e => e.name == d.name) with
  | none =>
    have := List.find?_eq_none.mp h d hd
    simp at this
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hname : e.name = d.name := by simpa using List.find?_some h
    rw [List.inj_on_of_nodup_map hn he hd hname]

theorem Tm.subst_nil (t : Tm) : t.subst [] = t := Tm.subst_of_fv t (fun _ _ => rfl)

theorem clauses_closed {Ω : TypingEnv} {Ψ : SizeCtx} {Θ : List Nat} {A : Ty} {D : List Clause}
    (hA : TyWf Ψ Θ 0 0 A) (hD : ∀ cl ∈ D, ClauseTy Ω Ψ Θ [] cl A) : (Tm.lam D).Closed := by
  unfold Tm.Closed
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  have := exprTy_fv (ExprTy.lam hA hD) x hx
  simp at this

/-! ## Theorem 15 -/

theorem theorem_15_proof (ramsey : RamseyPairs) (W sig Ξ : List FunDecl)
    (hW : ∀ d ∈ sig ++ Ξ, d ∈ W)
    (hnames : (W.map FunDecl.name).Nodup)
    (hclosed : ∀ d ∈ W, (Tm.lam d.clauses).Closed)
    (htyped : BlockTy sig Ξ)
    (hsig : SemValid W sig) :
    SemValid W Ξ := by
  obtain ⟨𝒢, hsct, _, hdecl⟩ := htyped
  have hwc : WorldClosed W := hclosed
  have hwf := callRel_wf ramsey 𝒢 hsct
  suffices H : ∀ st : FunName × List Ordinal.{0}, ∀ d ∈ Ξ, d.name = st.1 →
      ∀ ρ, ValidVal d.sizeParams ρ → d.sizeParams.map (fun p => ρ p.1) = st.2 →
      Tm.fn d.name ∈ interp W ρ TEnv.empty d.ty SzEnv.zero Env.empty by
    intro d hd ρ hv
    exact H (d.name, d.sizeParams.map (fun p => ρ p.1)) d hd rfl ρ hv rfl
  intro st
  induction st using hwf.induction with
  | _ st ih =>
  intro d hd hname ρ hv hst
  obtain ⟨hctxwf, htywf, hcls⟩ := hdecl d hd
  let Ω : TypingEnv := ⟨sig, Ξ, 𝒢, d.name, d.sizeParams⟩
  have hguard : GuardOK W Ω st.2 := by
    rintro g hg ρg hvg ⟨G, hG, hconf⟩
    refine ih (g.name, g.sizeParams.map (fun p => ρg p.1)) ⟨G, ?_, hconf⟩ g hg rfl ρg hvg rfl
    rw [← hname]; exact hG
  have E : FundEnv W Ω st.2 := ⟨hwc, hsig, hguard⟩
  have hθ : TEnvOK W [] TEnv.empty := by intro X hX; simp at hX
  have hok : CtxOK W Ω st.2 d.sizeParams [] [] ρ TEnv.empty [] :=
    ⟨hv, hctxwf.bounds, hθ, by simp [TermCtxWf], SemCtx.nil W ρ TEnv.empty, hst,
      fun p hp => SizeCtx.mem_dom (a := p.2) (by simpa using hp)⟩
  have hlam := (fundamental E (ExprTy.lam htywf hcls) ρ TEnv.empty [] hok).2
  rw [Tm.subst_nil] at hlam
  have hpos : PosOK W ⟨d.sizeParams, [], ρ, TEnv.empty⟩ d.ty := ⟨hv, hctxwf.bounds, hθ, htywf⟩
  have hdW : d ∈ W := hW d (List.mem_append_right _ hd)
  have := clause_head hwc (h := .fn d.name) (D := d.clauses) (by simp [IsHead]) rfl
    (headStep_fn (World.lookup_of_mem hnames hdW)) hpos ?_ ?_ [] _ _ (.nil _ _)
  · simpa [SCtx.den] using this
  · intro es u c' C hs hsel
    have hl := semSpine_app hs hpos _ hlam
    have hst' : Step W (Tm.appSpine (.lam d.clauses) es) u :=
      Step.head (by rw [headStep_lam]; exact hsel)
    have hposC := semSpine_posOK hs hpos
    exact (interp_cand_closed hwc hposC.2.2.2 c'.ρ hposC.2.2.1).red _ hl _ hst'
  · intro es c' C hs qs t hmem hlt hne
    cases hcls (.mk qs t) hmem with
    | mk hsp _ =>
      exact spine_shape hsp _ d.ty es c' C [] [] (by intro i b h; simp at h)
        (by intro X T h; simp at h) hpos (by rw [Ty.substSize_nil, Ty.substFTy_nil]) hs hlt hne

/-! ## Theorem 5 -/

theorem blocks_closed {blocks : List (List FunDecl)} (h : BlocksTy blocks) :
    ∀ d ∈ blocks.flatten, (Tm.lam d.clauses).Closed := by
  induction h with
  | nil => intro d hd; simp at hd
  | snoc _ hΞ ih =>
    intro d hd
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.mem_append] at hd
    rcases hd with hd | hd
    · exact ih d hd
    · obtain ⟨𝒢, _, _, hdecl⟩ := hΞ
      obtain ⟨_, hA, hcls⟩ := hdecl d hd
      exact clauses_closed hA hcls

theorem blocks_valid (ramsey : RamseyPairs) {W : World} (hnames : (W.map FunDecl.name).Nodup) (hwc : WorldClosed W)
    {blocks : List (List FunDecl)} (h : BlocksTy blocks) (hsub : ∀ d ∈ blocks.flatten, d ∈ W) :
    SemValid W blocks.flatten := by
  induction h with
  | nil => intro d hd; simp at hd
  | @snoc blocks Ξ _ hΞ ih =>
    have hsub' : ∀ d ∈ blocks.flatten, d ∈ W := fun d hd => hsub d (by simp [hd])
    have hprev := ih hsub'
    have hnew := theorem_15_proof ramsey W blocks.flatten Ξ (fun d hd => hsub d (by simpa using hd))
      hnames hwc hΞ hprev
    intro d hd ρ hv
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.mem_append] at hd
    rcases hd with hd | hd
    · exact hprev d hd ρ hv
    · exact hnew d hd ρ hv

theorem theorem_5_proof (ramsey : RamseyPairs) (blocks : List (List FunDecl)) (main : Tm) (A : Ty)
    (htyped : ProgramTy blocks main A) :
    SN blocks.flatten main := by
  obtain ⟨hbt, hnames, hmain⟩ := htyped
  have hwc : WorldClosed blocks.flatten := blocks_closed hbt
  have hvalid := blocks_valid ramsey hnames hwc hbt (fun d hd => hd)
  let Ω : TypingEnv := ⟨blocks.flatten, [], ⟨fun _ => 0, fun _ _ => []⟩, 0, []⟩
  have E : FundEnv blocks.flatten Ω [] := ⟨hwc, hvalid, fun g hg => by simp [Ω] at hg⟩
  have hθ : TEnvOK blocks.flatten [] TEnv.empty := by intro X hX; simp at hX
  have hok : CtxOK blocks.flatten Ω [] [] [] [] (fun _ => 0) TEnv.empty [] :=
    ⟨by intro p hp; simp at hp, by intro p hp; simp at hp, hθ, by simp [TermCtxWf],
      SemCtx.nil _ _ _, rfl, by intro p hp; simp [Ω] at hp⟩
  obtain ⟨hA, hm⟩ := fundamental E hmain _ _ _ hok
  rw [Tm.subst_nil] at hm
  exact (interp_closed_mem hwc hA _ hθ _ _ hm).2

end NishtAbel2024V4
