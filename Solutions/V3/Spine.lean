import Solutions.V3.Match

/-! # V3: semantic elimination spines and their alignment with copattern typing -/

namespace NishtAbel2024V3

/-- Semantic spines: eliminations valid for a closed type at a valuation. A projection picks an
ordinal `β` below the size of the record and names it by a fresh size variable. -/
inductive SemSpine (W : World) :
    SizeCtx → SizeVal → Ty → List Elim → SizeCtx → SizeVal → Ty → Prop where
  | nil (Ψ : SizeCtx) (ρ : SizeVal) (T : Ty) : SemSpine W Ψ ρ T [] Ψ ρ T
  | term {Ψ Ψ' : SizeCtx} {ρ ρ' : SizeVal} {T₁ T₂ C : Ty} {s : Tm} {es : List Elim} :
      s ∈ interp W ρ T₁ Env.empty → SemSpine W Ψ ρ T₂ es Ψ' ρ' C →
      SemSpine W Ψ ρ (.arr T₁ T₂) (.term s :: es) Ψ' ρ' C
  | proj {Ψ Ψ' : SizeCtx} {ρ ρ' : SizeVal} {a : Size} {R : List Ty} {d j : Nat} {Rd C : Ty}
      {β : Ordinal.{0}} {es : List Elim} :
      R[d]? = some Rd → j ∉ Ψ.dom → β < sizeVal ρ a →
      SemSpine W (Ψ ++ [(j, a)]) (SizeVal.update ρ j β) (Rd.substTy 0 (.nu (.var j 0) R)) es Ψ' ρ' C →
      SemSpine W Ψ ρ (.nu a R) (.proj d :: es) Ψ' ρ' C

/-- Positions reached by semantic spines satisfy the invariants. -/
def PosOK (Ψ : SizeCtx) (ρ : SizeVal) (T : Ty) : Prop :=
  ValidVal Ψ ρ ∧ CtxBoundsWf Ψ ∧ TyWf Ψ 0 T

theorem interp_unfold_nu_fresh {W : World} {Ψ : SizeCtx} {ρ : SizeVal} {a : Size} {R : List Ty}
    {d j : Nat} {Rd : Ty} (hwf : TyWf Ψ 0 (.nu a R)) (hj : j ∉ Ψ.dom) (hd : R[d]? = some Rd)
    (β : Ordinal.{0}) :
    interp W (SizeVal.update ρ j β) (Rd.substTy 0 (.nu (.var j 0) R)) Env.empty =
      interpAt W ρ R d (Env.cons (NuSet W R.length
        (fun d 𝒳 => interpAt W ρ R d (Env.cons 𝒳 Env.empty)) β) Env.empty) := by
  have hdl : d < R.length := (List.getElem?_eq_some_iff.mp hd).1
  have hRd : R[d] = Rd := (List.getElem?_eq_some_iff.mp hd).2
  have hR : ∀ T ∈ R, TyWf Ψ 1 T := by cases hwf with | nu _ h _ => exact h
  have hpos : ∀ T ∈ R, PolIn true 0 T := by cases hwf with | nu _ _ h => exact h
  have hag : ∀ i ∈ Ψ.dom, SizeVal.update ρ j β i = ρ i := SizeVal.update_agree hj
  have hwfj : TyWf (Ψ ++ [(j, Size.inf)]) 0 (.nu (.var j 0) R) :=
    .nu (by simp [SizeWf, SizeCtx.dom])
      (fun T hT => (hR T hT).weaken _ _ dom_append_left le_rfl) hpos
  rw [← hRd, interp_unfold_nu hdl hwfj]
  have hval : sizeVal (SizeVal.update ρ j β) (.var j 0) = β := by
    simp [sizeVal, SizeVal.update]
  rw [hval]
  have hG : (fun d 𝒳 => interpAt W (SizeVal.update ρ j β) R d (Env.cons 𝒳 Env.empty)) =
      (fun d 𝒳 => interpAt W ρ R d (Env.cons 𝒳 Env.empty)) := by
    funext d' 𝒳
    by_cases hd' : d' < R.length
    · rw [interpAt_eq W _ R d' _ hd', interpAt_eq W ρ R d' _ hd']
      exact interp_agree (hR _ (List.getElem_mem hd')) _ ρ _ _ hag (fun _ _ => rfl)
    · rw [interpAt_out W _ R d' _ (by omega), interpAt_out W ρ R d' _ (by omega)]
  rw [hG, interpAt_eq W _ R d _ hdl,
    interp_agree (hR _ (List.getElem_mem hdl)) _ ρ _ _ hag (fun _ _ => rfl),
    ← interpAt_eq W ρ R d _ hdl]

theorem PosOK.term {Ψ : SizeCtx} {ρ : SizeVal} {T₁ T₂ : Ty} (h : PosOK Ψ ρ (.arr T₁ T₂)) :
    PosOK Ψ ρ T₂ := by
  obtain ⟨hv, hb, hwf⟩ := h
  exact ⟨hv, hb, by cases hwf with | arr _ h => exact h⟩

theorem PosOK.proj {Ψ : SizeCtx} {ρ : SizeVal} {a : Size} {R : List Ty} {d j : Nat} {Rd : Ty}
    {β : Ordinal.{0}} (h : PosOK Ψ ρ (.nu a R)) (hd : R[d]? = some Rd) (hj : j ∉ Ψ.dom)
    (hβ : β < sizeVal ρ a) :
    PosOK (Ψ ++ [(j, a)]) (SizeVal.update ρ j β) (Rd.substTy 0 (.nu (.var j 0) R)) := by
  obtain ⟨hv, hb, hwf⟩ := h
  have ha : SizeWf Ψ a := by cases hwf with | nu ha _ _ => exact ha
  refine ⟨hv.extend hb hj ha hβ, hb.extend ha, ?_⟩
  exact (hwf.weaken _ _ dom_append_left le_rfl).unfold_nu hd (by simp [SizeWf, SizeCtx.dom])

/-- Applying a member of a type to a semantic spine for that type. -/
theorem semSpine_app {W : World} {Ψ Ψ' : SizeCtx} {ρ ρ' : SizeVal} {T C : Ty} {es : List Elim}
    (hs : SemSpine W Ψ ρ T es Ψ' ρ' C) :
    PosOK Ψ ρ T → ∀ r, r ∈ interp W ρ T Env.empty → Tm.appSpine r es ∈ interp W ρ' C Env.empty := by
  induction hs with
  | nil => intro _ r hr; exact hr
  | term hsT _ ih =>
    intro hok r hr
    exact ih hok.term _ (hr.2 _ hsT)
  | @proj Ψ Ψ' ρ ρ' a R d j Rd C β es hd hj hβ _ ih =>
    intro hok r hr
    apply ih (hok.proj hd hj hβ)
    have hdl : d < R.length := (List.getElem?_eq_some_iff.mp hd).1
    rw [interp_unfold_nu_fresh hok.2.2 hj hd β]
    simp only [interp] at hr
    rw [NuSet_eq] at hr
    exact hr.2 β hβ d hdl

theorem semSpine_split {W : World} :
    ∀ {es₁ es₂ : List Elim} {Ψ Ψ' : SizeCtx} {ρ ρ' : SizeVal} {T C : Ty},
      SemSpine W Ψ ρ T (es₁ ++ es₂) Ψ' ρ' C →
      ∃ Ψm ρm Tm', SemSpine W Ψ ρ T es₁ Ψm ρm Tm' ∧ SemSpine W Ψm ρm Tm' es₂ Ψ' ρ' C
  | [], es₂, Ψ, Ψ', ρ, ρ', T, C, h => ⟨Ψ, ρ, T, .nil _ _ _, h⟩
  | e :: es₁, es₂, Ψ, Ψ', ρ, ρ', T, C, h => by
    cases h with
    | term hs h' =>
      obtain ⟨Ψm, ρm, Tm', h₁, h₂⟩ := semSpine_split h'
      exact ⟨Ψm, ρm, Tm', .term hs h₁, h₂⟩
    | proj hd hj hβ h' =>
      obtain ⟨Ψm, ρm, Tm', h₁, h₂⟩ := semSpine_split h'
      exact ⟨Ψm, ρm, Tm', .proj hd hj hβ h₁, h₂⟩

theorem semSpine_snoc {W : World} {Ψ Ψ' Ψ'' : SizeCtx} {ρ ρ' ρ'' : SizeVal} {T C D : Ty}
    {es es' : List Elim} (h₁ : SemSpine W Ψ ρ T es Ψ' ρ' C) (h₂ : SemSpine W Ψ' ρ' C es' Ψ'' ρ'' D) :
    SemSpine W Ψ ρ T (es ++ es') Ψ'' ρ'' D := by
  induction h₁ with
  | nil => exact h₂
  | term hs _ ih => exact .term hs (ih h₂)
  | proj hd hj hβ _ ih => exact .proj hd hj hβ (ih h₂)

theorem semSpine_posOK {W : World} {Ψ Ψ' : SizeCtx} {ρ ρ' : SizeVal} {T C : Ty} {es : List Elim}
    (hs : SemSpine W Ψ ρ T es Ψ' ρ' C) : PosOK Ψ ρ T → PosOK Ψ' ρ' C ∧ (∀ i ∈ Ψ.dom, i ∈ Ψ'.dom) := by
  induction hs with
  | nil => intro h; exact ⟨h, fun _ h => h⟩
  | term _ _ ih => intro h; exact ih h.term
  | proj hd hj hβ _ ih =>
    intro h
    obtain ⟨h1, h2⟩ := ih (h.proj hd hj hβ)
    exact ⟨h1, fun i hi => h2 i (dom_append_left i hi)⟩

/-- Elimination spines of a semantic spine are closed. -/
theorem semSpine_closed {W : World} (hW : WorldClosed W) {Ψ Ψ' : SizeCtx} {ρ ρ' : SizeVal}
    {T C : Ty} {es : List Elim} (hs : SemSpine W Ψ ρ T es Ψ' ρ' C) :
    PosOK Ψ ρ T → ElimsClosed es := by
  induction hs with
  | nil => intro _; rfl
  | @term Ψ Ψ' ρ ρ' T₁ T₂ C s es hsT _ ih =>
    intro hok
    have hT₁ : TyWf Ψ 0 T₁ := by cases hok.2.2 with | arr h _ => exact h
    have hc := (interp_closed_mem hW hT₁ ρ hsT).1
    unfold ElimsClosed at ih ⊢
    simp only [List.flatMap_cons, Elim.fv]
    rw [ih hok.term]
    simpa [Tm.Closed] using hc
  | proj hd hj hβ _ ih =>
    intro hok
    unfold ElimsClosed at ih ⊢
    simp only [List.flatMap_cons, Elim.fv]
    rw [ih (hok.proj hd hj hβ)]
    rfl

/-! ## Alignment of copattern typing with semantic spines -/

theorem Size.subst_nil (a : Size) : a.subst [] = a := by cases a <;> rfl

mutual
theorem Ty.substSize_nil : ∀ A : Ty, A.substSize [] = A
  | .unit => rfl
  | .prod A B => by simp only [Ty.substSize]; rw [Ty.substSize_nil A, Ty.substSize_nil B]
  | .arr A B => by simp only [Ty.substSize]; rw [Ty.substSize_nil A, Ty.substSize_nil B]
  | .var _ => rfl
  | .mu a S => by simp only [Ty.substSize]; rw [Size.subst_nil, Ty.substSizeList_nil S]
  | .nu a R => by simp only [Ty.substSize]; rw [Size.subst_nil, Ty.substSizeList_nil R]
theorem Ty.substSizeList_nil : ∀ S : List Ty, Ty.substSizeList [] S = S
  | [] => rfl
  | A :: S => by simp only [Ty.substSizeList]; rw [Ty.substSize_nil A, Ty.substSizeList_nil S]
end

theorem Ty.substSizeList_getElem? (σ : List (Nat × Size)) :
    ∀ (S : List Ty) (d : Nat), (Ty.substSizeList σ S)[d]? = (S[d]?).map (Ty.substSize σ)
  | [], d => by simp [Ty.substSizeList]
  | A :: S, 0 => by simp [Ty.substSizeList]
  | A :: S, d + 1 => by simp only [Ty.substSizeList, List.getElem?_cons_succ]; exact Ty.substSizeList_getElem? σ S d

/-- The renaming invariant between a clause-side position and a spine-side position. -/
structure Renaming (Ψc : SizeCtx) (ρc : SizeVal) (Ψs : SizeCtx) (ρs : SizeVal)
    (π : List (Nat × Size)) : Prop where
  var : VarSubst π
  target : ∀ i b, π.lookup i = some b → SizeWf Ψc b
  untouched : ∀ i ∈ Ψs.dom, π.lookup i = none → i ∈ Ψc.dom
  val : ∀ i ∈ Ψs.dom, substVal ρc π i = ρs i

theorem Renaming.interp_eq {W : World} {Ψc Ψs : SizeCtx} {ρc ρs : SizeVal} {π : List (Nat × Size)}
    (h : Renaming Ψc ρc Ψs ρs π) {T : Ty} (hT : TyWf Ψs 0 T) (η : Env) :
    interp W ρc (T.substSize π) η = interp W ρs T η := by
  rw [interp_substSize W ρc h.var]
  exact interp_agree hT _ _ _ _ h.val (fun _ _ => rfl)

theorem Renaming.extend_clause {Ψc Ψs : SizeCtx} {ρc ρc' ρs : SizeVal} {π : List (Nat × Size)}
    (h : Renaming Ψc ρc Ψs ρs π) {Ψc' : SizeCtx} (hdom : ∀ i ∈ Ψc.dom, i ∈ Ψc'.dom)
    (hag : ∀ i ∈ Ψc.dom, ρc' i = ρc i) : Renaming Ψc' ρc' Ψs ρs π := by
  refine ⟨h.var, fun i b hb => (h.target i b hb).weaken hdom, fun i hi hn => hdom i (h.untouched i hi hn), ?_⟩
  intro i hi
  rw [← h.val i hi]
  simp only [substVal]
  cases hl : π.lookup i with
  | some b => exact sizeVal_agree (fun x hx => hag x hx) (h.target i b hl)
  | none => exact hag i (h.untouched i hi hl)

theorem lookup_size_cons (k x : Nat) (b : Size) (l : List (Nat × Size)) :
    ((k, b) :: l).lookup x = if x = k then some b else l.lookup x := by
  rw [List.lookup_cons]
  by_cases h : x = k
  · subst h; simp
  · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]

/-- Spine matching soundness, aligned with a semantic spine up to renaming of sizes. -/
theorem spine_align {W : World} (hW : WorldClosed W) {Ψc : SizeCtx} {qs : List Copat} {Tc : Ty}
    {Γ' : TermCtx} {Ψ'c : SizeCtx} {C : Ty} (hsp : SpineTy Ψc qs Tc Γ' Ψ'c C) :
    ∀ (ρc : SizeVal) (Ψs : SizeCtx) (ρs : SizeVal) (Ts : Ty) (es : List Elim) (Ψs' : SizeCtx)
      (ρs' : SizeVal) (Bs : Ty) (σm : TmSubst) (π : List (Nat × Size)),
      PosOK Ψc ρc Tc → PosOK Ψs ρs Ts → Tc = Ts.substSize π → Renaming Ψc ρc Ψs ρs π →
      SemSpine W Ψs ρs Ts es Ψs' ρs' Bs → matchSpine qs es = .yes σm → es.length = qs.length →
      ∃ ρc' π', ValidVal (Ψc ++ Ψ'c) ρc' ∧ CtxBoundsWf (Ψc ++ Ψ'c) ∧ (∀ i ∈ Ψc.dom, ρc' i = ρc i) ∧
        SemCtx W ρc' Γ' σm ∧ TermCtxWf (Ψc ++ Ψ'c) Γ' ∧ C = Bs.substSize π' ∧
        Renaming (Ψc ++ Ψ'c) ρc' Ψs' ρs' π' := by
  induction hsp with
  | nil Ψ A =>
    intro ρc Ψs ρs Ts es Ψs' ρs' Bs σm π hokc _ hT hren hs hm hlen
    cases es with
    | cons _ _ => simp at hlen
    | nil =>
      cases hs
      simp [matchSpine] at hm; subst hm
      refine ⟨ρc, π, by simpa using hokc.1, by simpa using hokc.2.1, fun _ _ => rfl,
        SemCtx.nil W ρc, by simp [TermCtxWf], hT, ?_⟩
      simpa using hren
  | @pat Ψ Ψ₁ Ψ₂ p qs A B C Γ₁ Γ₂ hp _ ih =>
    intro ρc Ψs ρs Ts es Ψs' ρs' Bs σm π hokc hoks hT hren hs hm hlen
    cases es with
    | nil => simp at hlen
    | cons e es =>
      cases hs with
      | proj _ _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | @term _ _ _ _ T₁ T₂ _ s _ hsT hs' =>
        simp only [matchSpine, matchCopat] at hm
        obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
        simp only [Ty.substSize] at hT
        injection hT with hA hB
        have hwfA : TyWf Ψ 0 A := by cases hokc.2.2 with | arr h _ => exact h
        have hwfB : TyWf Ψ 0 B := by cases hokc.2.2 with | arr _ h => exact h
        have hwfT₁ : TyWf Ψs 0 T₁ := by cases hoks.2.2 with | arr h _ => exact h
        have hsA : s ∈ interp W ρc A Env.empty := by
          rw [hA, hren.interp_eq hwfT₁]; exact hsT
        obtain ⟨ρ₁, hv₁, hag₁, hctx₁⟩ := pat_sound hW hp ρc s σ₁ hokc.1 hokc.2.1 hwfA hsA hm₁
        obtain ⟨hΓ₁, hb₁⟩ := patTy_ctx hp hwfA hokc.2.1
        have hren₁ := hren.extend_clause (Ψc' := Ψ ++ Ψ₁) dom_append_left hag₁
        obtain ⟨ρc', π', hv', hb', hag', hctx₂, hΓ₂, hC, hren'⟩ :=
          ih ρ₁ Ψs ρs T₂ es Ψs' ρs' Bs σ₂ π
            ⟨hv₁, hb₁, hwfB.weaken _ _ dom_append_left le_rfl⟩ hoks.term hB hren₁ hs' hm₂
            (by simpa using hlen)
        refine ⟨ρc', π', by simpa using hv', by simpa using hb', ?_, ?_, ?_, hC, by simpa using hren'⟩
        · intro i hi; rw [hag' i (dom_append_left i hi), hag₁ i hi]
        · apply (hctx₁.agree hΓ₁ (fun i hi => (hag' i hi).symm)).append hctx₂
          rw [(matchPat_facts p s σ₁ hm₁).1, patTy_dom hp]
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · simpa using (hΓ₁ q hq).weaken (Ψ ++ Ψ₁ ++ Ψ₂) 0 dom_append_left le_rfl
          · simpa using hΓ₂ q hq
  | @proj Ψ Ψ' d j qs a R Rd C Γ hd hj _ ih =>
    intro ρc Ψs ρs Ts es Ψs' ρs' Bs σm π hokc hoks hT hren hs hm hlen
    cases es with
    | nil => simp at hlen
    | cons e es =>
      cases hs with
      | term _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | @proj _ _ _ _ as Rs d' js Rds _ β _ hds hjs hβ hs' =>
        simp only [matchSpine, matchCopat] at hm
        by_cases hdd : d = d'
        · subst hdd
          simp only [if_true] at hm
          obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
          cases hm₁
          simp only [Ty.substSize] at hT
          injection hT with ha hR
          have has : SizeWf Ψs as := by cases hoks.2.2 with | nu h _ _ => exact h
          have hRs : ∀ T ∈ Rs, TyWf Ψs 1 T := by cases hoks.2.2 with | nu _ h _ => exact h
          have hRd : Rd = Rds.substSize π := by
            have := Ty.substSizeList_getElem? π Rs d
            rw [← hR, hd, hds] at this
            simpa using this
          have hβc : β < sizeVal ρc a := by
            rw [ha, sizeVal_subst hren.var]
            rw [sizeVal_agree (Ψ := Ψs) (fun i hi => hren.val i hi) has]
            exact hβ
          set ρ₁ := SizeVal.update ρc j β
          have hag₁ : ∀ i ∈ Ψ.dom, ρ₁ i = ρc i := SizeVal.update_agree hj
          have hokc₁ : PosOK (Ψ ++ [(j, a)]) ρ₁ (Rd.substTy 0 (.nu (.var j 0) R)) :=
            hokc.proj hd hj hβc
          have hoks₁ := hoks.proj hds hjs hβ
          set π' : List (Nat × Size) := (js, .var j 0) :: π
          have hRds_wf : TyWf Ψs 1 Rds := hRs Rds (List.mem_of_getElem? hds)
          have hT' : Rd.substTy 0 (.nu (.var j 0) R) =
              (Rds.substTy 0 (.nu (.var js 0) Rs)).substSize π' := by
            rw [Ty.substSize_substTy]
            have h1 : Rds.substSize π' = Rds.substSize π :=
              hRds_wf.substSize_cons_fresh hjs _ _
            have h2 : Ty.substSizeList π' Rs = Ty.substSizeList π Rs := by
              have := (hoks.2.2).substSize_cons_fresh hjs (.var j 0) π
              simp only [Ty.substSize] at this
              injection this
            have h3 : (Size.var js 0).subst π' = .var j 0 := by
              simp [π', Size.subst, lookup_size_cons, Size.shift]
            simp only [Ty.substSize, h1, h2, h3, ← hR, ← hRd]
          have hren₁ : Renaming (Ψ ++ [(j, a)]) ρ₁ (Ψs ++ [(js, as)]) (SizeVal.update ρs js β) π' := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro i b hb
              rw [lookup_size_cons] at hb
              by_cases hi : i = js
              · simp [hi] at hb; exact ⟨j, 0, hb.symm⟩
              · simp [hi] at hb; exact hren.var i b hb
            · intro i b hb
              rw [lookup_size_cons] at hb
              by_cases hi : i = js
              · simp [hi] at hb; subst hb; simp [SizeWf, SizeCtx.dom]
              · simp [hi] at hb; exact (hren.target i b hb).weaken dom_append_left
            · intro i hi hn
              rw [lookup_size_cons] at hn
              by_cases hij : i = js
              · simp [hij] at hn
              · simp only [hij, if_false] at hn
                have hi' : i ∈ Ψs.dom := by
                  simp only [SizeCtx.dom, List.map_append, List.mem_append, List.map_cons,
                    List.map_nil, List.mem_singleton] at hi
                  rcases hi with hi | hi
                  · exact hi
                  · exact absurd hi hij
                exact dom_append_left i (hren.untouched i hi' hn)
            · intro i hi
              simp only [substVal]
              rw [lookup_size_cons]
              by_cases hij : i = js
              · subst hij; simp [sizeVal, ρ₁, SizeVal.update]
              · have hi' : i ∈ Ψs.dom := by
                  simp only [SizeCtx.dom, List.map_append, List.mem_append, List.map_cons,
                    List.map_nil, List.mem_singleton] at hi
                  rcases hi with hi | hi
                  · exact hi
                  · exact absurd hi hij
                simp only [hij, if_false]
                have := (hren.extend_clause (Ψc' := Ψ ++ [(j, a)]) dom_append_left hag₁).val i hi'
                simp only [substVal] at this
                rw [this]
                simp [SizeVal.update, hij]
          obtain ⟨ρc', π'', hv', hb', hag', hctx, hΓ, hC, hren'⟩ :=
            ih ρ₁ _ _ _ es Ψs' ρs' Bs σ₂ π' hokc₁ hoks₁ hT' hren₁ hs' hm₂ (by simpa using hlen)
          refine ⟨ρc', π'', by simpa using hv', by simpa using hb', ?_, by simpa using hctx,
            by simpa using hΓ, hC, by simpa using hren'⟩
          intro i hi; rw [hag' i (dom_append_left i hi), hag₁ i hi]
        · simp [hdd, MatchRes.and_no_left] at hm

end NishtAbel2024V3
