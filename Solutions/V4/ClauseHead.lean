import Solutions.V4.Spine
import Mathlib.Data.Fintype.Card

/-! # V4: soundness of clause-headed terms -/

namespace NishtAbel2024V4

/-- One argument of a spine takes a step. -/
inductive SpineStep (W : World) : List Elim → List Elim → Prop where
  | here {s s' : Tm} {es : List Elim} : Step W s s' → SpineStep W (.term s :: es) (.term s' :: es)
  | there {e : Elim} {es es' : List Elim} : SpineStep W es es' → SpineStep W (e :: es) (e :: es')

theorem spineStep_append {W : World} {es es' : List Elim} (h : SpineStep W es es') (e : Elim) :
    SpineStep W (es ++ [e]) (es' ++ [e]) := by
  induction h with
  | here hs => exact .here hs
  | there _ ih => exact .there ih

theorem spineStep_snoc {W : World} (es : List Elim) {s s' : Tm} (h : Step W s s') :
    SpineStep W (es ++ [.term s]) (es ++ [.term s']) := by
  induction es with
  | nil => exact .here h
  | cons e es ih => exact .there ih

/-- Atomic heads: `λ{D⃗}` or a function name. -/
def IsHead : Tm → Prop
  | .lam _ => True
  | .fn _ => True
  | _ => False

/-- Steps of a head applied to a spine: a head step, or a step inside an argument. -/
theorem step_appSpine_head {W : World} {h : Tm} (hh : IsHead h) :
    ∀ (es : List Elim) (u : Tm), Step W (Tm.appSpine h es) u →
      headStep W (Tm.appSpine h es) = some u ∨ ∃ es', SpineStep W es es' ∧ u = Tm.appSpine h es' := by
  intro es
  induction es using List.reverseRecOn with
  | nil =>
    intro u hs
    cases h <;> simp [IsHead] at hh <;> cases hs <;> simp_all
  | append_singleton es e ih =>
    intro u hs
    rw [Tm.appSpine_snoc] at hs ⊢
    cases hs with
    | head hh' => exact Or.inl hh'
    | appFun hr =>
      rcases ih _ hr with hh' | ⟨es', hst, rfl⟩
      · left
        have := headStep_appSpine hh' [e]
        simpa using this
      · right; exact ⟨es' ++ [e], spineStep_append hst e, by simp⟩
    | appArg hs' =>
      right; exact ⟨es ++ [.term _], spineStep_snoc es hs', by simp⟩

theorem spineStep_acc_cons {W : World} : ∀ (e : Elim), (∀ s, e = .term s → SN W s) →
    ∀ es, Acc (fun es' es => SpineStep W es es') es →
      Acc (fun es' es => SpineStep W es es') (e :: es)
  | .proj d, _, es, hes => by
    induction hes with
    | intro es _ ih =>
      refine Acc.intro _ fun es' hst => ?_
      cases hst with
      | there hst => exact ih _ hst
  | .inst, _, es, hes => by
    induction hes with
    | intro es _ ih =>
      refine Acc.intro _ fun es' hst => ?_
      cases hst with
      | there hst => exact ih _ hst
  | .term s, he, es, hes => by
    have hs : SN W s := he s rfl
    clear he
    induction hs generalizing es with
    | intro s _ ihs =>
      induction hes with
      | intro es hes' ihes =>
        refine Acc.intro _ fun es' hst => ?_
        cases hst with
        | here hss =>
          exact ihs _ hss es (Acc.intro (r := fun es' es => SpineStep W es es') es hes')
        | there hst' => exact ihes _ hst'

/-- Spines whose term arguments are strongly normalizing are accessible for `SpineStep`. -/
theorem spineStep_acc {W : World} :
    ∀ es : List Elim, (∀ s, Elim.term s ∈ es → SN W s) → Acc (fun es' es => SpineStep W es es') es
  | [], _ => Acc.intro _ fun _ h => by cases h
  | e :: es, h =>
    spineStep_acc_cons e (fun s hs => h s (by rw [hs]; simp)) es
      (spineStep_acc es (fun s hs => h s (List.mem_cons_of_mem _ hs)))

/-- Semantic spines are preserved by argument steps. -/
theorem semSpine_spineStep {W : World} (hW : WorldClosed W) {c c' : SCtx} {T C : Ty}
    {es : List Elim} (hs : SemSpine W c T es c' C) :
    PosOK W c T → ∀ es', SpineStep W es es' → SemSpine W c T es' c' C := by
  induction hs with
  | nil => intro _ es' h; cases h
  | @term c c' T₁ T₂ C s es hsT hs' ih =>
    intro hok es' h
    cases h with
    | here hss =>
      have hT₁ : TyWf c.Ψ c.Θ 0 0 T₁ := by cases hok.2.2.2 with | arr h _ => exact h
      have hcand := interp_cand_closed hW hT₁ c.ρ hok.2.2.1
      exact .term (hcand.red _ hsT _ hss) hs'
    | there h => exact .term hsT (ih hok.term _ h)
  | proj hd hj hβ _ ih =>
    intro hok es' h
    cases h with
    | there h => exact .proj hd hj hβ (ih (hok.proj hd hj hβ) _ h)
  | instT hX h𝒳 _ ih =>
    intro hok es' h
    cases h with
    | there h => exact .instT hX h𝒳 (ih (hok.instT h𝒳) _ h)
  | instS hj hβ _ ih =>
    intro hok es' h
    cases h with
    | there h => exact .instS hj hβ (ih (hok.instS hj hβ) _ h)

/-! ## Spine-length facts for clause selection -/

theorem matchSpine_append_of_le :
    ∀ (qs : List Copat) (es es₂ : List Elim), qs.length ≤ es.length →
      matchSpine qs (es ++ es₂) = matchSpine qs es
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => by simp at h
  | q :: qs, e :: es, es₂, h => by
    simp only [matchSpine, List.cons_append]
    rw [matchSpine_append_of_le qs es es₂ (by simpa using h)]

def clauseLen : Clause → Nat
  | .mk qs _ => qs.length

def maxLen (D : List Clause) : Nat := D.foldr (fun cl m => max (clauseLen cl) m) 0

theorem le_maxLen {D : List Clause} {cl : Clause} (h : cl ∈ D) : clauseLen cl ≤ maxLen D := by
  induction D with
  | nil => simp at h
  | cons c D ih =>
    simp only [maxLen, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- If every clause longer than the spine already mismatches it, extending a stuck spine keeps
it stuck. -/
theorem selectClause_append_none {D : List Clause} {es : List Elim}
    (hlong : ∀ qs t, Clause.mk qs t ∈ D → es.length < qs.length → matchSpine qs es = .no)
    (h : selectClause D es = none) (es₂ : List Elim) : selectClause D (es ++ es₂) = none := by
  induction D with
  | nil => rfl
  | cons cl D ih =>
    obtain ⟨qs, t⟩ := cl
    have hD : ∀ qs' t', Clause.mk qs' t' ∈ D → es.length < qs'.length →
        matchSpine qs' es = .no :=
      fun qs' t' hm hl => hlong qs' t' (List.mem_cons_of_mem _ hm) hl
    simp only [selectClause] at h ⊢
    by_cases hq : qs.length ≤ es.length
    · rw [matchSpine_append_of_le qs es es₂ hq]
      cases hm : matchSpine qs es with
      | yes σ => rw [hm] at h; simp at h
      | no => rw [hm] at h; exact ih hD h
      | stuck => rfl
    · have hno := hlong qs t (by simp) (by omega)
      rw [matchSpine_append_no hno es₂]
      rw [hno] at h
      exact ih hD h

theorem exists_fresh (l : List Nat) : ∃ j, j ∉ l := by
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset l.toFinset
  exact ⟨j, by simpa using hj⟩

/-! ## Shapes of positions that a longer clause can still consume -/

/-- Elimination types: the types a copattern can consume. -/
def IsElimTy : Ty → Prop
  | .arr _ _ => True
  | .nu _ _ => True
  | .allT _ => True
  | .allS _ _ => True
  | _ => False

theorem isElimTy_rename {πS : List (Nat × Size)} {πT : List (Nat × Ty)} (hfv : FVarSubst πT) :
    ∀ {T : Ty}, IsElimTy ((T.substSize πS).substFTy πT) → IsElimTy T
  | .fvar X, h => by
    simp only [Ty.substSize, Ty.substFTy] at h
    cases hl : πT.lookup X with
    | none => simp [hl, IsElimTy] at h
    | some U =>
      obtain ⟨Y, rfl⟩ := hfv X U hl
      simp [hl, IsElimTy] at h
  | .arr _ _, _ => by simp [IsElimTy]
  | .nu _ _, _ => by simp [IsElimTy]
  | .allT _, _ => by simp [IsElimTy]
  | .allS _ _, _ => by simp [IsElimTy]
  | .unit, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h
  | .prod _ _, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h
  | .var _, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h
  | .mu _ _, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h
  | .exT _, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h
  | .exS _ _, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h

theorem VarSubst.cons {πS : List (Nat × Size)} (h : VarSubst πS) (js j : Nat) :
    VarSubst ((js, Size.var j 0) :: πS) := by
  intro i b hb
  rw [lookup_size_cons] at hb
  by_cases hi : i = js
  · simp [hi] at hb; exact ⟨j, 0, hb.symm⟩
  · simp [hi] at hb; exact h i b hb

theorem FVarSubst.cons {πT : List (Nat × Ty)} (h : FVarSubst πT) (Xs X : Nat) :
    FVarSubst ((Xs, Ty.fvar X) :: πT) := by
  intro Y T hT
  rw [lookup_ty_cons] at hT
  by_cases hY : Y = Xs
  · simp [hY] at hT; exact ⟨X, hT.symm⟩
  · simp [hY] at hT; exact h Y T hT

/-- Renamed types stay related after a projection at fresh size variables. -/
theorem align_proj_ty {cs : SCtx} {πS : List (Nat × Size)} {πT : List (Nat × Ty)}
    (hfv : FVarSubst πT) {a as : Size} {R Rs : List Ty}
    (hT : Ty.nu a R = ((Ty.nu as Rs).substSize πS).substFTy πT)
    (hwf : TyWf cs.Ψ cs.Θ 0 0 (.nu as Rs)) {d : Nat} {Rd Rds : Ty}
    (hd : R[d]? = some Rd) (hds : Rs[d]? = some Rds) {j js : Nat} (hjs : js ∉ cs.Ψ.dom) :
    Rd.substTy 0 (.nu (.var j 0) R) =
      ((Rds.substTy 0 (.nu (.var js 0) Rs)).substSize ((js, .var j 0) :: πS)).substFTy πT := by
  simp only [Ty.substSize, Ty.substFTy] at hT
  injection hT with _ hR
  have hRs : ∀ T ∈ Rs, TyWf cs.Ψ cs.Θ 1 0 T := by cases hwf with | nu _ h _ => exact h
  have hRd : Rd = (Rds.substSize πS).substFTy πT := by
    have h1 := Ty.substSizeList_getElem? πS Rs d
    have h2 := Ty.substFTyList_getElem? πT (Ty.substSizeList πS Rs) d
    rw [h1, hds] at h2
    rw [← hR, hd] at h2
    simpa using h2
  have hRds_wf : TyWf cs.Ψ cs.Θ 1 0 Rds := hRs Rds (List.mem_of_getElem? hds)
  rw [Ty.substSize_substTy, Ty.substFTy_substTy hfv.closed]
  have h1 : Rds.substSize ((js, .var j 0) :: πS) = Rds.substSize πS :=
    hRds_wf.substSize_cons_fresh hjs _ _
  have h2 : Ty.substSizeList ((js, .var j 0) :: πS) Rs = Ty.substSizeList πS Rs := by
    have := hwf.substSize_cons_fresh hjs (.var j 0) πS
    simp only [Ty.substSize] at this
    injection this
  have h3 : (Size.var js 0).subst ((js, .var j 0) :: πS) = .var j 0 := by
    simp [Size.subst, lookup_size_cons, Size.shift]
  simp only [Ty.substSize, Ty.substFTy, h1, h2, h3, ← hR, ← hRd]

/-- Renamed types stay related after a type instantiation at fresh type variables. -/
theorem align_instT_ty {cs : SCtx} {πS : List (Nat × Size)} {πT : List (Nat × Ty)}
    (hfv : FVarSubst πT) {B Bs' : Ty}
    (hT : Ty.allT B = ((Ty.allT Bs').substSize πS).substFTy πT)
    (hwf : TyWf cs.Ψ cs.Θ 0 0 (.allT Bs')) {X Xs : Nat} (hXs : Xs ∉ cs.Θ) :
    B.substTy 0 (.fvar X) =
      ((Bs'.substTy 0 (.fvar Xs)).substSize πS).substFTy ((Xs, .fvar X) :: πT) := by
  simp only [Ty.substSize, Ty.substFTy] at hT
  injection hT with hB
  have hBs : TyWf cs.Ψ cs.Θ 1 0 Bs' := by cases hwf with | allT h => exact h
  have hfv' := hfv.cons Xs X
  rw [Ty.substSize_substFTy hfv', Ty.substFTy_substTy hfv'.closed, Ty.substSize_substTy]
  have h1 : Bs'.substFTy ((Xs, .fvar X) :: πT) = Bs'.substFTy πT :=
    hBs.substFTy_cons_fresh hXs _ _
  have h2 : (Ty.fvar Xs).substFTy ((Xs, .fvar X) :: πT) = .fvar X := by
    simp [Ty.substFTy, lookup_ty_cons]
  rw [h1, h2, ← Ty.substSize_substFTy hfv, ← hB]
  rfl

/-- Renamed types stay related after a size instantiation at fresh size variables. -/
theorem align_instS_ty {cs : SCtx} {πS : List (Nat × Size)} {πT : List (Nat × Ty)}
    (hvarS : VarSubst πS) (hfv : FVarSubst πT) {a as : Size} {B Bs' : Ty}
    (hT : Ty.allS a B = ((Ty.allS as Bs').substSize πS).substFTy πT)
    (hwf : TyWf cs.Ψ cs.Θ 0 0 (.allS as Bs')) {j js : Nat} (hjs : js ∉ cs.Ψ.dom) :
    B.openSz 0 (.var j 0) =
      ((Bs'.openSz 0 (.var js 0)).substSize ((js, .var j 0) :: πS)).substFTy πT := by
  simp only [Ty.substSize, Ty.substFTy] at hT
  injection hT with _ hB
  have hBs : TyWf cs.Ψ cs.Θ 0 1 Bs' := by cases hwf with | allS _ h => exact h
  rw [Ty.substSize_openSz (hvarS.cons js j), Ty.substFTy_openSz hfv.closed]
  have h1 : Bs'.substSize ((js, .var j 0) :: πS) = Bs'.substSize πS :=
    hBs.substSize_cons_fresh hjs _ _
  have h3 : (Size.var js 0).subst ((js, .var j 0) :: πS) = .var j 0 := by
    simp [Size.subst, lookup_size_cons, Size.shift]
  rw [h1, h3, ← hB]

/-- A clause longer than a semantic spine, whose copatterns do not yet mismatch the spine, sees
an elimination type at the end of the spine. -/
theorem spine_shape {W : World} {Ψc : SizeCtx} {Θc : List Nat}
    {qs : List Copat} {Tc : Ty} {Γ' : TermCtx} {Ψ'c : SizeCtx} {Θ'c : List Nat} {C : Ty}
    (hsp : SpineTy Ψc Θc qs Tc Γ' Ψ'c Θ'c C) :
    ∀ (cs : SCtx) (Ts : Ty) (es : List Elim) (cs' : SCtx) (Bs : Ty)
      (πS : List (Nat × Size)) (πT : List (Nat × Ty)),
      VarSubst πS → FVarSubst πT → PosOK W cs Ts → Tc = (Ts.substSize πS).substFTy πT →
      SemSpine W cs Ts es cs' Bs → es.length < qs.length → matchSpine qs es ≠ .no →
      IsElimTy Bs := by
  induction hsp with
  | nil Ψ Θ A =>
    intro cs Ts es cs' Bs πS πT _ _ _ _ _ hlen _
    simp at hlen
  | @pat Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p qs A B C Γ₁ Γ₂ hp _ ih =>
    intro cs Ts es cs' Bs πS πT hvarS hfv hoks hT hs hlen hm
    cases es with
    | nil =>
      cases hs
      exact isElimTy_rename hfv (by rw [← hT]; simp [IsElimTy])
    | cons e es =>
      cases hs with
      | proj _ _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | instT _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | instS _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | @term _ _ T₁ T₂ _ s _ hsT hs' =>
        simp only [Ty.substSize, Ty.substFTy] at hT
        injection hT with _ hB
        refine ih cs T₂ es cs' Bs πS πT hvarS hfv hoks.term hB hs' (by simpa using hlen) ?_
        intro hno
        apply hm
        simp only [matchSpine, hno, MatchRes.and_no_right]
  | @proj Ψ Ψ' Θ Θ' d j qs a R Rd C Γ hd hj _ ih =>
    intro cs Ts es cs' Bs πS πT hvarS hfv hoks hT hs hlen hm
    cases es with
    | nil =>
      cases hs
      exact isElimTy_rename hfv (by rw [← hT]; simp [IsElimTy])
    | cons e es =>
      cases hs with
      | term _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | instT _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | instS _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | @proj _ _ as Rs d' js Rds _ β _ hds hjs hβ hs' =>
        by_cases hdd : d = d'
        · subst hdd
          have hT' := align_proj_ty (cs := cs) (j := j) hfv hT hoks.2.2.2 hd hds hjs
          refine ih _ _ es cs' Bs _ πT (hvarS.cons js j) hfv (hoks.proj hds hjs hβ) hT' hs'
            (by simpa using hlen) ?_
          intro hno
          apply hm
          simp only [matchSpine, hno, MatchRes.and_no_right]
        · exact (hm (by simp [matchSpine, matchCopat, hdd, MatchRes.and_no_left])).elim
  | @instT Ψ Ψ' Θ Θ' X qs B C Γ hX _ ih =>
    intro cs Ts es cs' Bs πS πT hvarS hfv hoks hT hs hlen hm
    cases es with
    | nil =>
      cases hs
      exact isElimTy_rename hfv (by rw [← hT]; simp [IsElimTy])
    | cons e es =>
      cases hs with
      | term _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | proj _ _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | instS _ _ _ =>
        simp only [Ty.substSize, Ty.substFTy] at hT
        cases hT
      | @instT _ _ Bs' _ Xs 𝒳 _ hXs h𝒳 hs' =>
        have hT' := align_instT_ty (cs := cs) (X := X) hfv hT hoks.2.2.2 hXs
        refine ih _ _ es cs' Bs πS _ hvarS (hfv.cons Xs X) (hoks.instT h𝒳) hT' hs'
          (by simpa using hlen) ?_
        intro hno
        apply hm
        simp only [matchSpine, hno, MatchRes.and_no_right]
  | @instS Ψ Ψ' Θ Θ' j qs a B C Γ hj _ ih =>
    intro cs Ts es cs' Bs πS πT hvarS hfv hoks hT hs hlen hm
    cases es with
    | nil =>
      cases hs
      exact isElimTy_rename hfv (by rw [← hT]; simp [IsElimTy])
    | cons e es =>
      cases hs with
      | term _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | proj _ _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | instT _ _ _ =>
        simp only [Ty.substSize, Ty.substFTy] at hT
        cases hT
      | @instS _ _ as Bs' _ js β _ hjs hβ hs' =>
        have hT' := align_instS_ty (cs := cs) (j := j) hvarS hfv hT hoks.2.2.2 hjs
        refine ih _ _ es cs' Bs _ πT (hvarS.cons js j) hfv (hoks.instS hjs hβ) hT' hs'
          (by simpa using hlen) ?_
        intro hno
        apply hm
        simp only [matchSpine, hno, MatchRes.and_no_right]

theorem semSpine_args_sn {W : World} (hW : WorldClosed W) {c c' : SCtx} {T C : Ty}
    {es : List Elim} (hs : SemSpine W c T es c' C) :
    PosOK W c T → ∀ s, Elim.term s ∈ es → SN W s := by
  induction hs with
  | nil => intro _ s h; simp at h
  | @term c₀ c₁ T₁ T₂ C₀ s₀ es₀ hsT _ ih =>
    intro hok s h
    rcases List.mem_cons.mp h with h' | h'
    · injection h' with h'; subst h'
      have hT₁ : TyWf c₀.Ψ c₀.Θ 0 0 T₁ := by cases hok.2.2.2 with | arr h _ => exact h
      exact (interp_closed_mem hW hT₁ c₀.ρ hok.2.2.1 _ _ hsT).2
    · exact ih hok.term s h'
  | proj hd hj hβ _ ih =>
    intro hok s h
    rcases List.mem_cons.mp h with h' | h'
    · cases h'
    · exact ih (hok.proj hd hj hβ) s h'
  | instT hX h𝒳 _ ih =>
    intro hok s h
    rcases List.mem_cons.mp h with h' | h'
    · cases h'
    · exact ih (hok.instT h𝒳) s h'
  | instS hj hβ _ ih =>
    intro hok s h
    rcases List.mem_cons.mp h with h' | h'
    · cases h'
    · exact ih (hok.instS hj hβ) s h'

theorem spineStep_length {W : World} {es es' : List Elim} (h : SpineStep W es es') :
    es'.length = es.length := by
  induction h with
  | here => rfl
  | there _ ih => simp [ih]

theorem appSpine_head_not_intro {h : Tm} (hh : IsHead h) (es : List Elim) :
    ¬ IsIntro (Tm.appSpine h es) := by
  intro hi
  cases es using List.reverseRecOn with
  | nil => cases h <;> simp_all [IsHead, IsIntro]
  | append_singleton es e => simp [IsIntro] at hi

/-- The clause-head lemma. `hshape` says that a clause longer than the spine whose copatterns do
not yet mismatch it only occurs at elimination types; it follows from clause typing
(`spine_shape`). At all other types a stuck clause-headed term is neutral. -/
theorem clause_head {W : World} (hW : WorldClosed W) {h : Tm} {D : List Clause} (hh : IsHead h)
    (hclosed : h.Closed)
    (hsel : ∀ es, headStep W (Tm.appSpine h es) = selectClause D es)
    {c : SCtx} {A : Ty} (hok : PosOK W c A)
    (hsound : ∀ es u c' C, SemSpine W c A es c' C → selectClause D es = some u →
      u ∈ c'.den W C)
    (hshape : ∀ es c' C, SemSpine W c A es c' C → ∀ qs t, Clause.mk qs t ∈ D →
      es.length < qs.length → matchSpine qs es ≠ .no → IsElimTy C) :
    ∀ es c' C, SemSpine W c A es c' C → Tm.appSpine h es ∈ c'.den W C := by
  suffices H : ∀ n es c' C, maxLen D - es.length = n → SemSpine W c A es c' C →
      Tm.appSpine h es ∈ c'.den W C by
    intro es c' C hs; exact H _ es c' C rfl hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro es c' C hn hs
  have hacc := spineStep_acc es (semSpine_args_sn hW hs hok)
  induction hacc generalizing c' C with
  | intro es _ ihacc =>
  have hpos := semSpine_posOK hs hok
  have hcand : Cand W (c'.den W C) := interp_cand_closed hW hpos.2.2.2 c'.ρ hpos.2.2.1
  have htc : (Tm.appSpine h es).Closed := by
    unfold Tm.Closed
    rw [Tm.fv_appSpine, hclosed, semSpine_closed hW hs hok]
    rfl
  have hni := appSpine_head_not_intro hh es
  have hred : ∀ t', Step W (Tm.appSpine h es) t' →
      (selectClause D es = some t') ∨ (∃ es', SpineStep W es es' ∧ t' = Tm.appSpine h es') := by
    intro t' hst
    rcases step_appSpine_head hh es t' hst with h' | h'
    · left; rw [← hsel]; exact h'
    · right; exact h'
  have hIH : ∀ es', SpineStep W es es' → Tm.appSpine h es' ∈ c'.den W C := by
    intro es' hst
    have hs' := semSpine_spineStep hW hs hok es' hst
    exact ihacc es' hst c' C (by rw [spineStep_length hst]; exact hn) hs'
  cases hselc : selectClause D es with
  | some u =>
    have hu := hsound es u c' C hs hselc
    apply hcand.neutral _ htc (neutral_of_headStep (by rw [hsel]; exact hselc))
    intro t' hst
    rcases hred t' hst with h' | ⟨es', hst', rfl⟩
    · rw [hselc] at h'; cases h'; exact hu
    · exact hIH es' hst'
  | none =>
    by_cases hlong : ∀ qs t, Clause.mk qs t ∈ D → es.length < qs.length →
        matchSpine qs es = .no
    · apply hcand.neutral _ htc
      · apply neutral_of_stuck hni
        intro es₂
        rw [← Tm.appSpine_append, hsel]
        exact selectClause_append_none hlong hselc es₂
      · intro t' hst
        rcases hred t' hst with h' | ⟨es', hst', rfl⟩
        · rw [hselc] at h'; cases h'
        · exact hIH es' hst'
    · push_neg at hlong
      obtain ⟨qs, t, hmem, hlt, hne⟩ := hlong
      have helim := hshape es c' C hs qs t hmem hlt hne
      have hL : es.length < maxLen D :=
        lt_of_lt_of_le hlt (le_maxLen (cl := .mk qs t) hmem)
      have hsn : SN W (Tm.appSpine h es) := SN.of_reducts fun t' hst => by
        rcases hred t' hst with h' | ⟨es', hst', rfl⟩
        · rw [hselc] at h'; cases h'
        · exact (hcand.sn _ (hIH es' hst')).2
      have hlt' : maxLen D - (es.length + 1) < n := by omega
      cases C with
      | arr C₁ C₂ =>
        simp only [SCtx.den, interp]
        refine ⟨⟨htc, hsn⟩, fun s hsC => ?_⟩
        have hs'' := semSpine_snoc hs (.term hsC (.nil _ _))
        have := ihn _ hlt' (es ++ [.term s]) c' C₂ (by simp) hs''
        simpa [SCtx.den] using this
      | nu a R =>
        simp only [SCtx.den, interp]
        rw [NuSet_eq]
        refine ⟨⟨htc, hsn⟩, fun β hβ d hd => ?_⟩
        obtain ⟨j, hj⟩ := exists_fresh c'.Ψ.dom
        have hdR : R[d]? = some R[d] := List.getElem?_eq_getElem hd
        have hs'' := semSpine_snoc hs (.proj hdR hj hβ (.nil _ _))
        have := ihn _ hlt' (es ++ [.proj d]) _ _ (by simp) hs''
        simp only [SCtx.den, SCtx.extSz] at this
        rw [interp_unfold_nu_fresh hpos.2.2.2 hj hdR β] at this
        simpa using this
      | allT B =>
        simp only [SCtx.den, interp]
        refine ⟨⟨htc, hsn⟩, fun 𝒳 h𝒳 => ?_⟩
        obtain ⟨X, hX⟩ := exists_fresh c'.Θ
        have hB : TyWf c'.Ψ c'.Θ 1 0 B := by cases hpos.2.2.2 with | allT h => exact h
        have hs'' := semSpine_snoc hs (.instT hX h𝒳 (.nil _ _))
        have := ihn _ hlt' (es ++ [.inst]) _ _ (by simp) hs''
        simp only [SCtx.den, SCtx.extTy] at this
        rw [interp_open_fresh_ty hB hX] at this
        simpa using this
      | allS a B =>
        simp only [SCtx.den, interp]
        refine ⟨⟨htc, hsn⟩, fun β hβ => ?_⟩
        obtain ⟨j, hj⟩ := exists_fresh c'.Ψ.dom
        have hB : TyWf c'.Ψ c'.Θ 0 1 B := by cases hpos.2.2.2 with | allS _ h => exact h
        have hs'' := semSpine_snoc hs (.instS hj hβ (.nil _ _))
        have := ihn _ hlt' (es ++ [.inst]) _ _ (by simp) hs''
        simp only [SCtx.den, SCtx.extSz] at this
        rw [interp_open_fresh_sz hB hj] at this
        simpa using this
      | unit => simp [IsElimTy] at helim
      | prod _ _ => simp [IsElimTy] at helim
      | var _ => simp [IsElimTy] at helim
      | fvar _ => simp [IsElimTy] at helim
      | mu _ _ => simp [IsElimTy] at helim
      | exT _ => simp [IsElimTy] at helim
      | exS _ _ => simp [IsElimTy] at helim

end NishtAbel2024V4
