import Solutions.V3.Spine
import Mathlib.Data.Fintype.Card

/-! # V3: soundness of clause-headed terms -/

namespace NishtAbel2024V3

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
theorem semSpine_spineStep {W : World} (hW : WorldClosed W) {Ψ Ψ' : SizeCtx} {ρ ρ' : SizeVal}
    {T C : Ty} {es : List Elim} (hs : SemSpine W Ψ ρ T es Ψ' ρ' C) :
    PosOK Ψ ρ T → ∀ es', SpineStep W es es' → SemSpine W Ψ ρ T es' Ψ' ρ' C := by
  induction hs with
  | nil => intro _ es' h; cases h
  | @term Ψ Ψ' ρ ρ' T₁ T₂ C s es hsT hs' ih =>
    intro hok es' h
    cases h with
    | here hss =>
      have hT₁ : TyWf Ψ 0 T₁ := by cases hok.2.2 with | arr h _ => exact h
      have hcand := interp_cand hW ρ hT₁ Env.empty (fun _ h => absurd h (Nat.not_lt_zero _))
      exact .term (hcand.red _ hsT _ hss) hs'
    | there h => exact .term hsT (ih hok.term _ h)
  | proj hd hj hβ hs' ih =>
    intro hok es' h
    cases h with
    | there h => exact .proj hd hj hβ (ih (hok.proj hd hj hβ) _ h)

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

theorem selectClause_append_none {D : List Clause} {es : List Elim} (hlen : maxLen D ≤ es.length)
    (h : selectClause D es = none) (es₂ : List Elim) : selectClause D (es ++ es₂) = none := by
  induction D with
  | nil => rfl
  | cons cl D ih =>
    obtain ⟨qs, t⟩ := cl
    have hq : qs.length ≤ es.length :=
      le_trans (le_maxLen (D := Clause.mk qs t :: D) (cl := Clause.mk qs t) (by simp)) hlen
    have hD : maxLen D ≤ es.length := by
      simp only [maxLen, List.foldr_cons] at hlen
      exact le_trans (le_max_right _ _) hlen
    simp only [selectClause] at h ⊢
    rw [matchSpine_append_of_le qs es es₂ hq]
    cases hm : matchSpine qs es with
    | yes σ => rw [hm] at h; simp at h
    | no => rw [hm] at h; exact ih hD h
    | stuck => rfl

theorem exists_fresh (l : List Nat) : ∃ j, j ∉ l := by
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset l.toFinset
  exact ⟨j, by simpa using hj⟩

theorem interp_intro_of_reducts {W : World} {Ψ : SizeCtx} {ρ : SizeVal} {C : Ty}
    (hC : TyWf Ψ 0 C) (hnot : ∀ A B, C ≠ .arr A B) (hnot' : ∀ a R, C ≠ .nu a R) {t : Tm}
    (hc : t.Closed) (hi : ¬ IsIntro t) (h : ∀ t', Step W t t' → t' ∈ interp W ρ C Env.empty) :
    t ∈ interp W ρ C Env.empty := by
  cases C with
  | unit => exact introSet_of_reducts hc hi h
  | prod A B => exact introSet_of_reducts hc hi h
  | mu a S =>
    simp only [interp] at h ⊢
    rw [MuSet_eq] at h ⊢
    exact introSet_of_reducts hc hi h
  | arr A B => exact absurd rfl (hnot A B)
  | nu a R => exact absurd rfl (hnot' a R)
  | var X => cases hC with | var h => exact absurd h (Nat.not_lt_zero _)

theorem semSpine_args_sn {W : World} (hW : WorldClosed W) {Ψ Ψ' : SizeCtx} {ρ ρ' : SizeVal}
    {T C : Ty} {es : List Elim} (hs : SemSpine W Ψ ρ T es Ψ' ρ' C) :
    PosOK Ψ ρ T → ∀ s, Elim.term s ∈ es → SN W s := by
  induction hs with
  | nil => intro _ s h; simp at h
  | @term Ψ₀ Ψ₁ ρ₀ ρ₁ T₁ T₂ C₀ s₀ es₀ hsT _ ih =>
    intro hok s h
    rcases List.mem_cons.mp h with h' | h'
    · injection h' with h'; subst h'
      have hT₁ : TyWf Ψ₀ 0 T₁ := by cases hok.2.2 with | arr h _ => exact h
      exact (interp_closed_mem hW hT₁ ρ₀ hsT).2
    · exact ih hok.term s h'
  | proj hd hj hβ _ ih =>
    intro hok s h
    rcases List.mem_cons.mp h with h' | h'
    · cases h'
    · exact ih (hok.proj hd hj hβ) s h'

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

/-- The clause-head lemma. -/
theorem clause_head {W : World} (hW : WorldClosed W) {h : Tm} {D : List Clause} (hh : IsHead h)
    (hclosed : h.Closed)
    (hsel : ∀ es, headStep W (Tm.appSpine h es) = selectClause D es)
    {Ψ : SizeCtx} {ρ : SizeVal} {A : Ty} (hok : PosOK Ψ ρ A)
    (hsound : ∀ es u Ψ' ρ' C, SemSpine W Ψ ρ A es Ψ' ρ' C → selectClause D es = some u →
      u ∈ interp W ρ' C Env.empty) :
    ∀ es Ψ' ρ' C, SemSpine W Ψ ρ A es Ψ' ρ' C → Tm.appSpine h es ∈ interp W ρ' C Env.empty := by
  suffices H : ∀ n es Ψ' ρ' C, maxLen D - es.length = n → SemSpine W Ψ ρ A es Ψ' ρ' C →
      Tm.appSpine h es ∈ interp W ρ' C Env.empty by
    intro es Ψ' ρ' C hs; exact H _ es Ψ' ρ' C rfl hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro es Ψ' ρ' C hn hs
  have hacc := spineStep_acc es (semSpine_args_sn hW hs hok)
  induction hacc generalizing Ψ' ρ' C with
  | intro es _ ihacc =>
  have hpos := (semSpine_posOK hs hok).1
  have hcand := interp_cand hW ρ' hpos.2.2 Env.empty (fun _ h => absurd h (Nat.not_lt_zero _))
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
  have hIH : ∀ es', SpineStep W es es' → Tm.appSpine h es' ∈ interp W ρ' C Env.empty := by
    intro es' hst
    have hs' := semSpine_spineStep hW hs hok es' hst
    exact ihacc es' hst Ψ' ρ' C (by rw [spineStep_length hst]; exact hn) hs'
  cases hselc : selectClause D es with
  | some u =>
    have hu := hsound es u Ψ' ρ' C hs hselc
    apply hcand.neutral _ htc (neutral_of_headStep (by rw [hsel]; exact hselc))
    intro t' hst
    rcases hred t' hst with h' | ⟨es', hst', rfl⟩
    · rw [hselc] at h'; cases h'; exact hu
    · exact hIH es' hst'
  | none =>
    by_cases hL : maxLen D ≤ es.length
    · apply hcand.neutral _ htc
      · apply neutral_of_stuck hni
        intro es₂
        rw [← Tm.appSpine_append, hsel]
        exact selectClause_append_none hL hselc es₂
      · intro t' hst
        rcases hred t' hst with h' | ⟨es', hst', rfl⟩
        · rw [hselc] at h'; cases h'
        · exact hIH es' hst'
    · have hsn : SN W (Tm.appSpine h es) := SN.of_reducts fun t' hst => by
        rcases hred t' hst with h' | ⟨es', hst', rfl⟩
        · rw [hselc] at h'; cases h'
        · exact (hcand.sn _ (hIH es' hst')).2
      have hlt : maxLen D - (es.length + 1) < n := by omega
      cases C with
      | arr C₁ C₂ =>
        refine ⟨⟨htc, hsn⟩, fun s hsC => ?_⟩
        have hs'' := semSpine_snoc hs (.term hsC (.nil _ _ _))
        have := ihn _ hlt (es ++ [.term s]) Ψ' ρ' C₂ (by simp) hs''
        simpa using this
      | nu a R =>
        simp only [interp]
        rw [NuSet_eq]
        refine ⟨⟨htc, hsn⟩, fun β hβ d hd => ?_⟩
        obtain ⟨j, hj⟩ := exists_fresh Ψ'.dom
        have hdR : R[d]? = some R[d] := List.getElem?_eq_getElem hd
        have hs'' := semSpine_snoc hs (.proj hdR hj hβ (.nil _ _ _))
        have := ihn _ hlt (es ++ [.proj d]) _ _ _ (by simp) hs''
        rw [interp_unfold_nu_fresh hpos.2.2 hj hdR β] at this
        simpa using this
      | unit =>
        apply interp_intro_of_reducts hpos.2.2 (by intro _ _ h; cases h) (by intro _ _ h; cases h)
          htc hni
        intro t' hst
        rcases hred t' hst with h' | ⟨es', hst', rfl⟩
        · rw [hselc] at h'; cases h'
        · exact hIH es' hst'
      | prod A B =>
        apply interp_intro_of_reducts hpos.2.2 (by intro _ _ h; cases h) (by intro _ _ h; cases h)
          htc hni
        intro t' hst
        rcases hred t' hst with h' | ⟨es', hst', rfl⟩
        · rw [hselc] at h'; cases h'
        · exact hIH es' hst'
      | mu a S =>
        apply interp_intro_of_reducts hpos.2.2 (by intro _ _ h; cases h) (by intro _ _ h; cases h)
          htc hni
        intro t' hst
        rcases hred t' hst with h' | ⟨es', hst', rfl⟩
        · rw [hselc] at h'; cases h'
        · exact hIH es' hst'
      | var X =>
        exfalso
        cases hpos.2.2 with | var h => exact Nat.not_lt_zero _ h

end NishtAbel2024V3
