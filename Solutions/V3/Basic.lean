import Definitions.Def_NishtAbel2024V3_Semantics

/-! # V3 basics: spines, matching, determinism of head steps -/

namespace NishtAbel2024V3

namespace Tm

@[simp] theorem appSpine_nil (r : Tm) : appSpine r [] = r := rfl

@[simp] theorem appSpine_cons (r : Tm) (e : Elim) (es : List Elim) :
    appSpine r (e :: es) = appSpine (.app r e) es := rfl

theorem appSpine_append (r : Tm) (es es' : List Elim) :
    appSpine r (es ++ es') = appSpine (appSpine r es) es' := by
  simp [appSpine, List.foldl_append]

@[simp] theorem appSpine_snoc (r : Tm) (es : List Elim) (e : Elim) :
    appSpine r (es ++ [e]) = .app (appSpine r es) e := by
  rw [appSpine_append]; rfl

theorem headSpine_appSpine (r : Tm) (es : List Elim) :
    (appSpine r es).headSpine = (r.headSpine.1, r.headSpine.2 ++ es) := by
  induction es generalizing r with
  | nil => simp
  | cons e es ih =>
    rw [appSpine_cons, ih]
    simp [headSpine]

end Tm

/-! ## Matching -/

theorem MatchRes.and_eq_yes {m₁ m₂ : MatchRes} {σ : TmSubst} (h : m₁.and m₂ = .yes σ) :
    ∃ σ₁ σ₂, m₁ = .yes σ₁ ∧ m₂ = .yes σ₂ ∧ σ = σ₁ ++ σ₂ := by
  cases m₁ <;> cases m₂ <;> simp_all [MatchRes.and]

theorem MatchRes.and_no_left (m : MatchRes) : MatchRes.and .no m = .no := by
  cases m <;> rfl

theorem MatchRes.and_no_right (m : MatchRes) : m.and .no = .no := by
  cases m <;> rfl

theorem matchSpine_yes_length {qs : List Copat} {es : List Elim} {σ : TmSubst}
    (h : matchSpine qs es = .yes σ) : qs.length ≤ es.length := by
  induction qs generalizing es σ with
  | nil => simp
  | cons q qs ih =>
    cases es with
    | nil => simp [matchSpine] at h
    | cons e es =>
      obtain ⟨_, σ₂, _, h₂, _⟩ := MatchRes.and_eq_yes h
      simpa using ih h₂

theorem matchSpine_append_yes {qs : List Copat} {es : List Elim} {σ : TmSubst}
    (h : matchSpine qs es = .yes σ) (es' : List Elim) :
    matchSpine qs (es ++ es') = .yes σ := by
  induction qs generalizing es σ with
  | nil => simpa [matchSpine] using h
  | cons q qs ih =>
    cases es with
    | nil => simp [matchSpine] at h
    | cons e es =>
      simp only [matchSpine, List.cons_append] at h ⊢
      obtain ⟨σ₁, σ₂, h₁, h₂, rfl⟩ := MatchRes.and_eq_yes h
      rw [h₁, ih h₂]
      rfl

theorem matchSpine_append_no {qs : List Copat} {es : List Elim}
    (h : matchSpine qs es = .no) (es' : List Elim) :
    matchSpine qs (es ++ es') = .no := by
  induction qs generalizing es with
  | nil => simp [matchSpine] at h
  | cons q qs ih =>
    cases es with
    | nil => simp [matchSpine] at h
    | cons e es =>
      simp only [matchSpine, List.cons_append] at h ⊢
      cases hq : matchCopat q e with
      | no => rfl
      | yes σ =>
        rw [hq] at h
        cases hm : matchSpine qs es with
        | no => rw [ih hm]; rfl
        | yes _ => rw [hm] at h; simp [MatchRes.and] at h
        | stuck => rw [hm] at h; simp [MatchRes.and] at h
      | stuck =>
        rw [hq] at h
        cases hm : matchSpine qs es with
        | no => rw [ih hm]; rfl
        | yes _ => rw [hm] at h; simp [MatchRes.and] at h
        | stuck => rw [hm] at h; simp [MatchRes.and] at h

theorem selectClause_append {D : List Clause} {es : List Elim} {u : Tm}
    (h : selectClause D es = some u) (es' : List Elim) :
    selectClause D (es ++ es') = some (Tm.appSpine u es') := by
  induction D with
  | nil => simp [selectClause] at h
  | cons cl D ih =>
    obtain ⟨qs, t⟩ := cl
    simp only [selectClause] at h ⊢
    cases hm : matchSpine qs es with
    | yes σ =>
      rw [hm] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [matchSpine_append_yes hm]
      simp only [Option.some.injEq]
      rw [List.drop_append_of_le_length (matchSpine_yes_length hm), Tm.appSpine_append]
    | no =>
      rw [hm] at h
      rw [matchSpine_append_no hm]
      exact ih h
    | stuck => rw [hm] at h; simp at h

/-! ## Head steps -/

theorem headStep_appSpine {W : World} {t u : Tm} (h : headStep W t = some u) (es : List Elim) :
    headStep W (Tm.appSpine t es) = some (Tm.appSpine u es) := by
  unfold headStep at h ⊢
  rw [Tm.headSpine_appSpine]
  generalize t.headSpine = p at h ⊢
  obtain ⟨hd, sp⟩ := p
  simp only at h ⊢
  cases hd with
  | lam D => exact selectClause_append h es
  | fn f =>
    cases hl : W.lookup f with
    | none => simp [hl] at h
    | some d =>
      simp only [hl] at h ⊢
      exact selectClause_append h es
  | _ => simp at h

theorem headStep_intro {W : World} {t : Tm} (h : IsIntro t) : headStep W t = none := by
  cases t <;> simp_all [IsIntro, headStep, Tm.headSpine]

theorem not_intro_of_headStep {W : World} {t u : Tm} (h : headStep W t = some u) : ¬ IsIntro t := by
  intro hi
  rw [headStep_intro hi] at h
  cases h

/-- A term with a head step is neutral. -/
theorem neutral_of_headStep {W : World} {t u : Tm} (h : headStep W t = some u) :
    IsNeutral W t := by
  refine ⟨not_intro_of_headStep h, ?_⟩
  intro es u' h'
  refine ⟨u, h, ?_⟩
  rw [headStep_appSpine h es] at h'
  cases h'
  rfl

/-- A term none of whose extensions has a head step is neutral. -/
theorem neutral_of_stuck {W : World} {t : Tm} (hi : ¬ IsIntro t)
    (h : ∀ es, headStep W (Tm.appSpine t es) = none) : IsNeutral W t := by
  refine ⟨hi, ?_⟩
  intro es u hu
  rw [h es] at hu
  cases hu

/-- Neutrality is preserved by adding eliminations. -/
theorem neutral_app {W : World} {t : Tm} (h : IsNeutral W t) (e : Elim) :
    IsNeutral W (.app t e) := by
  refine ⟨by simp [IsIntro], ?_⟩
  intro es u hu
  have hu' : headStep W (Tm.appSpine t (e :: es)) = some u := hu
  obtain ⟨t', ht', rfl⟩ := h.2 _ _ hu'
  refine ⟨.app t' e, ?_, rfl⟩
  have := headStep_appSpine ht' [e]
  simpa using this

end NishtAbel2024V3
