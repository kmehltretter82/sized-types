import Solutions.V5.Closed

/-! # V5: matching facts and closedness of reducts -/

namespace NishtAbel2024V5

open NishtAbel2024V2 (FunName)

theorem Tm.fv_appSpine (r : Tm) (es : List Elim) :
    (Tm.appSpine r es).fv = r.fv ++ es.flatMap Elim.fv := by
  induction es generalizing r with
  | nil => simp
  | cons e es ih => simp [ih, Tm.fv, List.append_assoc]

theorem Tm.appSpine_headSpine : ∀ t : Tm, Tm.appSpine t.headSpine.1 t.headSpine.2 = t
  | .app r e => by
    simp only [Tm.headSpine]
    rw [Tm.appSpine_snoc, Tm.appSpine_headSpine r]
  | .var _ => rfl
  | .fn _ => rfl
  | .unit => rfl
  | .pair _ _ => rfl
  | .cons _ _ => rfl
  | .pack _ => rfl
  | .lam _ => rfl

/-- Facts about a successful match: its domain, and free variables of its values. -/
def MatchFacts (σ : TmSubst) (vars : List Nat) (fvs : List Nat) : Prop :=
  σ.map Prod.fst = vars ∧ ∀ q ∈ σ, ∀ x ∈ q.2.fv, x ∈ fvs

theorem MatchFacts.append {σ₁ σ₂ : TmSubst} {v₁ v₂ f₁ f₂ : List Nat}
    (h₁ : MatchFacts σ₁ v₁ f₁) (h₂ : MatchFacts σ₂ v₂ f₂) :
    MatchFacts (σ₁ ++ σ₂) (v₁ ++ v₂) (f₁ ++ f₂) := by
  refine ⟨by simp [h₁.1, h₂.1], ?_⟩
  intro q hq x hx
  rcases List.mem_append.mp hq with hq | hq
  · exact List.mem_append_left _ (h₁.2 q hq x hx)
  · exact List.mem_append_right _ (h₂.2 q hq x hx)

theorem matchPat_facts : ∀ (p : Pat) (v : Tm) (σ : TmSubst),
    matchPat p v = .yes σ → MatchFacts σ p.vars v.fv
  | .var x, v, σ, h => by
    simp [matchPat] at h; subst h
    exact ⟨by simp [Pat.vars], by simp⟩
  | .unit, v, σ, h => by
    cases v <;> simp [matchPat] at h
    subst h; exact ⟨by simp [Pat.vars], by simp⟩
  | .pair p q, v, σ, h => by
    cases v <;> simp [matchPat] at h
    rename_i t u
    obtain ⟨σ₁, σ₂, h₁, h₂, rfl⟩ := MatchRes.and_eq_yes h
    have := (matchPat_facts p t σ₁ h₁).append (matchPat_facts q u σ₂ h₂)
    simpa [Pat.vars, Tm.fv] using this
  | .cons c p, v, σ, h => by
    cases v <;> simp [matchPat] at h
    rename_i c' t
    by_cases hc : c = c'
    · simp [hc] at h
      have := matchPat_facts p t σ h
      simpa [Pat.vars, Tm.fv] using this
    · simp [hc] at h
  | .pack p, v, σ, h => by
    cases v <;> simp [matchPat] at h
    rename_i t
    have := matchPat_facts p t σ h
    simpa [Pat.vars, Tm.fv] using this

theorem matchCopat_facts : ∀ (q : Copat) (e : Elim) (σ : TmSubst),
    matchCopat q e = .yes σ → MatchFacts σ q.vars e.fv
  | .pat p, .term t, σ, h => by
    simpa [Copat.vars, Elim.fv] using matchPat_facts p t σ h
  | .pat _, .proj _, σ, h => by simp [matchCopat] at h
  | .proj d, .proj d', σ, h => by
    by_cases hd : d = d'
    · simp [matchCopat, hd] at h; subst h; exact ⟨by simp [Copat.vars], by simp⟩
    · simp [matchCopat, hd] at h
  | .proj _, .term _, σ, h => by simp [matchCopat] at h
  | .pat _, .inst, σ, h => by simp [matchCopat] at h
  | .proj _, .inst, σ, h => by simp [matchCopat] at h
  | .inst, .inst, σ, h => by
    simp [matchCopat] at h; subst h; exact ⟨by simp [Copat.vars], by simp⟩
  | .inst, .term _, σ, h => by simp [matchCopat] at h
  | .inst, .proj _, σ, h => by simp [matchCopat] at h

theorem matchSpine_facts : ∀ (qs : List Copat) (es : List Elim) (σ : TmSubst),
    matchSpine qs es = .yes σ → MatchFacts σ (spineVars qs) (es.flatMap Elim.fv)
  | [], es, σ, h => by
    simp [matchSpine] at h; subst h; exact ⟨by simp [spineVars], by simp⟩
  | _ :: _, [], σ, h => by simp [matchSpine] at h
  | q :: qs, e :: es, σ, h => by
    simp only [matchSpine] at h
    obtain ⟨σ₁, σ₂, h₁, h₂, rfl⟩ := MatchRes.and_eq_yes h
    have := (matchCopat_facts q e σ₁ h₁).append (matchSpine_facts qs es σ₂ h₂)
    simpa [spineVars] using this

/-- Elimination spines with no free variables. -/
def ElimsClosed (es : List Elim) : Prop := es.flatMap Elim.fv = []

theorem selectClause_closed {D : List Clause} {es : List Elim} {u : Tm}
    (hD : Clause.fvList D = []) (hes : ElimsClosed es) (h : selectClause D es = some u) :
    u.Closed := by
  induction D with
  | nil => simp [selectClause] at h
  | cons cl D ih =>
    obtain ⟨qs, t⟩ := cl
    simp only [Clause.fvList, List.append_eq_nil_iff] at hD
    simp only [selectClause] at h
    cases hm : matchSpine qs es with
    | yes σ =>
      rw [hm] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hdom, hfv⟩ := matchSpine_facts qs es σ hm
      have hc : ∀ x v, σ.lookup x = some v → v.Closed := by
        intro x v hx
        have hmem := lookup_mem hx
        unfold Tm.Closed
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro y hy
        have := hfv _ hmem y hy
        simp only [ElimsClosed, List.flatMap_eq_nil_iff] at hes
        simp only [List.mem_flatMap] at this
        obtain ⟨a, ha, hya⟩ := this
        rw [hes a ha] at hya
        simp at hya
      have hbody : (t.subst σ).Closed := by
        apply Tm.closed_subst hc
        intro x hx
        apply lookup_isSome_of_mem
        rw [hdom]
        by_contra hn
        have : x ∈ t.fv.filter (fun x => decide (x ∉ spineVars qs)) := by simp [hx, hn]
        rw [hD.1] at this; simp at this
      unfold Tm.Closed
      rw [Tm.fv_appSpine, hbody]
      simp only [List.nil_append]
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      simp only [List.mem_flatMap] at hx
      obtain ⟨e, he, hxe⟩ := hx
      have : x ∈ es.flatMap Elim.fv := List.mem_flatMap.mpr ⟨e, List.mem_of_mem_drop he, hxe⟩
      rw [hes] at this; simp at this
    | no => rw [hm] at h; exact ih hD.2 h
    | stuck => rw [hm] at h; simp at h

/-- Clause bodies of all declarations are closed. -/
def WorldClosed (W : World) : Prop := ∀ d ∈ W, (Tm.lam d.clauses).Closed

theorem World.lookup_mem {W : World} {f : FunName} {d : FunDecl} (h : W.lookup f = some d) :
    d ∈ W := List.mem_of_find?_eq_some h

theorem headStep_closed {W : World} (hW : WorldClosed W) {t u : Tm} (ht : t.Closed)
    (h : headStep W t = some u) : u.Closed := by
  have hsplit := Tm.appSpine_headSpine t
  have hfv : t.fv = t.headSpine.1.fv ++ t.headSpine.2.flatMap Elim.fv := by
    conv_lhs => rw [← hsplit]
    rw [Tm.fv_appSpine]
  have hall : t.headSpine.1.fv ++ t.headSpine.2.flatMap Elim.fv = [] := by
    rw [← hfv]; exact ht
  rw [List.append_eq_nil_iff] at hall
  unfold headStep at h
  generalize hp : t.headSpine = p at h hall
  obtain ⟨hd, sp⟩ := p
  simp only at h hall
  cases hd with
  | lam D =>
    exact selectClause_closed (by simpa [Tm.fv] using hall.1) hall.2 h
  | fn f =>
    cases hl : W.lookup f with
    | none => simp [hl] at h
    | some d =>
      simp only [hl] at h
      have := hW d (World.lookup_mem hl)
      exact selectClause_closed (by simpa [Tm.Closed, Tm.fv] using this) hall.2 h
  | _ => simp at h

theorem step_closed {W : World} (hW : WorldClosed W) {t u : Tm} (h : Step W t u) (ht : t.Closed) :
    u.Closed := by
  induction h with
  | head hs => exact headStep_closed hW ht hs
  | appFun _ ih =>
    simp [Tm.Closed, Tm.fv] at ht ⊢
    exact ⟨ih ht.1, ht.2⟩
  | appArg _ ih =>
    simp [Tm.Closed, Tm.fv, Elim.fv] at ht ⊢
    exact ⟨ht.1, ih ht.2⟩
  | pairL _ ih =>
    simp [Tm.Closed, Tm.fv] at ht ⊢
    exact ⟨ih ht.1, ht.2⟩
  | pairR _ ih =>
    simp [Tm.Closed, Tm.fv] at ht ⊢
    exact ⟨ht.1, ih ht.2⟩
  | cons _ ih =>
    simp [Tm.Closed, Tm.fv] at ht ⊢
    exact ih ht
  | pack _ ih =>
    simp [Tm.Closed, Tm.fv] at ht ⊢
    exact ih ht

theorem steps_closed {W : World} (hW : WorldClosed W) {t u : Tm} (h : Steps W t u) (ht : t.Closed) :
    u.Closed := by
  induction h with
  | refl => exact ht
  | tail _ hs ih => exact step_closed hW hs ih

end NishtAbel2024V5
