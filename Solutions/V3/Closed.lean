import Solutions.V3.Basic

/-! # V3: free variables, closed substitution, closedness of reducts -/

namespace NishtAbel2024V3

/-! ## Association-list lookups -/

theorem lookup_cons_eq (k x : Nat) (b : Tm) (l : TmSubst) :
    ((k, b) :: l).lookup x = if x = k then some b else l.lookup x := by
  rw [List.lookup_cons]
  by_cases h : x = k
  · subst h; simp
  · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]

theorem lookup_filter_not_mem (σ : TmSubst) (L : List Nat) (x : Nat) :
    (σ.filter (fun p => decide (p.1 ∉ L))).lookup x = if x ∈ L then none else σ.lookup x := by
  induction σ with
  | nil => simp
  | cons p σ ih =>
    obtain ⟨y, v⟩ := p
    by_cases hy : y ∈ L
    · rw [List.filter_cons_of_neg (by simpa using hy), ih, lookup_cons_eq]
      by_cases hx : x ∈ L
      · simp [hx]
      · have : x ≠ y := fun h => hx (h ▸ hy)
        simp [hx, this]
    · rw [List.filter_cons_of_pos (by simpa using hy), lookup_cons_eq, lookup_cons_eq, ih]
      by_cases hx : x ∈ L
      · have : x ≠ y := fun h => hy (h ▸ hx)
        simp [hx, this]
      · simp [hx]

theorem lookup_isSome_of_mem {σ : TmSubst} {x : Nat} (h : x ∈ σ.map Prod.fst) :
    ∃ v, σ.lookup x = some v := by
  induction σ with
  | nil => simp at h
  | cons p σ ih =>
    obtain ⟨y, v⟩ := p
    rw [lookup_cons_eq]
    by_cases hx : x = y
    · exact ⟨v, by simp [hx]⟩
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h hx
      · simpa [hx] using ih h

theorem lookup_mem {σ : TmSubst} {x : Nat} {v : Tm} (h : σ.lookup x = some v) : (x, v) ∈ σ := by
  induction σ with
  | nil => simp at h
  | cons p σ ih =>
    obtain ⟨y, w⟩ := p
    rw [lookup_cons_eq] at h
    by_cases hx : x = y
    · simp [hx] at h; subst hx; subst h; simp
    · simp [hx] at h; exact List.mem_cons_of_mem _ (ih h)

/-! ## Substitution -/

mutual

theorem Tm.subst_congr {σ σ' : TmSubst} (h : ∀ x, σ.lookup x = σ'.lookup x) :
    ∀ t : Tm, t.subst σ = t.subst σ'
  | .var x => by simp only [Tm.subst, h x]
  | .fn _ => rfl
  | .app r e => by simp only [Tm.subst]; rw [Tm.subst_congr h r, Elim.subst_congr h e]
  | .unit => rfl
  | .pair t u => by simp only [Tm.subst]; rw [Tm.subst_congr h t, Tm.subst_congr h u]
  | .cons c t => by simp only [Tm.subst]; rw [Tm.subst_congr h t]
  | .lam D => by simp only [Tm.subst]; rw [Clause.substList_congr h D]

theorem Elim.subst_congr {σ σ' : TmSubst} (h : ∀ x, σ.lookup x = σ'.lookup x) :
    ∀ e : Elim, e.subst σ = e.subst σ'
  | .term t => by simp only [Elim.subst]; rw [Tm.subst_congr h t]
  | .proj _ => rfl

theorem Clause.substList_congr {σ σ' : TmSubst} (h : ∀ x, σ.lookup x = σ'.lookup x) :
    ∀ D : List Clause, Clause.substList σ D = Clause.substList σ' D
  | [] => rfl
  | .mk qs t :: D => by
    simp only [Clause.substList]
    rw [Tm.subst_congr (σ := σ.filter (fun p => decide (p.1 ∉ spineVars qs)))
        (σ' := σ'.filter (fun p => decide (p.1 ∉ spineVars qs)))
        (fun x => by simp only [lookup_filter_not_mem, h x]) t,
      Clause.substList_congr h D]

end

mutual

theorem Tm.subst_of_fv {σ : TmSubst} :
    ∀ t : Tm, (∀ x ∈ t.fv, σ.lookup x = none) → t.subst σ = t
  | .var x, h => by simp [Tm.subst, h x (by simp [Tm.fv])]
  | .fn _, _ => rfl
  | .app r e, h => by
    simp only [Tm.subst]
    rw [Tm.subst_of_fv r (fun x hx => h x (by simp [Tm.fv, hx])),
      Elim.subst_of_fv e (fun x hx => h x (by simp [Tm.fv, hx]))]
  | .unit, _ => rfl
  | .pair t u, h => by
    simp only [Tm.subst]
    rw [Tm.subst_of_fv t (fun x hx => h x (by simp [Tm.fv, hx])),
      Tm.subst_of_fv u (fun x hx => h x (by simp [Tm.fv, hx]))]
  | .cons c t, h => by
    simp only [Tm.subst]
    rw [Tm.subst_of_fv t (fun x hx => h x (by simp [Tm.fv, hx]))]
  | .lam D, h => by
    simp only [Tm.subst]
    rw [Clause.substList_of_fv D (fun x hx => h x (by simpa [Tm.fv] using hx))]

theorem Elim.subst_of_fv {σ : TmSubst} :
    ∀ e : Elim, (∀ x ∈ e.fv, σ.lookup x = none) → e.subst σ = e
  | .term t, h => by simp only [Elim.subst]; rw [Tm.subst_of_fv t (fun x hx => h x hx)]
  | .proj _, _ => rfl

theorem Clause.substList_of_fv {σ : TmSubst} :
    ∀ D : List Clause, (∀ x ∈ Clause.fvList D, σ.lookup x = none) → Clause.substList σ D = D
  | [], _ => rfl
  | .mk qs t :: D, h => by
    simp only [Clause.substList]
    rw [Tm.subst_of_fv t (fun x hx => by
        rw [lookup_filter_not_mem]
        by_cases hm : x ∈ spineVars qs
        · simp [hm]
        · simp only [hm, if_false]
          exact h x (by simp [Clause.fvList, hx, hm])),
      Clause.substList_of_fv D (fun x hx => h x (by simp [Clause.fvList, hx]))]

end

theorem Tm.subst_closed {t : Tm} (h : t.Closed) (σ : TmSubst) : t.subst σ = t :=
  Tm.subst_of_fv t (fun x hx => by simp [Tm.Closed] at h; simp [h] at hx)

/-! Composition, when the first substitution has closed values. -/

mutual

theorem Tm.subst_subst {σ₁ σ₂ : TmSubst} (hc : ∀ x v, σ₁.lookup x = some v → v.Closed) :
    ∀ t : Tm, (t.subst σ₁).subst σ₂ = t.subst (σ₁ ++ σ₂)
  | .var x => by
    cases h : σ₁.lookup x with
    | none => simp [Tm.subst, h, List.lookup_append]
    | some v => simp [Tm.subst, h, List.lookup_append, Tm.subst_closed (hc x v h)]
  | .fn _ => rfl
  | .app r e => by simp only [Tm.subst]; rw [Tm.subst_subst hc r, Elim.subst_subst hc e]
  | .unit => rfl
  | .pair t u => by simp only [Tm.subst]; rw [Tm.subst_subst hc t, Tm.subst_subst hc u]
  | .cons c t => by simp only [Tm.subst]; rw [Tm.subst_subst hc t]
  | .lam D => by simp only [Tm.subst]; rw [Clause.substList_subst hc D]

theorem Elim.subst_subst {σ₁ σ₂ : TmSubst} (hc : ∀ x v, σ₁.lookup x = some v → v.Closed) :
    ∀ e : Elim, (e.subst σ₁).subst σ₂ = e.subst (σ₁ ++ σ₂)
  | .term t => by simp only [Elim.subst]; rw [Tm.subst_subst hc t]
  | .proj _ => rfl

theorem Clause.substList_subst {σ₁ σ₂ : TmSubst} (hc : ∀ x v, σ₁.lookup x = some v → v.Closed) :
    ∀ D : List Clause, Clause.substList σ₂ (Clause.substList σ₁ D) = Clause.substList (σ₁ ++ σ₂) D
  | [] => rfl
  | .mk qs t :: D => by
    simp only [Clause.substList]
    have hc' : ∀ x v, (σ₁.filter (fun p => decide (p.1 ∉ spineVars qs))).lookup x = some v →
        v.Closed := by
      intro x v h
      rw [lookup_filter_not_mem] at h
      by_cases hm : x ∈ spineVars qs
      · simp [hm] at h
      · simp only [hm, if_false] at h; exact hc x v h
    rw [Tm.subst_subst hc' t, List.filter_append, Clause.substList_subst hc D]

end

/-! ## Free variables of substitutions -/

mutual

theorem Tm.fv_subst {σ : TmSubst} (hc : ∀ x v, σ.lookup x = some v → v.Closed) :
    ∀ t : Tm, ∀ x ∈ (t.subst σ).fv, x ∈ t.fv ∧ σ.lookup x = none
  | .var y, x, hx => by
    cases h : σ.lookup y with
    | none =>
      simp [Tm.subst, h, Tm.fv] at hx
      subst hx; exact ⟨by simp [Tm.fv], h⟩
    | some v =>
      have hv := hc y v h
      simp [Tm.Closed] at hv
      simp [Tm.subst, h, hv] at hx
  | .fn _, x, hx => by simp [Tm.subst, Tm.fv] at hx
  | .app r e, x, hx => by
    simp only [Tm.subst, Tm.fv, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨h1, h2⟩ := Tm.fv_subst hc r x hx; exact ⟨by simp [Tm.fv, h1], h2⟩
    · obtain ⟨h1, h2⟩ := Elim.fv_subst hc e x hx; exact ⟨by simp [Tm.fv, h1], h2⟩
  | .unit, x, hx => by simp [Tm.subst, Tm.fv] at hx
  | .pair t u, x, hx => by
    simp only [Tm.subst, Tm.fv, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨h1, h2⟩ := Tm.fv_subst hc t x hx; exact ⟨by simp [Tm.fv, h1], h2⟩
    · obtain ⟨h1, h2⟩ := Tm.fv_subst hc u x hx; exact ⟨by simp [Tm.fv, h1], h2⟩
  | .cons c t, x, hx => by
    simp only [Tm.subst, Tm.fv] at hx
    obtain ⟨h1, h2⟩ := Tm.fv_subst hc t x hx; exact ⟨by simp [Tm.fv, h1], h2⟩
  | .lam D, x, hx => by
    simp only [Tm.subst, Tm.fv] at hx ⊢
    exact Clause.fvList_subst hc D x hx

theorem Elim.fv_subst {σ : TmSubst} (hc : ∀ x v, σ.lookup x = some v → v.Closed) :
    ∀ e : Elim, ∀ x ∈ (e.subst σ).fv, x ∈ e.fv ∧ σ.lookup x = none
  | .term t, x, hx => Tm.fv_subst hc t x hx
  | .proj _, x, hx => by simp [Elim.subst, Elim.fv] at hx

theorem Clause.fvList_subst {σ : TmSubst} (hc : ∀ x v, σ.lookup x = some v → v.Closed) :
    ∀ D : List Clause, ∀ x ∈ Clause.fvList (Clause.substList σ D),
      x ∈ Clause.fvList D ∧ σ.lookup x = none
  | [], x, hx => by simp [Clause.substList, Clause.fvList] at hx
  | .mk qs t :: D, x, hx => by
    simp only [Clause.substList, Clause.fvList, List.mem_append, List.mem_filter,
      decide_eq_true_eq] at hx
    rcases hx with ⟨hx, hm⟩ | hx
    · have hc' : ∀ x v, (σ.filter (fun p => decide (p.1 ∉ spineVars qs))).lookup x = some v →
          v.Closed := by
        intro x v h
        rw [lookup_filter_not_mem] at h
        by_cases hm : x ∈ spineVars qs
        · simp [hm] at h
        · simp only [hm, if_false] at h; exact hc x v h
      obtain ⟨h1, h2⟩ := Tm.fv_subst hc' t x hx
      rw [lookup_filter_not_mem] at h2
      simp only [hm, if_false] at h2
      exact ⟨by simp [Clause.fvList, h1, hm], h2⟩
    · obtain ⟨h1, h2⟩ := Clause.fvList_subst hc D x hx
      exact ⟨by simp [Clause.fvList, h1], h2⟩

end

/-- Substituting closed values for all free variables gives a closed term. -/
theorem Tm.closed_subst {σ : TmSubst} {t : Tm} (hc : ∀ x v, σ.lookup x = some v → v.Closed)
    (hcov : ∀ x ∈ t.fv, ∃ v, σ.lookup x = some v) : (t.subst σ).Closed := by
  unfold Tm.Closed
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨h1, h2⟩ := Tm.fv_subst hc t x hx
  obtain ⟨v, hv⟩ := hcov x h1
  rw [hv] at h2; cases h2

end NishtAbel2024V3
