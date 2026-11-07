import Solutions.V5.ClauseHead

/-! # V5: auxiliary lemmas for the fundamental lemma -/

namespace NishtAbel2024V5

open NishtAbel2024V2 (InvGraph ConformsToGraph)

theorem step_pair_inv {W : World} {t u v : Tm} (h : Step W (.pair t u) v) :
    (∃ t', Step W t t' ∧ v = .pair t' u) ∨ (∃ u', Step W u u' ∧ v = .pair t u') := by
  cases h with
  | head hh => rw [headStep_intro (by simp [IsIntro])] at hh; cases hh
  | pairL h => exact Or.inl ⟨_, h, rfl⟩
  | pairR h => exact Or.inr ⟨_, h, rfl⟩

theorem step_cons_inv {W : World} {c : Nat} {t v : Tm} (h : Step W (.cons c t) v) :
    ∃ t', Step W t t' ∧ v = .cons c t' := by
  cases h with
  | head hh => rw [headStep_intro (by simp [IsIntro])] at hh; cases hh
  | cons h => exact ⟨_, h, rfl⟩

theorem step_unit_inv {W : World} {v : Tm} (h : Step W .unit v) : False := by
  cases h with
  | head hh => rw [headStep_intro (by simp [IsIntro])] at hh; cases hh

theorem steps_pair_inv {W : World} {t u v : Tm} (h : Steps W (.pair t u) v) :
    ∃ t' u', v = .pair t' u' ∧ Steps W t t' ∧ Steps W u u' := by
  induction h with
  | refl => exact ⟨t, u, rfl, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨t', u', rfl, ht, hu⟩ := ih
    rcases step_pair_inv hs with ⟨t'', h, rfl⟩ | ⟨u'', h, rfl⟩
    · exact ⟨t'', u', rfl, ht.tail h, hu⟩
    · exact ⟨t', u'', rfl, ht, hu.tail h⟩

theorem steps_cons_inv {W : World} {c : Nat} {t v : Tm} (h : Steps W (.cons c t) v) :
    ∃ t', v = .cons c t' ∧ Steps W t t' := by
  induction h with
  | refl => exact ⟨t, rfl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨t', rfl, ht⟩ := ih
    obtain ⟨t'', h, rfl⟩ := step_cons_inv hs
    exact ⟨t'', rfl, ht.tail h⟩

theorem steps_unit_inv {W : World} {v : Tm} (h : Steps W .unit v) : v = .unit := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [ih] at hs; exact (step_unit_inv hs).elim

theorem SN.pair {W : World} {t u : Tm} (ht : SN W t) (hu : SN W u) : SN W (.pair t u) := by
  induction ht generalizing u with
  | intro t _ iht =>
    induction hu with
    | intro u hu' ihu =>
      refine SN.of_reducts fun v hv => ?_
      rcases step_pair_inv hv with ⟨t', h, rfl⟩ | ⟨u', h, rfl⟩
      · exact iht t' h (Acc.intro u hu')
      · exact ihu u' h

theorem SN.cons {W : World} {c : Nat} {t : Tm} (ht : SN W t) : SN W (.cons c t) := by
  induction ht with
  | intro t _ ih =>
    refine SN.of_reducts fun v hv => ?_
    obtain ⟨t', h, rfl⟩ := step_cons_inv hv
    exact ih t' h

theorem SN.unit (W : World) : SN W .unit := SN.of_reducts fun _ h => (step_unit_inv h).elim

theorem step_pack_inv {W : World} {t v : Tm} (h : Step W (.pack t) v) :
    ∃ t', Step W t t' ∧ v = .pack t' := by
  cases h with
  | head hh => rw [headStep_intro (by simp [IsIntro])] at hh; cases hh
  | pack h => exact ⟨_, h, rfl⟩

theorem steps_pack_inv {W : World} {t v : Tm} (h : Steps W (.pack t) v) :
    ∃ t', v = .pack t' ∧ Steps W t t' := by
  induction h with
  | refl => exact ⟨t, rfl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨t', rfl, ht⟩ := ih
    obtain ⟨t'', h, rfl⟩ := step_pack_inv hs
    exact ⟨t'', rfl, ht.tail h⟩

theorem SN.pack {W : World} {t : Tm} (ht : SN W t) : SN W (.pack t) := by
  induction ht with
  | intro t _ ih =>
    refine SN.of_reducts fun v hv => ?_
    obtain ⟨t', h, rfl⟩ := step_pack_inv hv
    exact ih t' h

theorem conforms_map {S T : Type} {lt₁ le₁ : S → S → Prop} {lt₂ le₂ : T → T → Prop}
    {G : InvGraph} {xs ys : List S} (f : S → T)
    (hlt : ∀ x y, lt₁ x y → lt₂ (f x) (f y)) (hle : ∀ x y, le₁ x y → le₂ (f x) (f y))
    (h : ConformsToGraph lt₁ le₁ G xs ys) : ConformsToGraph lt₂ le₂ G (xs.map f) (ys.map f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simpa using h1, by simpa using h2, ?_⟩
  intro i j hi hj
  have hi' : i < xs.length := by simpa using hi
  have hj' : j < ys.length := by simpa using hj
  obtain ⟨a, b⟩ := h3 i j hi' hj'
  exact ⟨fun e => by simpa using hlt _ _ (a e), fun e => by simpa using hle _ _ (b e)⟩

theorem selectClause_inv {D : List Clause} {es : List Elim} {u : Tm} (h : selectClause D es = some u) :
    ∃ qs t σm, Clause.mk qs t ∈ D ∧ matchSpine qs es = .yes σm ∧
      u = Tm.appSpine (t.subst σm) (es.drop qs.length) := by
  induction D with
  | nil => simp [selectClause] at h
  | cons cl D ih =>
    obtain ⟨qs, t⟩ := cl
    simp only [selectClause] at h
    cases hm : matchSpine qs es with
    | yes σ =>
      rw [hm] at h; simp at h
      exact ⟨qs, t, σ, by simp, hm, h.symm⟩
    | no =>
      rw [hm] at h
      obtain ⟨qs', t', σ', hmem, hm', hu⟩ := ih h
      exact ⟨qs', t', σ', List.mem_cons_of_mem _ hmem, hm', hu⟩
    | stuck => rw [hm] at h; simp at h

theorem mem_substList {σ : TmSubst} {D : List Clause} {qs : List Copat} {t : Tm}
    (h : Clause.mk qs t ∈ Clause.substList σ D) :
    ∃ t₀, Clause.mk qs t₀ ∈ D ∧ t = t₀.subst (σ.filter (fun p => decide (p.1 ∉ spineVars qs))) := by
  induction D with
  | nil => simp [Clause.substList] at h
  | cons cl D ih =>
    obtain ⟨qs', t'⟩ := cl
    simp only [Clause.substList, List.mem_cons] at h
    rcases h with h | h
    · cases h; exact ⟨t', by simp, rfl⟩
    · obtain ⟨t₀, hm, rfl⟩ := ih h; exact ⟨t₀, List.mem_cons_of_mem _ hm, rfl⟩

theorem matchSpine_take {qs : List Copat} {es : List Elim} {σ : TmSubst}
    (h : matchSpine qs es = .yes σ) : matchSpine qs (es.take qs.length) = .yes σ := by
  have hlen := matchSpine_yes_length h
  have := matchSpine_append_of_le qs (es.take qs.length) (es.drop qs.length)
    (by simp [List.length_take]; omega)
  rw [List.take_append_drop] at this
  rw [← this]; exact h

theorem spineTy_dom {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ' : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty} (h : SpineTy Ψ Θ qs A Γ' Ψ' Θ' C) :
    Γ'.map Prod.fst = spineVars qs := by
  induction h with
  | nil => rfl
  | pat hp _ ih =>
    rw [List.map_append, patTy_dom hp, ih]
    simp [spineVars, Copat.vars]
  | proj _ _ _ ih => simpa [spineVars, Copat.vars] using ih
  | instT _ _ ih => simpa [spineVars, Copat.vars] using ih
  | instS _ _ ih => simpa [spineVars, Copat.vars] using ih

theorem headStep_lam (W : World) (D : List Clause) (es : List Elim) :
    headStep W (Tm.appSpine (.lam D) es) = selectClause D es := by
  unfold headStep
  rw [Tm.headSpine_appSpine]
  simp [Tm.headSpine]

theorem headStep_fn {W : World} {f : NishtAbel2024V2.FunName} {d : FunDecl}
    (h : W.lookup f = some d) (es : List Elim) :
    headStep W (Tm.appSpine (.fn f) es) = selectClause d.clauses es := by
  unfold headStep
  rw [Tm.headSpine_appSpine]
  simp [Tm.headSpine, h]

/-! ## Free variables of typed terms -/

theorem mem_dom_of_lookup {Γ : TermCtx} {x : Nat} {A : Ty} (h : Γ.lookup x = some A) :
    x ∈ Γ.map Prod.fst := by
  by_contra hn
  have := lookup_none_of_not_mem (σ := Γ.map (fun p => (p.1, Tm.unit))) (x := x) (by simpa using hn)
  induction Γ with
  | nil => simp at h
  | cons q Γ ih =>
    obtain ⟨y, B⟩ := q
    rw [List.lookup_cons] at h
    by_cases hxy : x = y
    · exact hn (by simp [hxy])
    · have hb : (x == y) = false := beq_eq_false_iff_ne.mpr hxy
      simp only [hb] at h
      exact ih h (fun h' => hn (List.mem_cons_of_mem _ h')) (by
        simp only [List.map_cons] at this
        rw [lookup_cons_eq] at this
        simpa [hxy] using this)

theorem clauses_fv_of {Γ : TermCtx} : ∀ (D : List Clause),
    (∀ cl ∈ D, ∀ x ∈ Clause.fvList [cl], x ∈ Γ.map Prod.fst) →
      ∀ x ∈ Clause.fvList D, x ∈ Γ.map Prod.fst
  | [], _, x, hx => by simp [Clause.fvList] at hx
  | .mk qs t :: D, ih, x, hx => by
    simp only [Clause.fvList, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ih (.mk qs t) (by simp) x (by simp [Clause.fvList]; simpa using hx)
    · exact clauses_fv_of D (fun cl h => ih cl (List.mem_cons_of_mem _ h)) x hx

theorem exprTy_fv {Ω : TypingEnv} {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {t : Tm} {A : Ty}
    (h : ExprTy Ω Ψ Θ Γ t A) : ∀ x ∈ t.fv, x ∈ Γ.map Prod.fst := by
  refine ExprTy.rec (motive_1 := fun _ _ Γ t _ _ => ∀ x ∈ t.fv, x ∈ Γ.map Prod.fst)
    (motive_2 := fun _ _ Γ cl _ _ => ∀ x ∈ Clause.fvList [cl], x ∈ Γ.map Prod.fst)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro Ψ Θ Γ x A hx y hy
    simp [Tm.fv] at hy; subst hy; exact mem_dom_of_lookup hx
  · intro Ψ Θ Γ y hy; simp [Tm.fv] at hy
  · intro Ψ Θ Γ t u A B _ _ ih₁ ih₂ y hy
    simp only [Tm.fv, List.mem_append] at hy
    rcases hy with hy | hy
    · exact ih₁ y hy
    · exact ih₂ y hy
  · intro Ψ Θ Γ c t a b S Sc _ _ _ _ ih y hy
    exact ih y (by simpa [Tm.fv] using hy)
  · intro Ψ Θ Γ r s A B _ _ ih₁ ih₂ y hy
    simp only [Tm.fv, Elim.fv, List.mem_append] at hy
    rcases hy with hy | hy
    · exact ih₁ y hy
    · exact ih₂ y hy
  · intro Ψ Θ Γ r a b R d Rd _ _ _ ih y hy
    simp only [Tm.fv, Elim.fv, List.append_nil] at hy
    exact ih y hy
  · intro Ψ Θ Γ r κ B T _ _ ih y hy
    simp only [Tm.fv, Elim.fv, List.append_nil] at hy
    exact ih y hy
  · intro Ψ Θ Γ r a b B _ _ ih y hy
    simp only [Tm.fv, Elim.fv, List.append_nil] at hy
    exact ih y hy
  · intro Ψ Θ Γ t κ B T _ _ _ ih y hy
    simp only [Tm.fv] at hy
    exact ih y hy
  · intro Ψ Θ Γ t a b B _ _ _ ih y hy
    simp only [Tm.fv] at hy
    exact ih y hy
  · intro Ψ Θ Γ D A _ _ ih y hy
    simp only [Tm.fv] at hy
    exact clauses_fv_of D ih y hy
  · intro Ψ Θ Γ g as _ _ _ _ _ y hy; simp [Tm.fv] at hy
  · intro Ψ Θ Γ g as _ _ _ _ _ _ y hy; simp [Tm.fv] at hy
  · intro Ψ Θ Γ t A B _ _ _ ih y hy; exact ih y hy
  · intro Ψ Ψ' Θ Θ' Γ Γ' qs t A C hsp _ ih y hy
    simp only [Clause.fvList, List.append_nil, List.mem_filter, decide_eq_true_eq] at hy
    have := ih y hy.1
    simp only [List.map_append, List.mem_append] at this
    rcases this with h' | h'
    · rw [spineTy_dom hsp] at h'; exact absurd h' hy.2
    · exact h'

end NishtAbel2024V5
