import Solutions.V3.Wf

/-! # V3: semantic contexts, subtyping soundness, pattern matching soundness -/

namespace NishtAbel2024V3

/-- `σ ∈ ⟦Γ⟧ρ`: every variable of `Γ` is bound by `σ` to a member of its type, and all values of
`σ` are closed. -/
def SemCtx (W : World) (ρ : SizeVal) (Γ : TermCtx) (σ : TmSubst) : Prop :=
  (∀ x A, Γ.lookup x = some A → ∃ v, σ.lookup x = some v ∧ v ∈ interp W ρ A Env.empty) ∧
  (∀ x v, σ.lookup x = some v → v.Closed)

/-- Every bound of the context is well-formed in the context. -/
def CtxBoundsWf (Ψ : SizeCtx) : Prop := ∀ p ∈ Ψ, SizeWf Ψ p.2

/-- Every type in the context is closed and well-formed. -/
def TermCtxWf (Ψ : SizeCtx) (Γ : TermCtx) : Prop := ∀ p ∈ Γ, TyWf Ψ 0 p.2

theorem interp_closed_mem {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {A : Ty}
    (hA : TyWf Ψ 0 A) (ρ : SizeVal) {v : Tm} (hv : v ∈ interp W ρ A Env.empty) : SNc W v :=
  (interp_cand hW ρ hA Env.empty (fun _ h => absurd h (Nat.not_lt_zero _))).sn v hv

/-! ## Subtyping -/

theorem subTy_sound {W : World} {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {A B : Ty}
    (h : SubTy Ψ A B) : ∀ η, interp W ρ A η ⊆ interp W ρ B η := by
  induction h with
  | refl _ => intro _; exact le_rfl
  | prod _ _ ihA ihB => intro η; exact prodSet_mono (ihA η) (ihB η)
  | arr _ _ ihA ihB => intro η; exact arrSet_mono (ihA η) (ihB η)
  | mu hab => intro η; exact muSet_mono_ord (sizeLe_sound hv hab)
  | nu hba => intro η; exact nuSet_anti_ord (sizeLe_sound hv hba)
  | trans _ _ ih₁ ih₂ => intro η; exact (ih₁ η).trans (ih₂ η)

/-! ## Valuation updates -/

def SizeVal.update (ρ : SizeVal) (j : Nat) (β : Ordinal.{0}) : SizeVal :=
  fun i => if i = j then β else ρ i

theorem SizeVal.update_agree {ρ : SizeVal} {j : Nat} {β : Ordinal.{0}} {Ψ : SizeCtx}
    (hj : j ∉ Ψ.dom) : ∀ i ∈ Ψ.dom, SizeVal.update ρ j β i = ρ i := by
  intro i hi
  have : i ≠ j := fun h => hj (h ▸ hi)
  simp [SizeVal.update, this]

theorem ValidVal.agree {Ψ : SizeCtx} {ρ ρ' : SizeVal} (hv : ValidVal Ψ ρ) (hb : CtxBoundsWf Ψ)
    (hag : ∀ i ∈ Ψ.dom, ρ' i = ρ i) : ValidVal Ψ ρ' := by
  intro p hp
  have hi : p.1 ∈ Ψ.dom := SizeCtx.mem_dom (a := p.2) (by simpa using hp)
  rw [hag _ hi, sizeVal_agree (fun i h => hag i h) (hb p hp)]
  exact hv p hp

theorem ValidVal.extend {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) (hb : CtxBoundsWf Ψ)
    {j : Nat} (hj : j ∉ Ψ.dom) {a : Size} (ha : SizeWf Ψ a) {β : Ordinal.{0}}
    (hβ : β < sizeVal ρ a) :
    ValidVal (Ψ ++ [(j, a)]) (SizeVal.update ρ j β) := by
  have hag := SizeVal.update_agree (ρ := ρ) (β := β) hj
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact (hv.agree hb hag) p hp
  · simp at hp; subst hp
    simp only [SizeVal.update, if_true]
    rw [sizeVal_agree hag ha]
    exact ⟨hβ, lt_of_lt_of_le hβ (sizeVal_le_omega hv ha)⟩

theorem CtxBoundsWf.extend {Ψ : SizeCtx} (hb : CtxBoundsWf Ψ) {j : Nat} {a : Size}
    (ha : SizeWf Ψ a) : CtxBoundsWf (Ψ ++ [(j, a)]) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact (hb p hp).weaken dom_append_left
  · simp at hp; subst hp; exact ha.weaken dom_append_left

/-! ## Facts about pattern typing -/

theorem patTy_dom {Ψ : SizeCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
    (h : PatTy Ψ p A Γ Ψ') : Γ.map Prod.fst = p.vars := by
  induction h with
  | var => rfl
  | unit => rfl
  | pair _ _ ih₁ ih₂ => simp [Pat.vars, ih₁, ih₂]
  | cons _ _ _ ih => simpa [Pat.vars] using ih

theorem patTy_ctx {Ψ : SizeCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
    (h : PatTy Ψ p A Γ Ψ') : TyWf Ψ 0 A → CtxBoundsWf Ψ →
      TermCtxWf (Ψ ++ Ψ') Γ ∧ CtxBoundsWf (Ψ ++ Ψ') := by
  induction h with
  | var Ψ x A =>
    intro hA hb
    refine ⟨?_, by simpa using hb⟩
    intro q hq; simp at hq; subst hq; simpa using hA
  | unit Ψ => intro _ hb; exact ⟨by simp [TermCtxWf], by simpa using hb⟩
  | @pair Ψ Ψ₁ Ψ₂ p q A B Γ₁ Γ₂ _ _ ih₁ ih₂ =>
    intro hAB hb
    cases hAB with
    | prod hA hB =>
      obtain ⟨hΓ₁, hb₁⟩ := ih₁ hA hb
      obtain ⟨hΓ₂, hb₂⟩ := ih₂ (hB.weaken _ _ dom_append_left le_rfl) hb₁
      refine ⟨?_, by simpa using hb₂⟩
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · have := hΓ₁ r hr
        have h' := this.weaken (Ψ ++ Ψ₁ ++ Ψ₂) 0 dom_append_left le_rfl
        simpa using h'
      · simpa using hΓ₂ r hr
  | @cons Ψ Ψ' c j p a S Sc Γ hc hj _ ih =>
    intro hA hb
    have ha : SizeWf Ψ a := by cases hA with | mu ha _ _ => exact ha
    have hA' : TyWf (Ψ ++ [(j, a)]) 0 (.mu a S) := hA.weaken _ _ dom_append_left le_rfl
    have hunf := hA'.unfold_mu (b := .var j 0) hc (by simp [SizeWf, SizeCtx.dom])
    obtain ⟨hΓ, hb'⟩ := ih hunf (hb.extend ha)
    exact ⟨by simpa using hΓ, by simpa using hb'⟩

/-! ## Semantic contexts -/

theorem SemCtx.nil (W : World) (ρ : SizeVal) : SemCtx W ρ [] [] :=
  ⟨by simp, by simp⟩

theorem lookup_none_of_not_mem {σ : TmSubst} {x : Nat} (h : x ∉ σ.map Prod.fst) :
    σ.lookup x = none := by
  cases hl : σ.lookup x with
  | none => rfl
  | some v => exact absurd (List.mem_map.mpr ⟨(x, v), lookup_mem hl, rfl⟩) h

theorem lookup_none_of_not_mem_ctx {Γ : TermCtx} {x : Nat} (h : Γ.lookup x = none) :
    x ∉ Γ.map Prod.fst := by
  intro hx
  obtain ⟨⟨y, A⟩, hm, rfl⟩ := List.mem_map.mp hx
  induction Γ with
  | nil => simp at hm
  | cons q Γ ih =>
    obtain ⟨z, B⟩ := q
    rw [List.lookup_cons] at h
    by_cases hyz : y = z
    · subst hyz; simp at h
    · have : (y == z) = false := beq_eq_false_iff_ne.mpr hyz
      simp only [this] at h
      rcases List.mem_cons.mp hm with hm | hm
      · simp at hm; exact hyz hm.1
      · exact ih hm h (List.mem_map.mpr ⟨(y, A), hm, rfl⟩)

/-- Joining semantic contexts for disjoint parts of a pattern. -/
theorem SemCtx.append {W : World} {ρ : SizeVal} {Γ₁ Γ₂ : TermCtx} {σ₁ σ₂ : TmSubst}
    (h₁ : SemCtx W ρ Γ₁ σ₁) (h₂ : SemCtx W ρ Γ₂ σ₂) (hdom : σ₁.map Prod.fst = Γ₁.map Prod.fst) :
    SemCtx W ρ (Γ₁ ++ Γ₂) (σ₁ ++ σ₂) := by
  refine ⟨?_, ?_⟩
  · intro x A hx
    rw [List.lookup_append] at hx ⊢
    cases hΓ : Γ₁.lookup x with
    | some B =>
      rw [hΓ] at hx; simp at hx; subst hx
      obtain ⟨v, hv, hmem⟩ := h₁.1 x _ hΓ
      exact ⟨v, by simp [hv], hmem⟩
    | none =>
      rw [hΓ] at hx; simp at hx
      have : σ₁.lookup x = none := by
        apply lookup_none_of_not_mem
        rw [hdom]
        exact lookup_none_of_not_mem_ctx hΓ
      obtain ⟨v, hv, hmem⟩ := h₂.1 x _ hx
      exact ⟨v, by simp [this, hv], hmem⟩
  · intro x v hx
    rw [List.lookup_append] at hx
    cases h : σ₁.lookup x with
    | some w => rw [h] at hx; simp at hx; subst hx; exact h₁.2 x _ h
    | none => rw [h] at hx; simp at hx; exact h₂.2 x _ hx

/-- Transport of a semantic context to a valuation agreeing on the relevant size variables. -/
theorem SemCtx.agree {W : World} {Ψ : SizeCtx} {Γ : TermCtx} (hΓ : TermCtxWf Ψ Γ) {ρ ρ' : SizeVal}
    (hag : ∀ i ∈ Ψ.dom, ρ i = ρ' i) {σ : TmSubst} (h : SemCtx W ρ Γ σ) : SemCtx W ρ' Γ σ := by
  refine ⟨?_, h.2⟩
  intro x A hx
  obtain ⟨v, hv, hmem⟩ := h.1 x A hx
  refine ⟨v, hv, ?_⟩
  have hA : TyWf Ψ 0 A := hΓ (x, A) (lookup_mem' hx)
  rwa [← interp_agree hA ρ ρ' _ _ hag (fun _ h => absurd h (Nat.not_lt_zero _))]
where
  lookup_mem' {Γ : TermCtx} {x : Nat} {A : Ty} (h : Γ.lookup x = some A) : (x, A) ∈ Γ := by
    induction Γ with
    | nil => simp at h
    | cons q Γ ih =>
      obtain ⟨y, B⟩ := q
      rw [List.lookup_cons] at h
      by_cases hxy : x = y
      · subst hxy; simp at h; subst h; simp
      · have : (x == y) = false := beq_eq_false_iff_ne.mpr hxy
        simp only [this] at h
        exact List.mem_cons_of_mem _ (ih h)

/-! ## Pattern matching soundness -/

theorem pat_sound {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {p : Pat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} (hp : PatTy Ψ p A Γ Ψ') :
    ∀ (ρ : SizeVal) (v : Tm) (σm : TmSubst), ValidVal Ψ ρ → CtxBoundsWf Ψ → TyWf Ψ 0 A →
      v ∈ interp W ρ A Env.empty → matchPat p v = .yes σm →
      ∃ ρ', ValidVal (Ψ ++ Ψ') ρ' ∧ (∀ i ∈ Ψ.dom, ρ' i = ρ i) ∧ SemCtx W ρ' Γ σm := by
  induction hp with
  | var Ψ x A =>
    intro ρ v σm hv _ hA hmem hm
    simp [matchPat] at hm; subst hm
    refine ⟨ρ, by simpa using hv, fun _ _ => rfl, ?_, ?_⟩
    · intro y B hy
      rw [lookup_cons_ty] at hy
      by_cases hyx : y = x
      · simp [hyx] at hy; subst hy; subst hyx
        exact ⟨v, by simp, hmem⟩
      · simp [hyx] at hy
    · intro y w hy
      rw [lookup_cons_eq] at hy
      by_cases hyx : y = x
      · simp [hyx] at hy; subst hy; exact (interp_closed_mem hW hA ρ hmem).1
      · simp [hyx] at hy
  | unit Ψ =>
    intro ρ v σm hv _ _ _ hm
    cases v <;> simp [matchPat] at hm
    subst hm
    exact ⟨ρ, by simpa using hv, fun _ _ => rfl, SemCtx.nil W ρ⟩
  | @pair Ψ Ψ₁ Ψ₂ p q A B Γ₁ Γ₂ hp₁ hp₂ ih₁ ih₂ =>
    intro ρ v σm hv hb hAB hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i t u
    obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
    have hA : TyWf Ψ 0 A := by cases hAB with | prod h _ => exact h
    have hB : TyWf Ψ 0 B := by cases hAB with | prod _ h => exact h
    simp only [interp] at hmem
    obtain ⟨t', u', heq, ht, hu⟩ := introSet_of_intro hmem (by simp [IsIntro])
    cases heq
    obtain ⟨ρ₁, hv₁, hag₁, hs₁⟩ := ih₁ ρ t σ₁ hv hb hA ht hm₁
    have hb₁ := (patTy_ctx hp₁ hA hb).2
    have hB₁ : TyWf (Ψ ++ Ψ₁) 0 B := hB.weaken _ _ dom_append_left le_rfl
    have hu₁ : u ∈ interp W ρ₁ B Env.empty := by
      rwa [interp_agree hB ρ₁ ρ _ _ hag₁ (fun _ h => absurd h (Nat.not_lt_zero _))]
    obtain ⟨ρ₂, hv₂, hag₂, hs₂⟩ := ih₂ ρ₁ u σ₂ hv₁ hb₁ hB₁ hu₁ hm₂
    refine ⟨ρ₂, by simpa using hv₂, ?_, ?_⟩
    · intro i hi
      rw [hag₂ i (dom_append_left i hi), hag₁ i hi]
    · have hΓ₁ := (patTy_ctx hp₁ hA hb).1
      have hs₁' := hs₁.agree hΓ₁ (fun i hi => (hag₂ i hi).symm)
      apply hs₁'.append hs₂
      rw [(matchPat_facts p t σ₁ hm₁).1, patTy_dom hp₁]
  | @cons Ψ Ψ' c j p a S Sc Γ hc hj hp' ih =>
    intro ρ v σm hv hb hA hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i c' t
    by_cases hcc : c = c'
    · simp [hcc] at hm
      subst hcc
      have ha : SizeWf Ψ a := by cases hA with | mu ha _ _ => exact ha
      have hS : ∀ T ∈ S, TyWf Ψ 1 T := by cases hA with | mu _ hS _ => exact hS
      simp only [interp] at hmem
      rw [MuSet_eq] at hmem
      obtain ⟨c₀, t₀, β, hβ, heq, ht⟩ := introSet_of_intro hmem (by simp [IsIntro])
      cases heq
      have hcl : c < S.length := (List.getElem?_eq_some_iff.mp hc).1
      have hScEq : S[c] = Sc := (List.getElem?_eq_some_iff.mp hc).2
      set ρ₁ := SizeVal.update ρ j β with hρ₁
      have hag : ∀ i ∈ Ψ.dom, ρ₁ i = ρ i := SizeVal.update_agree hj
      have hv₁ := hv.extend hb hj ha hβ
      have hb₁ := hb.extend (j := j) ha
      have hA' : TyWf (Ψ ++ [(j, a)]) 0 (.mu a S) := hA.weaken _ _ dom_append_left le_rfl
      have hwfj : TyWf (Ψ ++ [(j, a)]) 0 (.mu (.var j 0) S) := by
        cases hA' with
        | mu _ hS' hpos => exact .mu (by simp [SizeWf, SizeCtx.dom]) hS' hpos
      have hunf := hA'.unfold_mu (b := .var j 0) hc (by simp [SizeWf, SizeCtx.dom])
      have ht' : t ∈ interp W ρ₁ (Sc.substTy 0 (.mu (.var j 0) S)) Env.empty := by
        rw [← hScEq, interp_unfold_mu hcl hwfj]
        have hval : sizeVal ρ₁ (.var j 0) = β := by simp [sizeVal, hρ₁, SizeVal.update]
        rw [hval]
        have hF : (fun c 𝒳 => interpAt W ρ₁ S c (Env.cons 𝒳 Env.empty)) =
            (fun c 𝒳 => interpAt W ρ S c (Env.cons 𝒳 Env.empty)) := by
          funext c 𝒳
          by_cases hc' : c < S.length
          · rw [interpAt_eq W ρ₁ S c _ hc', interpAt_eq W ρ S c _ hc']
            exact interp_agree (hS _ (List.getElem_mem hc')) ρ₁ ρ _ _ hag (fun _ _ => rfl)
          · rw [interpAt_out W ρ₁ S c _ (by omega), interpAt_out W ρ S c _ (by omega)]
        rw [hF, interpAt_eq W ρ₁ S c _ hcl,
          interp_agree (hS _ (List.getElem_mem hcl)) ρ₁ ρ _ _ hag (fun _ _ => rfl),
          ← interpAt_eq W ρ S c _ hcl]
        exact ht
      obtain ⟨ρ', hv', hag', hs'⟩ := ih ρ₁ t σm hv₁ hb₁ hunf ht' hm
      refine ⟨ρ', by simpa using hv', ?_, hs'⟩
      intro i hi
      rw [hag' i (dom_append_left i hi), hag i hi]
    · simp [hcc] at hm
where
  lookup_cons_ty (k x : Nat) (b : Ty) (l : TermCtx) :
      ((k, b) :: l).lookup x = if x = k then some b else l.lookup x := by
    rw [List.lookup_cons]
    by_cases h : x = k
    · subst h; simp
    · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr h
      simp [hb, h]

end NishtAbel2024V3
