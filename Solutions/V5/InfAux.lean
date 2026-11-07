import Solutions.V5.InfPat

/-! # V5 inference: auxiliary facts about encodings, scopes and composed substitutions -/

namespace NishtAbel2024V5

/-! ## Well-formed sizes in larger contexts -/

theorem SizesWf.mono {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A) {Ψ' : SizeCtx}
    (hΨ : ∀ i ∈ Ψ.dom, i ∈ Ψ'.dom) : SizesWf Ψ' m A := by
  induction h with
  | unit => exact .unit _
  | prod _ _ ihA ihB => exact .prod ihA ihB
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | var => exact .var _ _
  | fvar => exact .fvar _ _
  | lam _ ih => exact .lam ih
  | app _ _ ihF ihG => exact .app ihF ihG
  | mu ha _ ih => exact .mu (ha.weaken hΨ le_rfl) ih
  | nu ha _ ih => exact .nu (ha.weaken hΨ le_rfl) ih
  | allT _ ih => exact .allT ih
  | exT _ ih => exact .exT ih
  | allS ha _ ih => exact .allS (ha.weaken hΨ le_rfl) ih
  | exS ha _ ih => exact .exS (ha.weaken hΨ le_rfl) ih

/-! ## Encodings -/

theorem dom_append_right' {Ψ Ψ' : SizeCtx} : ∀ i ∈ Ψ'.dom, i ∈ (Ψ ++ Ψ').dom := by
  intro i hi
  simp only [SizeCtx.dom, List.map_append, List.mem_append]
  exact Or.inr hi

/-- The outputs of an encoding: same size erasure, sizes from the generated context, generated
names admissible, all bounds `∞`. -/
theorem encode_facts {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx} {G G' : Ty}
    {Ψ : SizeCtx} (h : Encode πs ok π Δ Δb G Ψ G') :
    G'.eraseSz = G.eraseSz ∧ SizesWf Ψ 0 G' ∧ (∀ i ∈ Ψ.dom, ok i) ∧ (∀ p ∈ Ψ, p.2 = .inf 0) := by
  refine Encode.rec
    (motive_1 := fun _ _ _ G Ψ G' _ =>
      G'.eraseSz = G.eraseSz ∧ SizesWf Ψ 0 G' ∧ (∀ i ∈ Ψ.dom, ok i) ∧ (∀ p ∈ Ψ, p.2 = .inf 0))
    (motive_2 := fun _ _ _ S Ψ S' _ =>
      Ty.eraseSzList S' = Ty.eraseSzList S ∧ (∀ T ∈ S', SizesWf Ψ 0 T) ∧ (∀ i ∈ Ψ.dom, ok i) ∧
        (∀ p ∈ Ψ, p.2 = .inf 0))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros; exact ⟨rfl, .unit _, by simp [SizeCtx.dom], by simp⟩
  · intro π Δ Δb A B A' B' Ψ₁ Ψ₂ _ _ _ ih₁ ih₂
    refine ⟨by simp [Ty.eraseSz, ih₁.1, ih₂.1],
      .prod (ih₁.2.1.mono dom_append_left) (ih₂.2.1.mono dom_append_right'), ?_, ?_⟩
    · intro i hi
      simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ih₁.2.2.1 i hi
      · exact ih₂.2.2.1 i hi
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ih₁.2.2.2 p hp
      · exact ih₂.2.2.2 p hp
  · intro π Δ Δb A B A' B' Ψ₁ Ψ₂ _ _ _ ih₁ ih₂
    refine ⟨by simp [Ty.eraseSz, ih₁.1, ih₂.1],
      .arr (ih₁.2.1.mono dom_append_left) (ih₂.2.1.mono dom_append_right'), ?_, ?_⟩
    · intro i hi
      simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ih₁.2.2.1 i hi
      · exact ih₂.2.2.1 i hi
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ih₁.2.2.2 p hp
      · exact ih₂.2.2.2 p hp
  · intros; exact ⟨rfl, .var _ _, by simp [SizeCtx.dom], by simp⟩
  · intros; exact ⟨rfl, .fvar _ _, by simp [SizeCtx.dom], by simp⟩
  · intro π Δ Δb ι F F' Ψ _ ih
    exact ⟨by simp [Ty.eraseSz, ih.1], .lam ih.2.1, ih.2.2.1, ih.2.2.2⟩
  · intro π π' Δ Δb F G F' G' ι κ₁ κ₂ Ψ₁ Ψ₂ _ _ _ _ ih₁ ih₂
    refine ⟨by simp [Ty.eraseSz, ih₁.1, ih₂.1],
      .app (ih₁.2.1.mono dom_append_left) (ih₂.2.1.mono dom_append_right'), ?_, ?_⟩
    · intro i hi
      simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ih₁.2.2.1 i hi
      · exact ih₂.2.2.1 i hi
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ih₁.2.2.2 p hp
      · exact ih₂.2.2.2 p hp
  · intro π Δ Δb S S' Ψ i _ hok _ _ ih
    refine ⟨by simp [Ty.eraseSz, ih.1], .mu (by simp [SizeWfAt, SizeCtx.dom]) fun T hT =>
      (ih.2.1 T hT).mono (fun j hj => by simp [SizeCtx.dom] at hj ⊢; exact Or.inr hj), ?_, ?_⟩
    · intro j hj
      simp only [SizeCtx.dom, List.map_cons, List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact hok
      · exact ih.2.2.1 j hj
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · exact ih.2.2.2 p hp
  · intro π Δ Δb S S' Ψ _ _ ih
    exact ⟨by simp [Ty.eraseSz, ih.1], .mu trivial ih.2.1, ih.2.2.1, ih.2.2.2⟩
  · intro π Δ Δb R R' Ψ i _ hok _ _ ih
    refine ⟨by simp [Ty.eraseSz, ih.1], .nu (by simp [SizeWfAt, SizeCtx.dom]) fun T hT =>
      (ih.2.1 T hT).mono (fun j hj => by simp [SizeCtx.dom] at hj ⊢; exact Or.inr hj), ?_, ?_⟩
    · intro j hj
      simp only [SizeCtx.dom, List.map_cons, List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact hok
      · exact ih.2.2.1 j hj
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · exact ih.2.2.2 p hp
  · intro π Δ Δb R R' Ψ _ _ ih
    exact ⟨by simp [Ty.eraseSz, ih.1], .nu trivial ih.2.1, ih.2.2.1, ih.2.2.2⟩
  · intro π Δ Δb κ B B' Ψ _ ih
    exact ⟨by simp [Ty.eraseSz, ih.1], .allT ih.2.1, ih.2.2.1, ih.2.2.2⟩
  · intro π Δ Δb κ B B' Ψ _ ih
    exact ⟨by simp [Ty.eraseSz, ih.1], .exT ih.2.1, ih.2.2.1, ih.2.2.2⟩
  · intros; exact ⟨rfl, fun _ h => by simp at h, by simp [SizeCtx.dom], by simp⟩
  · intro π Δ Δb T T' S S' Ψ₁ Ψ₂ _ _ _ ih₁ ih₂
    refine ⟨by simp [Ty.eraseSzList, ih₁.1, ih₂.1], ?_, ?_, ?_⟩
    · intro U hU
      rcases List.mem_cons.mp hU with rfl | hU
      · exact ih₁.2.1.mono dom_append_left
      · exact (ih₂.2.1 U hU).mono dom_append_right'
    · intro i hi
      simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ih₁.2.2.1 i hi
      · exact ih₂.2.2.1 i hi
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ih₁.2.2.2 p hp
      · exact ih₂.2.2.2 p hp

/-! ## Scopes -/

theorem ScopeOK.left {φ : FlexSubst} {Φ₁ Φ₂ : List FlexVar} (h : ScopeOK φ (Φ₁ ++ Φ₂)) :
    ScopeOK φ Φ₁ := fun v hv => h v (List.mem_append_left _ hv)

theorem ScopeOK.right {φ : FlexSubst} {Φ₁ Φ₂ : List FlexVar} (h : ScopeOK φ (Φ₁ ++ Φ₂)) :
    ScopeOK φ Φ₂ := fun v hv => h v (List.mem_append_right _ hv)

theorem ScopeOK.tail {φ : FlexSubst} {v : FlexVar} {Φ : List FlexVar} (h : ScopeOK φ (v :: Φ)) :
    ScopeOK φ Φ := fun w hw => h w (List.mem_cons_of_mem _ hw)

theorem ScopeOK.var {φ : FlexSubst} {Φ : List FlexVar} (h : ScopeOK φ Φ) {v : FlexVar}
    (hv : v ∈ Φ) : SizeWf v.scope ((Size.var v.name 0).subst φ) := by
  obtain ⟨b, hb, hw⟩ := h v hv
  simp [Size.subst, hb, Size.shift_zero, hw]

theorem SizeWf.substBounds {Ψ : SizeCtx} {a : Size} (h : SizeWf Ψ a) (φ : FlexSubst) :
    SizeWf (Ψ.substBounds φ) a :=
  h.weaken (fun i hi => by rwa [SizeCtx.substBounds_dom]) le_rfl

theorem ScopeOK.encFlex {φ : FlexSubst} {Ψ ΨG : SizeCtx} (h : ScopeOK φ (encFlex Ψ ΨG)) :
    ∀ i ∈ ΨG.dom, SizeWf (Ψ.substBounds φ) ((Size.var i 0).subst φ) := by
  intro i hi
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  have := h.var (v := ⟨p.1, .mix, Ψ⟩) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  exact this.substBounds φ

theorem ScopeOK.callFlex {φ : FlexSubst} {Ψ : SizeCtx} {g : FunDecl} {as : List Nat}
    (h : ScopeOK φ (callFlex Ψ g as)) (hlen : as.length = g.sizeParams.length) :
    ∀ k ∈ as, SizeWf (Ψ.substBounds φ) ((Size.var k 0).subst φ) := by
  intro k hk
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hk
  have hn' : n < g.sizeParams.length := hlen ▸ hn
  have hmem : (g.sizeParams[n], as[n]) ∈ g.sizeParams.zip as := by
    rw [List.mem_iff_getElem]
    exact ⟨n, by simp [hn, hn'], by simp⟩
  have := h.var (v := ⟨as[n], paramPol g.ty (g.sizeParams[n]).1, Ψ⟩)
    (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  exact this.substBounds φ

/-! ## Composition of size substitutions -/

/-- Substituting after substituting: for sizes whose variables are all substituted. -/
theorem Size.subst_comp (σ φ : List (Nat × Size)) :
    ∀ a : Size, (∀ i ∈ a.fvars, (σ.lookup i).isSome) →
      (a.subst σ).subst φ = a.subst (σ.map fun p => (p.1, p.2.subst φ))
  | .inf _, _ => rfl
  | .bvar _ _, _ => rfl
  | .var i n, h => by
    have hi := h i (by simp [Size.fvars])
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hi
    have hb' : (σ.map fun p => (p.1, p.2.subst φ)).lookup i = some (b.subst φ) := by
      clear h hi
      induction σ with
      | nil => simp [List.lookup] at hb
      | cons q σ ih =>
        obtain ⟨y, c⟩ := q
        by_cases hiy : i = y
        · subst hiy; simp [List.lookup] at hb ⊢; rw [hb]
        · have hbe : (i == y) = false := by simpa using hiy
          simp only [List.lookup, hbe] at hb
          simp only [List.map_cons, List.lookup, hbe]
          exact ih hb
    simp only [Size.subst, hb, hb']
    exact Size.subst_shift b n
  | .meet a b, h => by
    simp only [Size.subst]
    rw [Size.subst_comp σ φ a (fun i hi => h i (by simp [Size.fvars, hi])),
      Size.subst_comp σ φ b (fun i hi => h i (by simp [Size.fvars, hi]))]

theorem SizeWfAt.fvars_dom {Ψ : SizeCtx} {m : Nat} :
    ∀ {a : Size}, SizeWfAt Ψ m a → ∀ i ∈ a.fvars, i ∈ Ψ.dom
  | .inf _, _, i, hi => by simp [Size.fvars] at hi
  | .var j _, h, i, hi => by simp [Size.fvars] at hi; subst hi; exact h
  | .bvar _ _, _, i, hi => by simp [Size.fvars] at hi
  | .meet _ _, h, i, hi => by
    simp only [Size.fvars, List.mem_append] at hi
    rcases hi with hi | hi
    · exact SizeWfAt.fvars_dom h.1 i hi
    · exact SizeWfAt.fvars_dom h.2 i hi

theorem Ty.substSize_comp {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A)
    (σ φ : List (Nat × Size)) (hσ : ∀ i ∈ Ψ.dom, (σ.lookup i).isSome) :
    (A.substSize σ).substSize φ = A.substSize (σ.map fun p => (p.1, p.2.subst φ)) := by
  induction h with
  | unit => rfl
  | prod _ _ ihA ihB => simp only [Ty.substSize, ihA, ihB]
  | arr _ _ ihA ihB => simp only [Ty.substSize, ihA, ihB]
  | var => rfl
  | fvar => rfl
  | lam _ ih => simp only [Ty.substSize, ih]
  | app _ _ ihF ihG => simp only [Ty.substSize, ihF, ihG]
  | @mu m a S ha hS ih =>
    simp only [Ty.substSize]
    rw [Size.subst_comp σ φ a (fun i hi => hσ i (SizeWfAt.fvars_dom ha i hi))]
    congr 1
    clear ha
    induction S with
    | nil => rfl
    | cons T S ihS =>
      simp only [Ty.substSizeList]
      rw [ih T (by simp), ihS (fun T' hT' => hS T' (by simp [hT']))
        (fun T' hT' => ih T' (by simp [hT']))]
  | @nu m a R ha hS ih =>
    simp only [Ty.substSize]
    rw [Size.subst_comp σ φ a (fun i hi => hσ i (SizeWfAt.fvars_dom ha i hi))]
    congr 1
    clear ha
    induction R with
    | nil => rfl
    | cons T R ihR =>
      simp only [Ty.substSizeList]
      rw [ih T (by simp), ihR (fun T' hT' => hS T' (by simp [hT']))
        (fun T' hT' => ih T' (by simp [hT']))]
  | allT _ ih => simp only [Ty.substSize, ih]
  | exT _ ih => simp only [Ty.substSize, ih]
  | allS ha _ ih =>
    simp only [Ty.substSize, ih]
    rw [Size.subst_comp σ φ _ (fun i hi => hσ i (SizeWfAt.fvars_dom ha i hi))]
  | exS ha _ ih =>
    simp only [Ty.substSize, ih]
    rw [Size.subst_comp σ φ _ (fun i hi => hσ i (SizeWfAt.fvars_dom ha i hi))]

theorem zip_map_snd (l : List Nat) (bs : List Size) (f : Size → Size) :
    (l.zip bs).map (fun p => (p.1, f p.2)) = l.zip (bs.map f) := by
  induction l generalizing bs with
  | nil => simp
  | cons x l ih =>
    cases bs with
    | nil => simp
    | cons b bs => simp [ih]

theorem zip_lookup_isSome (l : List Nat) (bs : List Size) (hlen : l.length ≤ bs.length) :
    ∀ i ∈ l, ((l.zip bs).lookup i).isSome := by
  induction l generalizing bs with
  | nil => intro i hi; simp at hi
  | cons x l ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      intro i hi
      by_cases hix : i = x
      · subst hix; simp
      · have hb : (i == x) = false := by simpa using hix
        simp only [List.zip_cons_cons, List.lookup, hb]
        exact ih bs (by simpa using hlen) i (by simpa [hix] using hi)

theorem SizeCtxWf.dom_nodup {Ψ : SizeCtx} (h : SizeCtxWf Ψ) : Ψ.dom.Nodup := by
  induction h with
  | nil => simp [SizeCtx.dom]
  | @snoc Ψ i a _ hi _ ih =>
    simp only [SizeCtx.dom, List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro x hx y hy
    simp at hy; subst hy
    exact fun h => hi (h ▸ hx)

theorem SizeCtxWf.bound_wf {Ψ : SizeCtx} (h : SizeCtxWf Ψ) : ∀ p ∈ Ψ, SizeWf Ψ p.2 := by
  induction h with
  | nil => intro p hp; simp at hp
  | snoc _ _ ha ih => exact CtxBoundsWf.extend ih ha

theorem lookup_zip_getElem' : ∀ (l : List Nat) (as : List Size), l.Nodup → l.length = as.length →
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
    have := lookup_zip_getElem' l as (List.nodup_cons.mp hnd).2 (by simpa using hlen) k hk' ha'
    simp only [List.zip_cons_cons, List.getElem_cons_succ, List.lookup_cons, hb]
    exact this

end NishtAbel2024V5
