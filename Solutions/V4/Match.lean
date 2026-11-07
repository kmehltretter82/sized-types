import Solutions.V4.Wf

/-! # V4: semantic contexts, subtyping soundness, pattern matching soundness -/

namespace NishtAbel2024V4

/-- Free type variables are interpreted by candidates. -/
def TEnvOK (W : World) (Θ : List Nat) (θ : TEnv) : Prop := ∀ X ∈ Θ, Cand W (θ X)

/-- `σ ∈ ⟦Γ⟧ρθ`: every variable of `Γ` is bound by `σ` to a member of its type, and all values of
`σ` are closed. -/
def SemCtx (W : World) (ρ : SizeVal) (θ : TEnv) (Γ : TermCtx) (σ : TmSubst) : Prop :=
  (∀ x A, Γ.lookup x = some A →
    ∃ v, σ.lookup x = some v ∧ v ∈ interp W ρ θ A SzEnv.zero Env.empty) ∧
  (∀ x v, σ.lookup x = some v → v.Closed)

/-- Every bound of the context is well-formed in the context. -/
def CtxBoundsWf (Ψ : SizeCtx) : Prop := ∀ p ∈ Ψ, SizeWf Ψ p.2

/-- Every type in the context is locally closed and well-formed. -/
def TermCtxWf (Ψ : SizeCtx) (Θ : List Nat) (Γ : TermCtx) : Prop := ∀ p ∈ Γ, TyWf Ψ Θ 0 0 p.2

theorem interp_closed_mem {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Θ : List Nat} {A : Ty}
    (hA : TyWf Ψ Θ 0 0 A) (ρ : SizeVal) {θ : TEnv} (hθ : TEnvOK W Θ θ) (ζ : SzEnv) (η : Env)
    {v : Tm} (hv : v ∈ interp W ρ θ A ζ η) : SNc W v :=
  (interp_cand hW ρ hθ hA ζ η (fun _ h => absurd h (Nat.not_lt_zero _))).sn v hv

theorem interp_cand_closed {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Θ : List Nat} {A : Ty}
    (hA : TyWf Ψ Θ 0 0 A) (ρ : SizeVal) {θ : TEnv} (hθ : TEnvOK W Θ θ) :
    Cand W (interp W ρ θ A SzEnv.zero Env.empty) :=
  interp_cand hW ρ hθ hA _ _ (fun _ h => absurd h (Nat.not_lt_zero _))

/-! ## Subtyping -/

theorem subTy_sound {W : World} {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) (θ : TEnv)
    {A B : Ty} (h : SubTy Ψ A B) :
    ∀ η, interp W ρ θ A SzEnv.zero η ⊆ interp W ρ θ B SzEnv.zero η := by
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

def TEnv.update (θ : TEnv) (X : Nat) (𝒳 : Set Tm) : TEnv :=
  fun Y => if Y = X then 𝒳 else θ Y

theorem SizeVal.update_agree {ρ : SizeVal} {j : Nat} {β : Ordinal.{0}} {Ψ : SizeCtx}
    (hj : j ∉ Ψ.dom) : ∀ i ∈ Ψ.dom, SizeVal.update ρ j β i = ρ i := by
  intro i hi
  have : i ≠ j := fun h => hj (h ▸ hi)
  simp [SizeVal.update, this]

theorem TEnv.update_agree {θ : TEnv} {X : Nat} {𝒳 : Set Tm} {Θ : List Nat} (hX : X ∉ Θ) :
    ∀ Y ∈ Θ, TEnv.update θ X 𝒳 Y = θ Y := by
  intro Y hY
  have : Y ≠ X := fun h => hX (h ▸ hY)
  simp [TEnv.update, this]

theorem TEnvOK.extend {W : World} {Θ : List Nat} {θ : TEnv} (h : TEnvOK W Θ θ) {X : Nat}
    {𝒳 : Set Tm} (h𝒳 : Cand W 𝒳) : TEnvOK W (Θ ++ [X]) (TEnv.update θ X 𝒳) := by
  intro Y hY
  by_cases hYX : Y = X
  · simp [TEnv.update, hYX]; exact h𝒳
  · simp only [TEnv.update, hYX, if_false]
    rcases List.mem_append.mp hY with hY | hY
    · exact h Y hY
    · simp at hY; exact absurd hY hYX

theorem TEnvOK.agree {W : World} {Θ : List Nat} {θ θ' : TEnv} (h : TEnvOK W Θ θ)
    (hag : ∀ X ∈ Θ, θ' X = θ X) : TEnvOK W Θ θ' :=
  fun X hX => by rw [hag X hX]; exact h X hX

theorem ValidVal.agree {Ψ : SizeCtx} {ρ ρ' : SizeVal} (hv : ValidVal Ψ ρ) (hb : CtxBoundsWf Ψ)
    (hag : ∀ i ∈ Ψ.dom, ρ' i = ρ i) : ValidVal Ψ ρ' := by
  intro p hp
  have hi : p.1 ∈ Ψ.dom := SizeCtx.mem_dom (a := p.2) (by simpa using hp)
  rw [hag _ hi, sizeVal_agree (fun i h => hag i h) (fun _ h => absurd h (Nat.not_lt_zero _))
    (hb p hp)]
  exact hv p hp

theorem ValidVal.extend {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) (hb : CtxBoundsWf Ψ)
    {j : Nat} (hj : j ∉ Ψ.dom) {a : Size} (ha : SizeWf Ψ a) {β : Ordinal.{0}}
    (hβ : β < sizeVal ρ SzEnv.zero a) :
    ValidVal (Ψ ++ [(j, a)]) (SizeVal.update ρ j β) := by
  have hag := SizeVal.update_agree (ρ := ρ) (β := β) hj
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact (hv.agree hb hag) p hp
  · simp at hp; subst hp
    simp only [SizeVal.update, if_true]
    rw [sizeVal_agree hag (fun _ h => absurd h (Nat.not_lt_zero _)) ha]
    exact ⟨hβ, lt_of_lt_of_le hβ (sizeVal_le_omega hv ha _)⟩

theorem CtxBoundsWf.extend {Ψ : SizeCtx} (hb : CtxBoundsWf Ψ) {j : Nat} {a : Size}
    (ha : SizeWf Ψ a) : CtxBoundsWf (Ψ ++ [(j, a)]) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact (hb p hp).weaken dom_append_left le_rfl
  · simp at hp; subst hp; exact ha.weaken dom_append_left le_rfl

theorem sizeWf_fresh_var (Ψ : SizeCtx) (j : Nat) (a : Size) : SizeWf (Ψ ++ [(j, a)]) (.var j 0) := by
  simp [SizeWf, SizeWfAt, SizeCtx.dom]

/-! ## Opening at fresh variables -/

/-- The payload type of a constructor pattern, opened at a fresh size variable. -/
theorem interp_unfold_mu_fresh {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {a : Size} {S : List Ty} {c j : Nat} {Sc : Ty} (hwf : TyWf Ψ Θ 0 0 (.mu a S))
    (hj : j ∉ Ψ.dom) (hc : S[c]? = some Sc) (β : Ordinal.{0}) :
    interp W (SizeVal.update ρ j β) θ (Sc.substTy 0 (.mu (.var j 0) S)) SzEnv.zero Env.empty =
      interpAt W ρ θ S c SzEnv.zero (Env.cons (MuSet W
        (fun c 𝒳 => interpAt W ρ θ S c SzEnv.zero (Env.cons 𝒳 Env.empty)) β) Env.empty) := by
  have hcl : c < S.length := (List.getElem?_eq_some_iff.mp hc).1
  have hScEq : S[c] = Sc := (List.getElem?_eq_some_iff.mp hc).2
  have hS : ∀ T ∈ S, TyWf Ψ Θ 1 0 T := by cases hwf with | mu _ h _ => exact h
  have hpos : ∀ T ∈ S, PolIn true 0 T := by cases hwf with | mu _ _ h => exact h
  have hag : ∀ i ∈ Ψ.dom, SizeVal.update ρ j β i = ρ i := SizeVal.update_agree hj
  have hwfj : TyWf (Ψ ++ [(j, Size.inf)]) Θ 0 0 (.mu (.var j 0) S) :=
    .mu (sizeWf_fresh_var _ _ _)
      (fun T hT => (hS T hT).weaken _ _ _ _ dom_append_left (fun _ h => h) le_rfl le_rfl) hpos
  rw [← hScEq, interp_unfold_mu hcl hwfj]
  have hval : sizeVal (SizeVal.update ρ j β) SzEnv.zero (.var j 0) = β := by
    simp [sizeVal, SizeVal.update]
  rw [hval]
  have hF : (fun c 𝒳 => interpAt W (SizeVal.update ρ j β) θ S c SzEnv.zero (Env.cons 𝒳 Env.empty)) =
      (fun c 𝒳 => interpAt W ρ θ S c SzEnv.zero (Env.cons 𝒳 Env.empty)) := by
    funext c' 𝒳
    by_cases hc' : c' < S.length
    · rw [interpAt_eq W _ θ S c' _ _ hc', interpAt_eq W ρ θ S c' _ _ hc']
      exact interp_agree (hS _ (List.getElem_mem hc')) _ ρ θ θ _ _ _ _ hag (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ _ => rfl)
    · rw [interpAt_out W _ θ S c' _ _ (by omega), interpAt_out W ρ θ S c' _ _ (by omega)]
  rw [hF, interpAt_eq W _ θ S c _ _ hcl,
    interp_agree (hS _ (List.getElem_mem hcl)) _ ρ θ θ _ _ _ _ hag (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl),
    ← interpAt_eq W ρ θ S c _ _ hcl]

theorem interp_unfold_nu_fresh {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {a : Size} {R : List Ty} {d j : Nat} {Rd : Ty} (hwf : TyWf Ψ Θ 0 0 (.nu a R))
    (hj : j ∉ Ψ.dom) (hd : R[d]? = some Rd) (β : Ordinal.{0}) :
    interp W (SizeVal.update ρ j β) θ (Rd.substTy 0 (.nu (.var j 0) R)) SzEnv.zero Env.empty =
      interpAt W ρ θ R d SzEnv.zero (Env.cons (NuSet W R.length
        (fun d 𝒳 => interpAt W ρ θ R d SzEnv.zero (Env.cons 𝒳 Env.empty)) β) Env.empty) := by
  have hdl : d < R.length := (List.getElem?_eq_some_iff.mp hd).1
  have hRd : R[d] = Rd := (List.getElem?_eq_some_iff.mp hd).2
  have hR : ∀ T ∈ R, TyWf Ψ Θ 1 0 T := by cases hwf with | nu _ h _ => exact h
  have hpos : ∀ T ∈ R, PolIn true 0 T := by cases hwf with | nu _ _ h => exact h
  have hag : ∀ i ∈ Ψ.dom, SizeVal.update ρ j β i = ρ i := SizeVal.update_agree hj
  have hwfj : TyWf (Ψ ++ [(j, Size.inf)]) Θ 0 0 (.nu (.var j 0) R) :=
    .nu (sizeWf_fresh_var _ _ _)
      (fun T hT => (hR T hT).weaken _ _ _ _ dom_append_left (fun _ h => h) le_rfl le_rfl) hpos
  rw [← hRd, interp_unfold_nu hdl hwfj]
  have hval : sizeVal (SizeVal.update ρ j β) SzEnv.zero (.var j 0) = β := by
    simp [sizeVal, SizeVal.update]
  rw [hval]
  have hG : (fun d 𝒳 => interpAt W (SizeVal.update ρ j β) θ R d SzEnv.zero (Env.cons 𝒳 Env.empty)) =
      (fun d 𝒳 => interpAt W ρ θ R d SzEnv.zero (Env.cons 𝒳 Env.empty)) := by
    funext d' 𝒳
    by_cases hd' : d' < R.length
    · rw [interpAt_eq W _ θ R d' _ _ hd', interpAt_eq W ρ θ R d' _ _ hd']
      exact interp_agree (hR _ (List.getElem_mem hd')) _ ρ θ θ _ _ _ _ hag (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ _ => rfl)
    · rw [interpAt_out W _ θ R d' _ _ (by omega), interpAt_out W ρ θ R d' _ _ (by omega)]
  rw [hG, interpAt_eq W _ θ R d _ _ hdl,
    interp_agree (hR _ (List.getElem_mem hdl)) _ ρ θ θ _ _ _ _ hag (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl),
    ← interpAt_eq W ρ θ R d _ _ hdl]

/-- The body of `∀X`/`∃X`, opened at a fresh type variable. -/
theorem interp_open_fresh_ty {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {B : Ty} (hB : TyWf Ψ Θ 1 0 B) {X : Nat} (hX : X ∉ Θ) (𝒳 : Set Tm) :
    interp W ρ (TEnv.update θ X 𝒳) (B.substTy 0 (.fvar X)) SzEnv.zero Env.empty =
      interp W ρ θ B SzEnv.zero (Env.cons 𝒳 Env.empty) := by
  rw [interp_openTy (T := .fvar X) (fun _ _ _ _ => rfl)]
  have h1 : interp W ρ (TEnv.update θ X 𝒳) (.fvar X) SzEnv.zero Env.empty = 𝒳 := by
    simp [interp, TEnv.update]
  rw [h1]
  exact interp_agree hB ρ ρ _ θ _ _ _ _ (fun _ _ => rfl) (TEnv.update_agree hX) (fun _ _ => rfl)
    (fun _ _ => rfl)

/-- The body of `∀(j<a)`/`∃(j<a)`, opened at a fresh size variable. -/
theorem interp_open_fresh_sz {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {B : Ty} (hB : TyWf Ψ Θ 0 1 B) {j : Nat} (hj : j ∉ Ψ.dom) (β : Ordinal.{0}) :
    interp W (SizeVal.update ρ j β) θ (B.openSz 0 (.var j 0)) SzEnv.zero Env.empty =
      interp W ρ θ B (SzEnv.cons β SzEnv.zero) Env.empty := by
  rw [interp_openSz0]
  have h1 : sizeVal (SizeVal.update ρ j β) SzEnv.zero (.var j 0) = β := by
    simp [sizeVal, SizeVal.update]
  rw [h1]
  exact interp_agree hB _ ρ θ θ _ _ _ _ (SizeVal.update_agree hj) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-! ## Facts about pattern typing -/

theorem patTy_dom {Ψ : SizeCtx} {Θ : List Nat} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
    {Θ' : List Nat} (h : PatTy Ψ Θ p A Γ Ψ' Θ') : Γ.map Prod.fst = p.vars := by
  induction h with
  | var => rfl
  | unit => rfl
  | pair _ _ ih₁ ih₂ => simp [Pat.vars, ih₁, ih₂]
  | cons _ _ _ ih => simpa [Pat.vars] using ih
  | packT _ _ ih => simpa [Pat.vars] using ih
  | packS _ _ ih => simpa [Pat.vars] using ih

theorem patTy_ctx {Ψ : SizeCtx} {Θ : List Nat} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
    {Θ' : List Nat} (h : PatTy Ψ Θ p A Γ Ψ' Θ') : TyWf Ψ Θ 0 0 A → CtxBoundsWf Ψ →
      TermCtxWf (Ψ ++ Ψ') (Θ ++ Θ') Γ ∧ CtxBoundsWf (Ψ ++ Ψ') := by
  induction h with
  | var Ψ Θ x A =>
    intro hA hb
    refine ⟨?_, by simpa using hb⟩
    intro q hq; simp at hq; subst hq; simpa using hA
  | unit Ψ Θ => intro _ hb; exact ⟨by simp [TermCtxWf], by simpa using hb⟩
  | @pair Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p q A B Γ₁ Γ₂ _ _ ih₁ ih₂ =>
    intro hAB hb
    cases hAB with
    | prod hA hB =>
      obtain ⟨hΓ₁, hb₁⟩ := ih₁ hA hb
      obtain ⟨hΓ₂, hb₂⟩ := ih₂ (hB.mono dom_append_left mem_append_left') hb₁
      refine ⟨?_, by simpa using hb₂⟩
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · have h' := (hΓ₁ r hr).mono (Ψ' := Ψ ++ Ψ₁ ++ Ψ₂) (Θ' := Θ ++ Θ₁ ++ Θ₂)
          dom_append_left mem_append_left'
        simpa using h'
      · simpa using hΓ₂ r hr
  | @cons Ψ Ψ' Θ Θ' c j p a S Sc Γ hc hj _ ih =>
    intro hA hb
    have ha : SizeWf Ψ a := by cases hA with | mu ha _ _ => exact ha
    have hA' : TyWf (Ψ ++ [(j, a)]) Θ 0 0 (.mu a S) := hA.mono dom_append_left (fun _ h => h)
    have hunf := hA'.unfold_mu (b := .var j 0) hc (sizeWf_fresh_var _ _ _)
    obtain ⟨hΓ, hb'⟩ := ih hunf (hb.extend ha)
    exact ⟨by simpa using hΓ, by simpa using hb'⟩
  | @packT Ψ Ψ' Θ Θ' X p B Γ hX _ ih =>
    intro hA hb
    have hB : TyWf Ψ Θ 1 0 B := by cases hA with | exT h => exact h
    have hopen : TyWf Ψ (Θ ++ [X]) 0 0 (B.substTy 0 (.fvar X)) :=
      (hB.weaken _ _ _ _ (fun _ h => h) mem_append_left' le_rfl le_rfl).open_ty
        (.fvar (by simp))
    obtain ⟨hΓ, hb'⟩ := ih hopen hb
    exact ⟨by simpa using hΓ, hb'⟩
  | @packS Ψ Ψ' Θ Θ' j p a B Γ hj _ ih =>
    intro hA hb
    have ha : SizeWf Ψ a := by cases hA with | exS ha _ => exact ha
    have hB : TyWf Ψ Θ 0 1 B := by cases hA with | exS _ h => exact h
    have hopen : TyWf (Ψ ++ [(j, a)]) Θ 0 0 (B.openSz 0 (.var j 0)) :=
      (hB.weaken _ _ _ _ dom_append_left (fun _ h => h) le_rfl le_rfl).open_sz
        (sizeWf_fresh_var _ _ _)
    obtain ⟨hΓ, hb'⟩ := ih hopen (hb.extend ha)
    exact ⟨by simpa using hΓ, by simpa using hb'⟩

/-! ## Semantic contexts -/

theorem SemCtx.nil (W : World) (ρ : SizeVal) (θ : TEnv) : SemCtx W ρ θ [] [] :=
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

theorem SemCtx.append {W : World} {ρ : SizeVal} {θ : TEnv} {Γ₁ Γ₂ : TermCtx} {σ₁ σ₂ : TmSubst}
    (h₁ : SemCtx W ρ θ Γ₁ σ₁) (h₂ : SemCtx W ρ θ Γ₂ σ₂)
    (hdom : σ₁.map Prod.fst = Γ₁.map Prod.fst) : SemCtx W ρ θ (Γ₁ ++ Γ₂) (σ₁ ++ σ₂) := by
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

theorem lookup_mem_ctx {Γ : TermCtx} {x : Nat} {A : Ty} (h : Γ.lookup x = some A) : (x, A) ∈ Γ := by
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

/-- Transport of a semantic context to valuations agreeing on the relevant variables. -/
theorem SemCtx.agree {W : World} {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx}
    (hΓ : TermCtxWf Ψ Θ Γ) {ρ ρ' : SizeVal} {θ θ' : TEnv} (hag : ∀ i ∈ Ψ.dom, ρ i = ρ' i)
    (hagθ : ∀ X ∈ Θ, θ X = θ' X) {σ : TmSubst} (h : SemCtx W ρ θ Γ σ) : SemCtx W ρ' θ' Γ σ := by
  refine ⟨?_, h.2⟩
  intro x A hx
  obtain ⟨v, hv, hmem⟩ := h.1 x A hx
  refine ⟨v, hv, ?_⟩
  have hA : TyWf Ψ Θ 0 0 A := hΓ (x, A) (lookup_mem_ctx hx)
  rwa [← interp_agree hA ρ ρ' θ θ' _ _ _ _ hag hagθ (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _))]

theorem lookup_cons_ty (k x : Nat) (b : Ty) (l : TermCtx) :
    ((k, b) :: l).lookup x = if x = k then some b else l.lookup x := by
  rw [List.lookup_cons]
  by_cases h : x = k
  · subst h; simp
  · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]

/-! ## Pattern matching soundness -/

/-- The conclusion of pattern matching soundness. -/
def PatOK (W : World) (Ψ Ψ' : SizeCtx) (Θ Θ' : List Nat) (ρ : SizeVal) (θ : TEnv) (Γ : TermCtx)
    (σm : TmSubst) : Prop :=
  ∃ ρ' θ', ValidVal (Ψ ++ Ψ') ρ' ∧ (∀ i ∈ Ψ.dom, ρ' i = ρ i) ∧ TEnvOK W (Θ ++ Θ') θ' ∧
    (∀ X ∈ Θ, θ' X = θ X) ∧ SemCtx W ρ' θ' Γ σm

theorem pat_sound {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Θ : List Nat} {p : Pat}
    {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : List Nat} (hp : PatTy Ψ Θ p A Γ Ψ' Θ') :
    ∀ (ρ : SizeVal) (θ : TEnv) (v : Tm) (σm : TmSubst), ValidVal Ψ ρ → CtxBoundsWf Ψ →
      TEnvOK W Θ θ → TyWf Ψ Θ 0 0 A → v ∈ interp W ρ θ A SzEnv.zero Env.empty →
      matchPat p v = .yes σm → PatOK W Ψ Ψ' Θ Θ' ρ θ Γ σm := by
  induction hp with
  | var Ψ Θ x A =>
    intro ρ θ v σm hv _ hθ hA hmem hm
    simp [matchPat] at hm; subst hm
    refine ⟨ρ, θ, by simpa using hv, fun _ _ => rfl, by simpa using hθ, fun _ _ => rfl, ?_, ?_⟩
    · intro y B hy
      rw [lookup_cons_ty] at hy
      by_cases hyx : y = x
      · simp [hyx] at hy; subst hy; subst hyx
        exact ⟨v, by simp, hmem⟩
      · simp [hyx] at hy
    · intro y w hy
      rw [lookup_cons_eq] at hy
      by_cases hyx : y = x
      · simp [hyx] at hy; subst hy; exact (interp_closed_mem hW hA ρ hθ _ _ hmem).1
      · simp [hyx] at hy
  | unit Ψ Θ =>
    intro ρ θ v σm hv _ hθ _ _ hm
    cases v <;> simp [matchPat] at hm
    subst hm
    exact ⟨ρ, θ, by simpa using hv, fun _ _ => rfl, by simpa using hθ, fun _ _ => rfl,
      SemCtx.nil W ρ θ⟩
  | @pair Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p q A B Γ₁ Γ₂ hp₁ hp₂ ih₁ ih₂ =>
    intro ρ θ v σm hv hb hθ hAB hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i t u
    obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
    have hA : TyWf Ψ Θ 0 0 A := by cases hAB with | prod h _ => exact h
    have hB : TyWf Ψ Θ 0 0 B := by cases hAB with | prod _ h => exact h
    simp only [interp] at hmem
    obtain ⟨t', u', heq, ht, hu⟩ := introSet_of_intro hmem (by simp [IsIntro])
    cases heq
    obtain ⟨ρ₁, θ₁, hv₁, hag₁, hθ₁, hagθ₁, hs₁⟩ := ih₁ ρ θ t σ₁ hv hb hθ hA ht hm₁
    have hb₁ := (patTy_ctx hp₁ hA hb).2
    have hB₁ : TyWf (Ψ ++ Ψ₁) (Θ ++ Θ₁) 0 0 B := hB.mono dom_append_left mem_append_left'
    have hu₁ : u ∈ interp W ρ₁ θ₁ B SzEnv.zero Env.empty := by
      rwa [interp_agree hB ρ₁ ρ θ₁ θ _ _ _ _ hag₁ hagθ₁ (fun _ h => absurd h (Nat.not_lt_zero _))
        (fun _ h => absurd h (Nat.not_lt_zero _))]
    obtain ⟨ρ₂, θ₂, hv₂, hag₂, hθ₂, hagθ₂, hs₂⟩ := ih₂ ρ₁ θ₁ u σ₂ hv₁ hb₁ hθ₁ hB₁ hu₁ hm₂
    refine ⟨ρ₂, θ₂, by simpa using hv₂, ?_, by simpa using hθ₂, ?_, ?_⟩
    · intro i hi
      rw [hag₂ i (dom_append_left i hi), hag₁ i hi]
    · intro X hX
      rw [hagθ₂ X (mem_append_left' X hX), hagθ₁ X hX]
    · have hΓ₁ := (patTy_ctx hp₁ hA hb).1
      have hs₁' := hs₁.agree hΓ₁ (fun i hi => (hag₂ i hi).symm) (fun X hX => (hagθ₂ X hX).symm)
      apply hs₁'.append hs₂
      rw [(matchPat_facts p t σ₁ hm₁).1, patTy_dom hp₁]
  | @cons Ψ Ψ' Θ Θ' c j p a S Sc Γ hc hj hp' ih =>
    intro ρ θ v σm hv hb hθ hA hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i c' t
    by_cases hcc : c = c'
    · simp [hcc] at hm
      subst hcc
      have ha : SizeWf Ψ a := by cases hA with | mu ha _ _ => exact ha
      simp only [interp] at hmem
      rw [MuSet_eq] at hmem
      obtain ⟨c₀, t₀, β, hβ, heq, ht⟩ := introSet_of_intro hmem (by simp [IsIntro])
      cases heq
      have hv₁ := hv.extend hb hj ha hβ
      have hb₁ := hb.extend (j := j) ha
      have hA' : TyWf (Ψ ++ [(j, a)]) Θ 0 0 (.mu a S) := hA.mono dom_append_left (fun _ h => h)
      have hunf := hA'.unfold_mu (b := .var j 0) hc (sizeWf_fresh_var _ _ _)
      have ht' : t ∈ interp W (SizeVal.update ρ j β) θ (Sc.substTy 0 (.mu (.var j 0) S))
          SzEnv.zero Env.empty := by
        rw [interp_unfold_mu_fresh hA hj hc β]; exact ht
      obtain ⟨ρ', θ', hv', hag', hθ', hagθ', hs'⟩ := ih _ θ t σm hv₁ hb₁ hθ hunf ht' hm
      refine ⟨ρ', θ', by simpa using hv', ?_, hθ', hagθ', hs'⟩
      intro i hi
      rw [hag' i (dom_append_left i hi), SizeVal.update_agree hj i hi]
    · simp [hcc] at hm
  | @packT Ψ Ψ' Θ Θ' X p B Γ hX hp' ih =>
    intro ρ θ v σm hv hb hθ hA hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i t
    have hB : TyWf Ψ Θ 1 0 B := by cases hA with | exT h => exact h
    simp only [interp] at hmem
    obtain ⟨t₀, 𝒳, heq, h𝒳, ht⟩ := introSet_of_intro hmem (by simp [IsIntro])
    cases heq
    have hθ₁ := hθ.extend (X := X) h𝒳
    have hopen : TyWf Ψ (Θ ++ [X]) 0 0 (B.substTy 0 (.fvar X)) :=
      (hB.weaken _ _ _ _ (fun _ h => h) mem_append_left' le_rfl le_rfl).open_ty
        (.fvar (by simp))
    have ht' : t ∈ interp W ρ (TEnv.update θ X 𝒳) (B.substTy 0 (.fvar X)) SzEnv.zero
        Env.empty := by
      rw [interp_open_fresh_ty hB hX]; exact ht
    obtain ⟨ρ', θ', hv', hag', hθ', hagθ', hs'⟩ := ih ρ _ t σm hv hb hθ₁ hopen ht' hm
    refine ⟨ρ', θ', by simpa using hv', hag', by simpa using hθ', ?_, hs'⟩
    intro Y hY
    rw [hagθ' Y (mem_append_left' Y hY), TEnv.update_agree hX Y hY]
  | @packS Ψ Ψ' Θ Θ' j p a B Γ hj hp' ih =>
    intro ρ θ v σm hv hb hθ hA hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i t
    have ha : SizeWf Ψ a := by cases hA with | exS ha _ => exact ha
    have hB : TyWf Ψ Θ 0 1 B := by cases hA with | exS _ h => exact h
    simp only [interp] at hmem
    obtain ⟨t₀, β, heq, hβ, ht⟩ := introSet_of_intro hmem (by simp [IsIntro])
    cases heq
    have hv₁ := hv.extend hb hj ha hβ
    have hb₁ := hb.extend (j := j) ha
    have hopen : TyWf (Ψ ++ [(j, a)]) Θ 0 0 (B.openSz 0 (.var j 0)) :=
      (hB.weaken _ _ _ _ dom_append_left (fun _ h => h) le_rfl le_rfl).open_sz
        (sizeWf_fresh_var _ _ _)
    have ht' : t ∈ interp W (SizeVal.update ρ j β) θ (B.openSz 0 (.var j 0)) SzEnv.zero
        Env.empty := by
      rw [interp_open_fresh_sz hB hj]; exact ht
    obtain ⟨ρ', θ', hv', hag', hθ', hagθ', hs'⟩ := ih _ θ t σm hv₁ hb₁ hθ hopen ht' hm
    refine ⟨ρ', θ', by simpa using hv', ?_, hθ', hagθ', hs'⟩
    intro i hi
    rw [hag' i (dom_append_left i hi), SizeVal.update_agree hj i hi]

end NishtAbel2024V4
