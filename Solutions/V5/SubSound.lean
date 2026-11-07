import Solutions.V5.KindWf

/-! # V5: valuation updates, semantic opening, and soundness of subtyping -/

namespace NishtAbel2024V5

/-! ## Valuation updates -/

def SizeVal.update (ρ : SizeVal) (j : Nat) (β : Ordinal.{0}) : SizeVal :=
  fun i => if i = j then β else ρ i

def TEnv.update (θ : TEnv) (X : Nat) (P : PSem) : TEnv :=
  fun Y => if Y = X then P else θ Y

theorem SizeVal.update_agree {ρ : SizeVal} {j : Nat} {β : Ordinal.{0}} {Ψ : SizeCtx}
    (hj : j ∉ Ψ.dom) : ∀ i ∈ Ψ.dom, SizeVal.update ρ j β i = ρ i := by
  intro i hi
  have : i ≠ j := fun h => hj (h ▸ hi)
  simp [SizeVal.update, this]

theorem TEnv.update_agree {θ : TEnv} {X : Nat} {P : PSem} {Θ : List Nat} (hX : X ∉ Θ) :
    ∀ Y ∈ Θ, TEnv.update θ X P Y = θ Y := by
  intro Y hY
  have : Y ≠ X := fun h => hX (h ▸ hY)
  simp [TEnv.update, this]

@[simp] theorem TEnv.update_self (θ : TEnv) (X : Nat) (P : PSem) : TEnv.update θ X P X = P := by
  simp [TEnv.update]

@[simp] theorem SizeVal.update_self (ρ : SizeVal) (j : Nat) (β : Ordinal.{0}) :
    SizeVal.update ρ j β j = β := by
  simp [SizeVal.update]

/-- Every bound of the context is well-formed in the context. -/
def CtxBoundsWf (Ψ : SizeCtx) : Prop := ∀ p ∈ Ψ, SizeWf Ψ p.2

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
    simp only [SizeVal.update_self]
    rw [sizeVal_agree hag (fun _ h => absurd h (Nat.not_lt_zero _)) ha]
    exact hβ

theorem CtxBoundsWf.extend {Ψ : SizeCtx} (hb : CtxBoundsWf Ψ) {j : Nat} {a : Size}
    (ha : SizeWf Ψ a) : CtxBoundsWf (Ψ ++ [(j, a)]) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact (hb p hp).weaken dom_append_left le_rfl
  · simp at hp; subst hp; exact ha.weaken dom_append_left le_rfl

theorem sizeWf_fresh_var (Ψ : SizeCtx) (j : Nat) (a : Size) :
    SizeWf (Ψ ++ [(j, a)]) (.var j 0) := by
  simp [SizeWf, SizeWfAt, SizeCtx.dom]

/-! ## Lookups in extended kinding contexts -/

theorem KCtx.lookup_append (Δ Δ' : KCtx) (X : Nat) :
    (Δ ++ Δ').lookup X = match Δ.lookup X with
      | some e => some e
      | none => Δ'.lookup X := by
  induction Δ with
  | nil => rfl
  | cons p Δ ih =>
    obtain ⟨Y, e⟩ := p
    by_cases h : X = Y
    · subst h; simp [List.lookup]
    · have hb : (X == Y) = false := by simpa using h
      simp only [List.cons_append, List.lookup, hb]
      exact ih

theorem KCtx.lookup_none_of_not_dom {Δ : KCtx} {X : Nat} (h : X ∉ Δ.dom) : Δ.lookup X = none := by
  cases hl : Δ.lookup X with
  | none => rfl
  | some e => exact absurd (KCtx.lookup_some_dom hl) h

theorem KCtx.lookup_snoc_fresh {Δ : KCtx} {X : Nat} (hX : X ∉ Δ.dom) (e : Pol × Kind) :
    (Δ ++ [(X, e)]).lookup X = some e := by
  rw [KCtx.lookup_append, KCtx.lookup_none_of_not_dom hX]
  simp [List.lookup]

theorem TRel.extend {W : World} {Δ : KCtx} {θ : TEnv} (h : TRel W Δ θ θ) {X : Nat}
    (hX : X ∉ Δ.dom) {π : Pol} {κ : Kind} {Y : Sem κ.erase} (hY : Good W κ Y) :
    TRel W (Δ ++ [(X, π, κ)]) (TEnv.update θ X (PSem.ofSem κ.erase Y))
      (TEnv.update θ X (PSem.ofSem κ.erase Y)) := by
  intro Z π' κ' hZ
  rw [KCtx.lookup_append] at hZ
  cases hl : Δ.lookup Z with
  | some e =>
    rw [hl] at hZ
    simp only [Option.some.injEq] at hZ
    subst hZ
    have hZX : Z ≠ X := fun h => hX (h ▸ KCtx.lookup_some_dom hl)
    simp only [TEnv.update, hZX, if_false]
    exact h Z π' κ' hl
  | none =>
    rw [hl] at hZ
    by_cases hZX : Z = X
    · subst hZX
      simp [List.lookup] at hZ
      obtain ⟨rfl, rfl⟩ := hZ
      simp only [TEnv.update_self, PSem.ofSem_self]
      exact ⟨hY, hY, PolRel.refl _ hY⟩
    · have hb : (Z == X) = false := by simpa using hZX
      simp [List.lookup, hb] at hZ

theorem TRel.agree {W : World} {Δ : KCtx} {θ θ' : TEnv} (h : TRel W Δ θ θ)
    (hag : ∀ X ∈ Δ.dom, θ' X = θ X) : TRel W Δ θ' θ' := by
  intro X π κ hX
  rw [hag X (KCtx.lookup_some_dom hX)]
  exact h X π κ hX

/-! ## Opening at fresh variables -/

/-- Opening a type binder at a fresh free type variable. -/
theorem interp_open_fresh_ty {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {m : Nat} {B : Ty} (hB : TyWf Ψ Θ 1 m B) {X : Nat} (hX : X ∉ Θ) (P : PSem) (ι : SKind)
    (ζ : SzEnv) (η : Env) :
    interp W ρ (TEnv.update θ X P) (B.substTy 0 (.fvar X)) ι ζ η =
      interp W ρ θ B ι ζ (Env.cons P η) := by
  rw [interp_openTy (T := .fvar X) (fun _ _ _ _ _ => rfl)]
  have h1 : tyVal W ρ (TEnv.update θ X P) (.fvar X) ζ η = P := by
    funext ι'
    simp [tyVal, interp]
  rw [h1]
  exact interp_agree hB ρ ρ _ θ _ _ _ _ (fun _ _ => rfl) (TEnv.update_agree hX) (fun _ _ => rfl)
    (fun n hn => by cases n with | zero => rfl | succ n => omega) ι

/-- Opening a size binder at a fresh free size variable. -/
theorem interp_open_fresh_sz {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {k : Nat} {B : Ty} (hB : TyWf Ψ Θ k 1 B) {j : Nat} (hj : j ∉ Ψ.dom) (β : Ordinal.{0})
    (ι : SKind) (η : Env) :
    interp W (SizeVal.update ρ j β) θ (B.openSz 0 (.var j 0)) ι SzEnv.zero η =
      interp W ρ θ B ι (SzEnv.cons β SzEnv.zero) η := by
  rw [interp_openSz0 W _ θ (b := .var j 0) trivial]
  have h1 : sizeVal (SizeVal.update ρ j β) SzEnv.zero (.var j 0) = β := by
    simp [sizeVal, SizeVal.update]
  rw [h1]
  exact interp_agree hB _ ρ θ θ _ _ _ _ (SizeVal.update_agree hj) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) ι

/-! ## Casts between equal simple kinds -/

theorem PSem.ofSem_cast {ι ι' : SKind} (e : ι = ι') (X : Sem ι) :
    PSem.ofSem ι' (cast (congrArg Sem e) X) = PSem.ofSem ι X := by
  subst e; rfl

theorem good_cast {W : World} {κ : Kind} {ι ι' : SKind} (e : ι = ι') (X : Sem ι) :
    Good W κ (cast (congrArg Sem e) X) ↔ Good W κ X := by
  subst e; rfl

/-! ## β-conversion -/

theorem interp_beta {W : World} {Ψ : SizeCtx} {Δ : KCtx} {F G : Ty} {ι : SKind} {κ : Kind}
    (hk : KindingC Ψ Δ (.app (.lam ι F) G ι) κ) (ρ : SizeVal) (θ : TEnv) :
    interp W ρ θ (.app (.lam ι F) G ι) κ.erase SzEnv.zero Env.empty =
      interp W ρ θ (F.substTy 0 G) κ.erase SzEnv.zero Env.empty := by
  obtain ⟨π, κ₁, κ₂, hF, hG, hι, hs⟩ := Kinding.inv_app hk
  obtain ⟨π', κ₁', κ₂', hι', hF', hs'⟩ := Kinding.inv_lam hF
  have e₂ : κ₂'.erase = κ.erase := by
    cases hs' with
    | arr _ _ h2 => exact h2.erase_eq.trans hs.erase_eq
  have hGc : TyWf Ψ (Δ.inv π).dom 0 0 G := hG.tyWf
  rw [interp_app, interp_openTy (envFree_of_closed hGc ρ θ), ← e₂, interp_lam_arr]
  apply interp_agree_kinded hF' ρ θ θ SzEnv.zero
  · intros; rfl
  · intro k π'' κ'' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      subst hι
      rw [hι']
      simp [tyVal]
    | succ k => simp at hk

/-! ## Functors of fixpoints -/

theorem functor_cand {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Δ : KCtx} {R : List Ty}
    {ρ : SizeVal} {θ : TEnv} {π : Pol} (hθ : TRel W Δ θ θ)
    (hR : ∀ T ∈ R, Kinding Ψ (Δ.inv π) ((π, .star) :: BCtx.inv π []) 0 T .star) :
    ∀ d < R.length, ∀ 𝒳, Cand W 𝒳 →
      Cand W (interpAt W ρ θ R d SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty)) := by
  intro d hd 𝒳 h𝒳
  rw [interpAt_eq W ρ θ R d _ _ hd]
  have hBnil : BRel W (BCtx.inv π []) Env.empty Env.empty := fun _ _ _ hk => by simp at hk
  exact (kinding_sound hW (hR _ (List.getElem_mem hd)) ρ θ θ SzEnv.zero _ _ (hθ.inv_refl π)
    (hBnil.cons (κ := .star) h𝒳 h𝒳 (PolRel.refl π (W := W) h𝒳))).1

theorem functor_mono_pos {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Δ : KCtx}
    {S : List Ty} {ρ : SizeVal} {θ : TEnv} (hθ : TRel W Δ θ θ)
    (hpos : ∀ T ∈ S, Kinding Ψ Δ [(.pos, .star)] 0 T .star) :
    ∀ c 𝒳 𝒴, Cand W 𝒳 → Cand W 𝒴 → 𝒳 ⊆ 𝒴 →
      interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty) ⊆
        interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒴) Env.empty) := by
  intro c 𝒳 𝒴 h𝒳 h𝒴 hsub
  by_cases hc : c < S.length
  · rw [interpAt_eq W ρ θ S c _ _ hc, interpAt_eq W ρ θ S c _ _ hc]
    have hBnil : BRel W [] Env.empty Env.empty := fun _ _ _ hk => by simp at hk
    exact (kinding_sound hW (hpos _ (List.getElem_mem hc)) ρ θ θ SzEnv.zero _ _ hθ
      (hBnil.cons (κ := .star) h𝒳 h𝒴 hsub)).2.2
  · rw [interpAt_out W ρ θ S c _ _ (by omega)]
    exact Set.empty_subset _

theorem functor_le {W : World} {Ψ : SizeCtx} {Δ : KCtx} {X : Nat} {S S' : List Ty}
    {ρ : SizeVal} {θ : TEnv} (hX : X ∉ Δ.dom) (hlen : S.length = S'.length)
    (hSw : ∀ T ∈ S, TyWf Ψ Δ.dom 1 0 T) (hSw' : ∀ T ∈ S', TyWf Ψ Δ.dom 1 0 T)
    (hv : ValidVal Ψ ρ) (hb : CtxBoundsWf Ψ) (hθ : TRel W Δ θ θ)
    (ih : ∀ (c : Nat) (T T' : Ty), S[c]? = some T → S'[c]? = some T' →
      ∀ (ρ : SizeVal) (θ : TEnv), ValidVal Ψ ρ → CtxBoundsWf Ψ →
        TRel W (Δ ++ [(X, .mix, .star)]) θ θ →
        KSound W .star (interp W ρ θ (T.substTy 0 (.fvar X)) Kind.star.erase SzEnv.zero Env.empty)
          (interp W ρ θ (T'.substTy 0 (.fvar X)) Kind.star.erase SzEnv.zero Env.empty)) :
    ∀ c 𝒳, Cand W 𝒳 →
      interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty) ⊆
        interpAt W ρ θ S' c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty) := by
  intro c 𝒳 h𝒳
  by_cases hc : c < S.length
  · have hc' : c < S'.length := hlen ▸ hc
    rw [interpAt_eq W ρ θ S c _ _ hc, interpAt_eq W ρ θ S' c _ _ hc']
    have h := ih c _ _ (List.getElem?_eq_getElem hc) (List.getElem?_eq_getElem hc') ρ
      (TEnv.update θ X (PSem.ofSem Kind.star.erase 𝒳)) hv hb (hθ.extend hX (κ := .star) h𝒳)
    simp only [Kind.erase_star] at h
    rw [interp_open_fresh_ty (hSw _ (List.getElem_mem hc)) hX,
      interp_open_fresh_ty (hSw' _ (List.getElem_mem hc')) hX] at h
    exact h.2.2
  · rw [interpAt_out W ρ θ S c _ _ (by omega)]
    exact Set.empty_subset _

/-- Stages of `μ` are ordered along bound normalization. -/
theorem muSet_up_mono {W : World} {F : Nat → Set Tm → Set Tm} {ρ : SizeVal} {a b : Size}
    (h : sizeVal ρ SzEnv.zero a.up ≤ sizeVal ρ SzEnv.zero b.up ∨
      sizeVal ρ SzEnv.zero a ≤ sizeVal ρ SzEnv.zero b.up) :
    MuSet W F (sizeVal ρ SzEnv.zero a) ⊆ MuSet W F (sizeVal ρ SzEnv.zero b) := by
  have h' : sizeVal ρ SzEnv.zero a ≤ sizeVal ρ SzEnv.zero b ∨
      (Omega ≤ sizeVal ρ SzEnv.zero a ∧ Omega ≤ sizeVal ρ SzEnv.zero b) := by
    rcases h with h | h
    · exact le_of_up_le ρ SzEnv.zero a b h
    · exact le_of_le_up ρ SzEnv.zero a b h
  rcases h' with hab | ⟨ha, hb⟩
  · exact muSet_mono_ord hab
  · rw [muSet_ge_omega W F ha, muSet_ge_omega W F hb]

theorem nuSet_up_anti {W : World} {n : Nat} {G : Nat → Set Tm → Set Tm} {ρ : SizeVal}
    {a b : Size} (h : sizeVal ρ SzEnv.zero b.up ≤ sizeVal ρ SzEnv.zero a.up ∨
      sizeVal ρ SzEnv.zero b ≤ sizeVal ρ SzEnv.zero a.up) :
    NuSet W n G (sizeVal ρ SzEnv.zero a) ⊆ NuSet W n G (sizeVal ρ SzEnv.zero b) := by
  have h' : sizeVal ρ SzEnv.zero b ≤ sizeVal ρ SzEnv.zero a ∨
      (Omega ≤ sizeVal ρ SzEnv.zero b ∧ Omega ≤ sizeVal ρ SzEnv.zero a) := by
    rcases h with h | h
    · exact le_of_up_le ρ SzEnv.zero b a h
    · exact le_of_le_up ρ SzEnv.zero b a h
  rcases h' with hba | ⟨hb, ha⟩
  · exact nuSet_anti_ord hba
  · rw [nuSet_ge_omega W n G ha, nuSet_ge_omega W n G hb]

/-! ## Soundness of subtyping -/

theorem subTy_sound {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Δ : KCtx} {A B : Ty}
    {κ : Kind} (h : SubTy Ψ Δ A B κ) :
    ∀ (ρ : SizeVal) (θ : TEnv), ValidVal Ψ ρ → CtxBoundsWf Ψ → TRel W Δ θ θ →
      KSound W κ (interp W ρ θ A κ.erase SzEnv.zero Env.empty)
        (interp W ρ θ B κ.erase SzEnv.zero Env.empty) := by
  have hBnil : ∀ η η' : Env, BRel W [] η η' := fun _ _ k _ _ hk => by simp at hk
  induction h with
  | refl hA =>
    intro ρ θ _ _ hθ
    exact kinding_sound hW hA ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
  | trans _ _ ih₁ ih₂ =>
    intro ρ θ hv hb hθ
    have h₁ := ih₁ ρ θ hv hb hθ
    have h₂ := ih₂ ρ θ hv hb hθ
    exact ⟨h₁.1, h₂.2.1, SemLe.trans h₁.1 h₁.2.1 h₂.2.1 h₁.2.2 h₂.2.2⟩
  | beta_l hk _ ih =>
    intro ρ θ hv hb hθ
    rw [interp_beta hk ρ θ]
    exact ih ρ θ hv hb hθ
  | beta_r hk _ ih =>
    intro ρ θ hv hb hθ
    rw [interp_beta hk ρ θ]
    exact ih ρ θ hv hb hθ
  | prod _ _ ihA ihB =>
    intro ρ θ hv hb hθ
    have hA := ihA ρ θ hv hb hθ
    have hB := ihB ρ θ hv hb hθ
    simp only [Kind.erase_star, interp_prod_star] at hA hB ⊢
    exact ⟨introSet_cand hW _, introSet_cand hW _, prodSet_mono hA.2.2 hB.2.2⟩
  | arr _ _ ihA ihB =>
    intro ρ θ hv hb hθ
    have hA := ihA ρ θ hv hb hθ
    have hB := ihB ρ θ hv hb hθ
    simp only [Kind.erase_star, interp_arr_star] at hA hB ⊢
    exact ⟨arrSet_cand hW hA.2.1 hB.1, arrSet_cand hW hA.1 hB.2.1, arrSet_mono hA.2.2 hB.2.2⟩
  | @app Ψ Δ F F' G G' ι π κ₁ κ₂ _ _ _ hG hG' hι ihF ihGpos ihGneg =>
    intro ρ θ hv hb hθ
    subst hι
    have hF := ihF ρ θ hv hb hθ
    simp only [Kind.erase_arr] at hF
    have hGs := kinding_sound hW hG ρ θ θ SzEnv.zero Env.empty Env.empty (hθ.inv_refl π)
      (hBnil _ _)
    have hGs' := kinding_sound hW hG' ρ θ θ SzEnv.zero Env.empty Env.empty (hθ.inv_refl π)
      (hBnil _ _)
    have hrel : PolRel W π κ₁ (interp W ρ θ G κ₁.erase SzEnv.zero Env.empty)
        (interp W ρ θ G' κ₁.erase SzEnv.zero Env.empty) := by
      cases π with
      | pos => exact (ihGpos trivial ρ θ hv hb hθ).2.2
      | neg => exact (ihGneg trivial ρ θ hv hb hθ).2.2
      | mix => exact ⟨(ihGpos trivial ρ θ hv hb hθ).2.2, (ihGneg trivial ρ θ hv hb hθ).2.2⟩
      | top => trivial
    rw [interp_app, interp_app]
    exact ⟨hF.1.1 _ hGs.1, hF.2.1.1 _ hGs'.1, hF.2.2 _ _ hGs.1 hGs'.1 hrel⟩
  | @lam Ψ Δ F F' ι ι' π κ₁ κ₂ X hX _ hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    obtain ⟨π₁, κ₁₁, κ₂₁, _, hFk, _⟩ := Kinding.inv_lam hk
    obtain ⟨π₂, κ₁₂, κ₂₂, _, hFk', _⟩ := Kinding.inv_lam hk'
    have hFw : TyWf Ψ Δ.dom 1 0 F := by simpa using hFk.tyWf
    have hFw' : TyWf Ψ Δ.dom 1 0 F' := by simpa using hFk'.tyWf
    have hgF : ∀ Y : Sem κ₁.erase, Good W κ₁ Y → Good W κ₂
        (interp W ρ θ F κ₂.erase SzEnv.zero (Env.cons (PSem.ofSem κ₁.erase Y) Env.empty)) :=
      fun Y hY => hs.1.1 Y hY
    have hgF' : ∀ Y : Sem κ₁.erase, Good W κ₁ Y → Good W κ₂
        (interp W ρ θ F' κ₂.erase SzEnv.zero (Env.cons (PSem.ofSem κ₁.erase Y) Env.empty)) :=
      fun Y hY => hs'.1.1 Y hY
    have hmF' : ∀ Y Z : Sem κ₁.erase, Good W κ₁ Y → Good W κ₁ Z → PolRel W π κ₁ Y Z →
        SemLe W κ₂
          (interp W ρ θ F' κ₂.erase SzEnv.zero (Env.cons (PSem.ofSem κ₁.erase Y) Env.empty))
          (interp W ρ θ F' κ₂.erase SzEnv.zero (Env.cons (PSem.ofSem κ₁.erase Z) Env.empty)) :=
      fun Y Z hY hZ hYZ => hs'.1.2 Y Z hY hZ hYZ
    intro Y Z hY hZ hYZ
    have hY' := ih ρ (TEnv.update θ X (PSem.ofSem κ₁.erase Y)) hv hb (hθ.extend hX hY)
    rw [interp_open_fresh_ty hFw hX, interp_open_fresh_ty hFw' hX] at hY'
    exact SemLe.trans (hgF Y hY) (hgF' Y hY) (hgF' Z hZ) hY'.2.2 (hmF' Y Z hY hZ hYZ)
  | @allT Ψ Δ κ κ' B B' X hsub hX _ hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_allT_star]
    have hBw : TyWf Ψ Δ.dom 1 0 B := by simpa using (Kinding.inv_allT hk).2.tyWf
    have hBw' : TyWf Ψ Δ.dom 1 0 B' := by simpa using (Kinding.inv_allT hk').2.tyWf
    intro t ht
    refine ⟨ht.1, fun Y hY => ?_⟩
    have e := hsub.erase_eq
    have hY' : Good W κ' (cast (congrArg Sem e) Y) := (good_cast e Y).mpr (Good.sub hsub hY)
    have h1 : Tm.app t .inst ∈
        interpT W ρ θ B SzEnv.zero (Env.cons (PSem.ofSem κ.erase Y) Env.empty) := by
      have := ht.2 _ hY'
      rw [← PSem.ofSem_cast e Y]
      exact this
    have hih := ih ρ (TEnv.update θ X (PSem.ofSem κ.erase Y)) hv hb (hθ.extend hX hY)
    simp only [Kind.erase_star] at hih
    rw [interp_open_fresh_ty hBw hX, interp_open_fresh_ty hBw' hX] at hih
    exact hih.2.2 h1
  | @exT Ψ Δ κ κ' B B' X hsub hX _ hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_exT_star]
    have hBw : TyWf Ψ Δ.dom 1 0 B := by simpa using (Kinding.inv_exT hk).2.tyWf
    have hBw' : TyWf Ψ Δ.dom 1 0 B' := by simpa using (Kinding.inv_exT hk').2.tyWf
    apply introSet_mono
    rintro v ⟨t, Y, rfl, hY, ht⟩
    have e := hsub.erase_eq
    refine ⟨t, cast (congrArg Sem e) Y, rfl, (good_cast e Y).mpr (Good.sub hsub hY), ?_⟩
    have hih := ih ρ (TEnv.update θ X (PSem.ofSem κ.erase Y)) hv hb (hθ.extend hX hY)
    simp only [Kind.erase_star] at hih
    rw [interp_open_fresh_ty hBw hX, interp_open_fresh_ty hBw' hX] at hih
    have h2 : t ∈ interpT W ρ θ B' SzEnv.zero (Env.cons (PSem.ofSem κ.erase Y) Env.empty) :=
      hih.2.2 ht
    rw [← PSem.ofSem_cast e Y] at h2
    exact h2
  | @allS Ψ Δ a b B B' j hle hj _ hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_allS_star]
    obtain ⟨_, ha, hBk⟩ := Kinding.inv_allS hk
    obtain ⟨_, hbw, hBk'⟩ := Kinding.inv_allS hk'
    have hBw := hBk.tyWf
    have hBw' := hBk'.tyWf
    have hba := sizeLe_sound hv hle
    intro t ht
    refine ⟨ht.1, fun β hβ => ?_⟩
    have h1 := ht.2 β (lt_of_lt_of_le hβ hba)
    have hih := ih (SizeVal.update ρ j β) θ (hv.extend hb hj hbw hβ) (hb.extend hbw) hθ
    simp only [Kind.erase_star] at hih
    rw [interp_open_fresh_sz hBw hj, interp_open_fresh_sz hBw' hj] at hih
    exact hih.2.2 h1
  | @exS Ψ Δ a b B B' j hle hj _ hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_exS_star]
    obtain ⟨_, ha, hBk⟩ := Kinding.inv_exS hk
    obtain ⟨_, hbw, hBk'⟩ := Kinding.inv_exS hk'
    have hBw := hBk.tyWf
    have hBw' := hBk'.tyWf
    have hab := sizeLe_sound hv hle
    apply introSet_mono
    rintro v ⟨t, β, rfl, hβ, ht⟩
    refine ⟨t, β, rfl, lt_of_lt_of_le hβ hab, ?_⟩
    have hih := ih (SizeVal.update ρ j β) θ (hv.extend hb hj ha hβ) (hb.extend ha) hθ
    simp only [Kind.erase_star] at hih
    rw [interp_open_fresh_sz hBw hj, interp_open_fresh_sz hBw' hj] at hih
    exact hih.2.2 ht
  | @mu_pos Ψ Δ a b S S' X hle hlen hX _ hpos hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_mu_star]
    obtain ⟨_, π, _, _, hS⟩ := Kinding.inv_mu hk
    obtain ⟨_, π', _, _, hS'⟩ := Kinding.inv_mu hk'
    have hSw : ∀ T ∈ S, TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hS T hT).tyWf
    have hSw' : ∀ T ∈ S', TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hS' T hT).tyWf
    have hle' := hle.imp (sizeLe_sound hv) (sizeLe_sound hv)
    refine Set.Subset.trans (muSet_mono_cand hW ?_ _) (muSet_up_mono hle')
    intro c 𝒳 𝒴 h𝒳 h𝒴 hsub
    exact Set.Subset.trans (functor_le hX hlen hSw hSw' hv hb hθ ih c 𝒳 h𝒳)
      (functor_mono_pos hW hθ hpos c 𝒳 𝒴 h𝒳 h𝒴 hsub)
  | @mu_eqv Ψ Δ a b S S' X hle hlen hX _ _ hk hk' ih₁ ih₂ =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_mu_star]
    obtain ⟨_, π, _, _, hS⟩ := Kinding.inv_mu hk
    obtain ⟨_, π', _, _, hS'⟩ := Kinding.inv_mu hk'
    have hSw : ∀ T ∈ S, TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hS T hT).tyWf
    have hSw' : ∀ T ∈ S', TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hS' T hT).tyWf
    have hle' := hle.imp (sizeLe_sound hv) (sizeLe_sound hv)
    have ih₂' : ∀ (c : Nat) (T T' : Ty), S'[c]? = some T → S[c]? = some T' →
        ∀ (ρ : SizeVal) (θ : TEnv), ValidVal Ψ ρ → CtxBoundsWf Ψ →
          TRel W (Δ ++ [(X, .mix, .star)]) θ θ →
          KSound W .star
            (interp W ρ θ (T.substTy 0 (.fvar X)) Kind.star.erase SzEnv.zero Env.empty)
            (interp W ρ θ (T'.substTy 0 (.fvar X)) Kind.star.erase SzEnv.zero Env.empty) :=
      fun c T T' h1 h2 => ih₂ c T' T h2 h1
    refine Set.Subset.trans (subset_of_eq (muSet_congr_cand hW ?_ _)) (muSet_up_mono hle')
    intro c 𝒳 h𝒳
    exact Set.Subset.antisymm (functor_le hX hlen hSw hSw' hv hb hθ ih₁ c 𝒳 h𝒳)
      (functor_le hX hlen.symm hSw' hSw hv hb hθ ih₂' c 𝒳 h𝒳)
  | @nu_pos Ψ Δ a b R R' X hle hlen hX _ hpos hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_nu_star]
    obtain ⟨_, π, _, _, hR⟩ := Kinding.inv_nu hk
    obtain ⟨_, π', _, _, hR'⟩ := Kinding.inv_nu hk'
    have hRw : ∀ T ∈ R, TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hR T hT).tyWf
    have hRw' : ∀ T ∈ R', TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hR' T hT).tyWf
    have hle' := hle.imp (sizeLe_sound hv) (sizeLe_sound hv)
    rw [← hlen]
    refine Set.Subset.trans (nuSet_mono_cand hW (functor_cand hW hθ hR)
      (hlen ▸ functor_cand hW hθ hR') ?_ _) (nuSet_up_anti hle')
    intro d _ 𝒳 𝒴 h𝒳 h𝒴 hsub
    exact Set.Subset.trans (functor_le hX hlen hRw hRw' hv hb hθ ih d 𝒳 h𝒳)
      (functor_mono_pos hW hθ hpos d 𝒳 𝒴 h𝒳 h𝒴 hsub)
  | @nu_eqv Ψ Δ a b R R' X hle hlen hX _ _ hk hk' ih₁ ih₂ =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_nu_star]
    obtain ⟨_, π, _, _, hR⟩ := Kinding.inv_nu hk
    obtain ⟨_, π', _, _, hR'⟩ := Kinding.inv_nu hk'
    have hRw : ∀ T ∈ R, TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hR T hT).tyWf
    have hRw' : ∀ T ∈ R', TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hR' T hT).tyWf
    have hle' := hle.imp (sizeLe_sound hv) (sizeLe_sound hv)
    have ih₂' : ∀ (c : Nat) (T T' : Ty), R'[c]? = some T → R[c]? = some T' →
        ∀ (ρ : SizeVal) (θ : TEnv), ValidVal Ψ ρ → CtxBoundsWf Ψ →
          TRel W (Δ ++ [(X, .mix, .star)]) θ θ →
          KSound W .star
            (interp W ρ θ (T.substTy 0 (.fvar X)) Kind.star.erase SzEnv.zero Env.empty)
            (interp W ρ θ (T'.substTy 0 (.fvar X)) Kind.star.erase SzEnv.zero Env.empty) :=
      fun c T T' h1 h2 => ih₂ c T' T h2 h1
    rw [← hlen]
    refine Set.Subset.trans (subset_of_eq (nuSet_congr_cand hW (functor_cand hW hθ hR) ?_ _))
      (nuSet_up_anti hle')
    intro d _ 𝒳 h𝒳
    exact Set.Subset.antisymm (functor_le hX hlen hRw hRw' hv hb hθ ih₁ d 𝒳 h𝒳)
      (functor_le hX hlen.symm hRw' hRw hv hb hθ ih₂' d 𝒳 h𝒳)

end NishtAbel2024V5
