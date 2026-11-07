import Solutions.V4.Cand

/-! # V4: monotonicity of the interpretation -/

namespace NishtAbel2024V4

theorem introSet_mono {W : World} {P Q : Tm → Prop} (h : ∀ v, P v → Q v) :
    IntroSet W P ⊆ IntroSet W Q :=
  fun _ ht => ⟨ht.1, fun v hv hi => h v (ht.2 v hv hi)⟩

theorem arrSet_mono {W : World} {𝒜 𝒜' ℬ ℬ' : Set Tm} (hA : 𝒜' ⊆ 𝒜) (hB : ℬ ⊆ ℬ') :
    ArrSet W 𝒜 ℬ ⊆ ArrSet W 𝒜' ℬ' :=
  fun _ ht => ⟨ht.1, fun s hs => hB (ht.2 s (hA hs))⟩

theorem prodSet_mono {W : World} {𝒜 𝒜' ℬ ℬ' : Set Tm} (hA : 𝒜 ⊆ 𝒜') (hB : ℬ ⊆ ℬ') :
    ProdSet W 𝒜 ℬ ⊆ ProdSet W 𝒜' ℬ' :=
  introSet_mono fun _ ⟨t, u, hv, ht, hu⟩ => ⟨t, u, hv, hA ht, hB hu⟩

/-- Monotone set operators. -/
def SetMono (F : Set Tm → Set Tm) : Prop := ∀ 𝒳 𝒴, 𝒳 ⊆ 𝒴 → F 𝒳 ⊆ F 𝒴

theorem muSet_mono_ord {W : World} {F : Nat → Set Tm → Set Tm} {α α' : Ordinal.{0}}
    (h : α ≤ α') : MuSet W F α ⊆ MuSet W F α' := by
  rw [MuSet_eq, MuSet_eq]
  exact introSet_mono fun _ ⟨c, t, β, hβ, hv, ht⟩ => ⟨c, t, β, lt_of_lt_of_le hβ h, hv, ht⟩

theorem nuSet_anti_ord {W : World} {n : Nat} {G : Nat → Set Tm → Set Tm} {α α' : Ordinal.{0}}
    (h : α ≤ α') : NuSet W n G α' ⊆ NuSet W n G α := by
  rw [NuSet_eq, NuSet_eq]
  exact fun _ ht => ⟨ht.1, fun β hβ d hd => ht.2 β (lt_of_lt_of_le hβ h) d hd⟩

theorem muSet_mono_fun {W : World} {F F' : Nat → Set Tm → Set Tm}
    (hle : ∀ c 𝒳, F c 𝒳 ⊆ F' c 𝒳) (hmono : ∀ c, SetMono (F' c)) (α : Ordinal.{0}) :
    MuSet W F α ⊆ MuSet W F' α := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [MuSet_eq, MuSet_eq]
    exact introSet_mono fun _ ⟨c, t, β, hβ, hv, ht⟩ =>
      ⟨c, t, β, hβ, hv, hmono c _ _ (ih β hβ) (hle c _ ht)⟩

theorem nuSet_mono_fun {W : World} {n : Nat} {G G' : Nat → Set Tm → Set Tm}
    (hle : ∀ d < n, ∀ 𝒳, G d 𝒳 ⊆ G' d 𝒳) (hmono : ∀ d < n, SetMono (G' d)) (α : Ordinal.{0}) :
    NuSet W n G α ⊆ NuSet W n G' α := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [NuSet_eq, NuSet_eq]
    exact fun _ ht => ⟨ht.1, fun β hβ d hd =>
      hmono d hd _ _ (ih β hβ) (hle d hd _ (ht.2 β hβ d hd))⟩

theorem interpAt_out (W : World) (ρ : SizeVal) (θ : TEnv) :
    ∀ (S : List Ty) (c : Nat) (ζ : SzEnv) (η : Env), S.length ≤ c → interpAt W ρ θ S c ζ η = ∅
  | [], c, ζ, η, _ => by cases c <;> rfl
  | A :: S, 0, ζ, η, h => by simp at h
  | A :: S, c + 1, ζ, η, h => by
    simp only [interpAt]
    exact interpAt_out W ρ θ S c ζ η (by simpa using h)

/-- Two environments that agree except at `j`, where the first is contained in the second. -/
def EnvLe (j : Nat) (η η' : Env) : Prop := (∀ X, X ≠ j → η X = η' X) ∧ η j ⊆ η' j

theorem EnvLe.cons {j : Nat} {η η' : Env} (h : EnvLe j η η') (𝒳 : Set Tm) :
    EnvLe (j + 1) (Env.cons 𝒳 η) (Env.cons 𝒳 η') := by
  refine ⟨?_, h.2⟩
  intro X hX
  cases X with
  | zero => rfl
  | succ X => exact h.1 X (by omega)

theorem EnvLe.at_zero {𝒳 𝒴 : Set Tm} (η : Env) (h : 𝒳 ⊆ 𝒴) :
    EnvLe 0 (Env.cons 𝒳 η) (Env.cons 𝒴 η) := by
  refine ⟨?_, h⟩
  intro X hX
  cases X with
  | zero => exact absurd rfl hX
  | succ X => rfl

theorem allTSet_mono {W : World} {F F' : Set Tm → Set Tm} (h : ∀ 𝒳, F 𝒳 ⊆ F' 𝒳) :
    AllTSet W F ⊆ AllTSet W F' :=
  fun _ ht => ⟨ht.1, fun 𝒳 h𝒳 => h 𝒳 (ht.2 𝒳 h𝒳)⟩

theorem exTSet_mono {W : World} {F F' : Set Tm → Set Tm} (h : ∀ 𝒳, F 𝒳 ⊆ F' 𝒳) :
    ExTSet W F ⊆ ExTSet W F' :=
  introSet_mono fun _ ⟨t, 𝒳, hv, h𝒳, ht⟩ => ⟨t, 𝒳, hv, h𝒳, h 𝒳 ht⟩

theorem allSSet_mono {W : World} {α : Ordinal.{0}} {F F' : Ordinal.{0} → Set Tm}
    (h : ∀ β, F β ⊆ F' β) : AllSSet W α F ⊆ AllSSet W α F' :=
  fun _ ht => ⟨ht.1, fun β hβ => h β (ht.2 β hβ)⟩

theorem exSSet_mono {W : World} {α : Ordinal.{0}} {F F' : Ordinal.{0} → Set Tm}
    (h : ∀ β, F β ⊆ F' β) : ExSSet W α F ⊆ ExSSet W α F' :=
  introSet_mono fun _ ⟨t, β, hv, hβ, ht⟩ => ⟨t, β, hv, hβ, h β ht⟩

/-- Positivity gives monotonicity, negativity antitonicity. -/
theorem interp_mono {W : World} (ρ : SizeVal) (θ : TEnv) {Ψ : SizeCtx} {Θ : List Nat}
    {n m : Nat} {A : Ty} (hA : TyWf Ψ Θ n m A) :
    ∀ (b : Bool) (j : Nat) (ζ : SzEnv) (η η' : Env), PolIn b j A → EnvLe j η η' →
      (b = true → interp W ρ θ A ζ η ⊆ interp W ρ θ A ζ η') ∧
      (b = false → interp W ρ θ A ζ η' ⊆ interp W ρ θ A ζ η) := by
  induction hA with
  | unit k =>
    intro b j ζ η η' _ _
    exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  | prod _ _ ihA ihB =>
    intro b j ζ η η' hp he
    cases hp with
    | prod hpA hpB =>
      have hA' := ihA b j ζ η η' hpA he
      have hB' := ihB b j ζ η η' hpB he
      exact ⟨fun hb => prodSet_mono (hA'.1 hb) (hB'.1 hb),
        fun hb => prodSet_mono (hA'.2 hb) (hB'.2 hb)⟩
  | arr _ _ ihA ihB =>
    intro b j ζ η η' hp he
    cases hp with
    | arr hpA hpB =>
      have hA' := ihA (!b) j ζ η η' hpA he
      have hB' := ihB b j ζ η η' hpB he
      refine ⟨fun hb => arrSet_mono (hA'.2 (by simp [hb])) (hB'.1 hb),
        fun hb => arrSet_mono (hA'.1 (by simp [hb])) (hB'.2 hb)⟩
  | var hX =>
    rename_i k m' X
    intro b j ζ η η' hp he
    cases hp with
    | var_self => exact ⟨fun _ => he.2, fun h => by cases h⟩
    | var_other hne =>
      simp only [interp]
      rw [he.1 X hne]
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  | fvar _ =>
    intro b j ζ η η' _ _
    exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  | @mu k m' a S _ _ hpos ih =>
    intro b j ζ η η' hp he
    have hpS : ∀ T ∈ S, PolIn b (j + 1) T := by cases hp with | mu h => exact h
    have hmono : ∀ (η₀ : Env) c, SetMono (fun 𝒳 => interpAt W ρ θ S c ζ (Env.cons 𝒳 η₀)) := by
      intro η₀ c 𝒳 𝒴 hxy
      by_cases hc : c < S.length
      · simp only [interpAt_eq W ρ θ S c _ _ hc]
        exact (ih _ (List.getElem_mem hc) true 0 ζ _ _ (hpos _ (List.getElem_mem hc))
          (EnvLe.at_zero η₀ hxy)).1 rfl
      · simp [interpAt_out W ρ θ S c _ _ (by omega)]
    have hstep : ∀ c 𝒳, (b = true →
        interpAt W ρ θ S c ζ (Env.cons 𝒳 η) ⊆ interpAt W ρ θ S c ζ (Env.cons 𝒳 η')) ∧
        (b = false →
          interpAt W ρ θ S c ζ (Env.cons 𝒳 η') ⊆ interpAt W ρ θ S c ζ (Env.cons 𝒳 η)) := by
      intro c 𝒳
      by_cases hc : c < S.length
      · simp only [interpAt_eq W ρ θ S c _ _ hc]
        exact ih _ (List.getElem_mem hc) b (j + 1) ζ _ _ (hpS _ (List.getElem_mem hc))
          (he.cons 𝒳)
      · simp [interpAt_out W ρ θ S c _ _ (by omega)]
    simp only [interp]
    exact ⟨fun hb => muSet_mono_fun (fun c 𝒳 => (hstep c 𝒳).1 hb) (fun c => hmono η' c) _,
      fun hb => muSet_mono_fun (fun c 𝒳 => (hstep c 𝒳).2 hb) (fun c => hmono η c) _⟩
  | @nu k m' a R _ _ hpos ih =>
    intro b j ζ η η' hp he
    have hpR : ∀ T ∈ R, PolIn b (j + 1) T := by cases hp with | nu h => exact h
    have hmono : ∀ (η₀ : Env), ∀ d < R.length,
        SetMono (fun 𝒳 => interpAt W ρ θ R d ζ (Env.cons 𝒳 η₀)) := by
      intro η₀ d hd 𝒳 𝒴 hxy
      simp only [interpAt_eq W ρ θ R d _ _ hd]
      exact (ih _ (List.getElem_mem hd) true 0 ζ _ _ (hpos _ (List.getElem_mem hd))
        (EnvLe.at_zero η₀ hxy)).1 rfl
    have hstep : ∀ d < R.length, ∀ 𝒳, (b = true →
        interpAt W ρ θ R d ζ (Env.cons 𝒳 η) ⊆ interpAt W ρ θ R d ζ (Env.cons 𝒳 η')) ∧
        (b = false →
          interpAt W ρ θ R d ζ (Env.cons 𝒳 η') ⊆ interpAt W ρ θ R d ζ (Env.cons 𝒳 η)) := by
      intro d hd 𝒳
      simp only [interpAt_eq W ρ θ R d _ _ hd]
      exact ih _ (List.getElem_mem hd) b (j + 1) ζ _ _ (hpR _ (List.getElem_mem hd))
        (he.cons 𝒳)
    simp only [interp]
    exact ⟨fun hb => nuSet_mono_fun (fun d hd 𝒳 => (hstep d hd 𝒳).1 hb) (hmono η') _,
      fun hb => nuSet_mono_fun (fun d hd 𝒳 => (hstep d hd 𝒳).2 hb) (hmono η) _⟩
  | allT _ ih =>
    intro b j ζ η η' hp he
    have hpB := by cases hp with | allT h => exact h
    have hstep := fun 𝒳 => ih b (j + 1) ζ _ _ hpB (he.cons 𝒳)
    simp only [interp]
    exact ⟨fun hb => allTSet_mono fun 𝒳 => (hstep 𝒳).1 hb,
      fun hb => allTSet_mono fun 𝒳 => (hstep 𝒳).2 hb⟩
  | exT _ ih =>
    intro b j ζ η η' hp he
    have hpB := by cases hp with | exT h => exact h
    have hstep := fun 𝒳 => ih b (j + 1) ζ _ _ hpB (he.cons 𝒳)
    simp only [interp]
    exact ⟨fun hb => exTSet_mono fun 𝒳 => (hstep 𝒳).1 hb,
      fun hb => exTSet_mono fun 𝒳 => (hstep 𝒳).2 hb⟩
  | allS _ _ ih =>
    intro b j ζ η η' hp he
    have hpB := by cases hp with | allS h => exact h
    have hstep := fun β => ih b j (SzEnv.cons β ζ) η η' hpB he
    simp only [interp]
    exact ⟨fun hb => allSSet_mono fun β => (hstep β).1 hb,
      fun hb => allSSet_mono fun β => (hstep β).2 hb⟩
  | exS _ _ ih =>
    intro b j ζ η η' hp he
    have hpB := by cases hp with | exS h => exact h
    have hstep := fun β => ih b j (SzEnv.cons β ζ) η η' hpB he
    simp only [interp]
    exact ⟨fun hb => exSSet_mono fun β => (hstep β).1 hb,
      fun hb => exSSet_mono fun β => (hstep β).2 hb⟩

end NishtAbel2024V4
