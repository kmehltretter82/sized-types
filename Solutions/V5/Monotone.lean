import Solutions.V5.Cand

/-! # V5: monotonicity of the interpretation -/

namespace NishtAbel2024V5

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

theorem allTSet_mono {W : World} {κ : Kind} {F F' : Sem κ.erase → Set Tm}
    (h : ∀ X, Good W κ X → F X ⊆ F' X) : AllTSet W κ F ⊆ AllTSet W κ F' :=
  fun _ ht => ⟨ht.1, fun 𝒳 h𝒳 => h 𝒳 h𝒳 (ht.2 𝒳 h𝒳)⟩

theorem exTSet_mono {W : World} {κ : Kind} {F F' : Sem κ.erase → Set Tm}
    (h : ∀ X, Good W κ X → F X ⊆ F' X) : ExTSet W κ F ⊆ ExTSet W κ F' :=
  introSet_mono fun _ ⟨t, 𝒳, hv, h𝒳, ht⟩ => ⟨t, 𝒳, hv, h𝒳, h 𝒳 h𝒳 ht⟩

theorem allSSet_mono {W : World} {α : Ordinal.{0}} {F F' : Ordinal.{0} → Set Tm}
    (h : ∀ β, F β ⊆ F' β) : AllSSet W α F ⊆ AllSSet W α F' :=
  fun _ ht => ⟨ht.1, fun β hβ => h β (ht.2 β hβ)⟩

theorem exSSet_mono {W : World} {α : Ordinal.{0}} {F F' : Ordinal.{0} → Set Tm}
    (h : ∀ β, F β ⊆ F' β) : ExSSet W α F ⊆ ExSSet W α F' :=
  introSet_mono fun _ ⟨t, β, hv, hβ, ht⟩ => ⟨t, β, hv, hβ, h β ht⟩

end NishtAbel2024V5
