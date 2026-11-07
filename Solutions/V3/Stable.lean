import Solutions.V3.Monotone
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

/-! # V3: `Ω` and stabilization of the `μ`/`ν` stages -/

namespace NishtAbel2024V3

open Cardinal Ordinal Order Set

instance : Infinite Tm := Infinite.of_injective Tm.var (fun a b h => by cases h; rfl)

theorem omega_isSuccLimit : IsSuccLimit Omega := by
  unfold Omega
  apply Cardinal.isSuccLimit_ord
  exact (Cardinal.aleph0_le_mk Tm).trans (Order.le_succ _)

theorem add_nat_lt_omega {α : Ordinal.{0}} (h : α < Omega) (n : Nat) : α + n < Omega := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, Ordinal.add_one_eq_succ]
    exact omega_isSuccLimit.succ_lt ih

/-- An increasing family of term sets is constant on some successor step below `Ω`. -/
theorem exists_succ_subset_of_mono {P : Ordinal.{0} → Set Tm} (hP : Monotone P) :
    ∃ β < Omega, P (succ β) ⊆ P β := by
  by_contra h
  push_neg at h
  have hex : ∀ β, β < Omega → ∃ v, v ∈ P (succ β) ∧ v ∉ P β :=
    fun β hβ => Set.not_subset.mp (h β hβ)
  classical
  let g : Ordinal.{0} → Tm := fun β => if hβ : β < Omega then (hex β hβ).choose else .unit
  apply Cardinal.not_injective_limitation_set g
  have key : ∀ β₁ β₂, β₁ < Omega → β₂ < Omega → β₁ < β₂ → g β₁ ≠ g β₂ := by
    intro β₁ β₂ h₁ h₂ hlt heq
    have m1 := (hex β₁ h₁).choose_spec.1
    have m2 := (hex β₂ h₂).choose_spec.2
    simp only [g, dif_pos h₁, dif_pos h₂] at heq
    rw [heq] at m1
    exact m2 (hP (Order.succ_le_of_lt hlt) m1)
  intro β₁ h₁ β₂ h₂ heq
  have h₁' : β₁ < Omega := h₁
  have h₂' : β₂ < Omega := h₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key β₁ β₂ h₁' h₂' hlt heq
  · exact key β₂ β₁ h₂' h₁' hlt heq.symm

/-- A decreasing family of term sets is constant on some successor step below `Ω`. -/
theorem exists_subset_succ_of_anti {N : Ordinal.{0} → Set Tm} (hN : Antitone N) :
    ∃ β < Omega, N β ⊆ N (succ β) := by
  by_contra h
  push_neg at h
  have hex : ∀ β, β < Omega → ∃ v, v ∈ N β ∧ v ∉ N (succ β) :=
    fun β hβ => Set.not_subset.mp (h β hβ)
  classical
  let g : Ordinal.{0} → Tm := fun β => if hβ : β < Omega then (hex β hβ).choose else .unit
  apply Cardinal.not_injective_limitation_set g
  have key : ∀ β₁ β₂, β₁ < Omega → β₂ < Omega → β₁ < β₂ → g β₁ ≠ g β₂ := by
    intro β₁ β₂ h₁ h₂ hlt heq
    have m1 := (hex β₁ h₁).choose_spec.2
    have m2 := (hex β₂ h₂).choose_spec.1
    simp only [g, dif_pos h₁, dif_pos h₂] at heq
    rw [← heq] at m2
    exact m1 (hN (Order.succ_le_of_lt hlt) m2)
  intro β₁ h₁ β₂ h₂ heq
  have h₁' : β₁ < Omega := h₁
  have h₂' : β₂ < Omega := h₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key β₁ β₂ h₁' h₂' hlt heq
  · exact key β₂ β₁ h₂' h₁' hlt heq.symm

/-- The value predicate of stage `α` of an inductive type. -/
def MuPred (W : World) (F : Nat → Set Tm → Set Tm) (α : Ordinal.{0}) : Set Tm :=
  fun v => ∃ c t β, ∃ _ : β < α, v = .cons c t ∧ t ∈ F c (MuSet W F β)

theorem MuSet_eq' (W : World) (F : Nat → Set Tm → Set Tm) (α : Ordinal.{0}) :
    MuSet W F α = IntroSet W (MuPred W F α) := MuSet_eq W F α

/-- The stages of an inductive type are constant from some `β₀ < Ω` on. -/
theorem muSet_stable (W : World) (F : Nat → Set Tm → Set Tm) :
    ∃ β₀ < Omega, MuSet W F β₀ = MuSet W F Omega := by
  have hmono : Monotone (MuPred W F) := by
    intro α α' h v ⟨c, t, β, hβ, hv, ht⟩
    exact ⟨c, t, β, lt_of_lt_of_le hβ h, hv, ht⟩
  obtain ⟨β₀, hβ₀, hstep⟩ := exists_succ_subset_of_mono hmono
  have hconst : ∀ γ, β₀ ≤ γ → MuPred W F γ = MuPred W F β₀ := by
    intro γ
    induction γ using WellFoundedLT.induction with
    | _ γ ih =>
      intro hγ
      apply Set.Subset.antisymm _ (hmono hγ)
      rintro v ⟨c, t, β, hβ, hv, ht⟩
      by_cases hlt : β < β₀
      · exact ⟨c, t, β, hlt, hv, ht⟩
      · have hβeq : MuSet W F β = MuSet W F β₀ := by
          rw [MuSet_eq', MuSet_eq', ih β hβ (not_lt.mp hlt)]
        rw [hβeq] at ht
        exact hstep ⟨c, t, β₀, Order.lt_succ β₀, hv, ht⟩
  refine ⟨β₀, hβ₀, ?_⟩
  rw [MuSet_eq', MuSet_eq', hconst Omega hβ₀.le]

/-- The stages of a coinductive type are constant from some `β₀ < Ω` on. -/
theorem nuSet_stable (W : World) (n : Nat) (G : Nat → Set Tm → Set Tm) :
    ∃ β₀ < Omega, NuSet W n G β₀ = NuSet W n G Omega := by
  have hanti : Antitone (NuSet W n G) := fun α α' h => nuSet_anti_ord h
  obtain ⟨β₀, hβ₀, hstep⟩ := exists_subset_succ_of_anti hanti
  have hconst : ∀ γ, β₀ ≤ γ → NuSet W n G γ = NuSet W n G β₀ := by
    intro γ
    induction γ using WellFoundedLT.induction with
    | _ γ ih =>
      intro hγ
      apply Set.Subset.antisymm (hanti hγ)
      intro t ht
      have ht' := hstep ht
      rw [NuSet_eq] at ht'
      have ht0 := ht
      rw [NuSet_eq] at ht0
      rw [NuSet_eq]
      refine ⟨ht0.1, ?_⟩
      intro β hβ d hd
      by_cases hlt : β < β₀
      · exact ht0.2 β hlt d hd
      · rw [ih β hβ (not_lt.mp hlt)]
        exact ht'.2 β₀ (Order.lt_succ β₀) d hd
  exact ⟨β₀, hβ₀, (hconst Omega hβ₀.le).symm⟩

/-- `μ^∞` is closed under constructors: a payload at stage `Ω` is a payload at some stage below. -/
theorem muSet_omega_closed {W : World} {F : Nat → Set Tm → Set Tm} {c : Nat} {t : Tm}
    (ht : t ∈ F c (MuSet W F Omega)) : ∃ β < Omega, t ∈ F c (MuSet W F β) := by
  obtain ⟨β₀, hβ₀, heq⟩ := muSet_stable W F
  exact ⟨β₀, hβ₀, by rw [heq]; exact ht⟩

/-- Projections of `ν^∞` land at stage `Ω`. -/
theorem nuSet_omega_proj {W : World} {n : Nat} {G : Nat → Set Tm → Set Tm} {t : Tm}
    (ht : t ∈ NuSet W n G Omega) {d : Nat} (hd : d < n) :
    Tm.app t (.proj d) ∈ G d (NuSet W n G Omega) := by
  obtain ⟨β₀, hβ₀, heq⟩ := nuSet_stable W n G
  rw [NuSet_eq] at ht
  rw [← heq]
  exact ht.2 β₀ hβ₀ d hd

end NishtAbel2024V3
