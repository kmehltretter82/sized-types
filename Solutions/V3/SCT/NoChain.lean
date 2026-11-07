import Mathlib.Order.WellFounded

universe u

/-- To establish well-foundedness it is enough to rule out descending sequences. -/
theorem NishtAbel2024V3.wellFounded_of_no_descending_sequence {α : Type u} (r : α → α → Prop)
    (h : ∀ f : ℕ → α, (∀ n, r (f (n + 1)) (f n)) → False) : WellFounded r :=
  wellFounded_iff_isEmpty_descending_chain.mpr ⟨fun ⟨f, hf⟩ => h f hf⟩
