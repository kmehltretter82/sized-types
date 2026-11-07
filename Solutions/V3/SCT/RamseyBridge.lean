import Definitions.Def_NishtAbel2024V2_Syntax
import Mathlib.Data.Nat.Nth

namespace NishtAbel2024V2.SCTPort

universe u

theorem homogeneous_pair_subsequence {C : Type} [Finite C] (c : Nat → Nat → C)
    (ramsey : ∀ (color : Finset Nat → C), ∃ (M : Set Nat) (b : C), M.Infinite ∧
      ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b) :
    ∃ (seq : Nat → Nat) (color : C), StrictMono seq ∧
      ∀ i j, i < j → c (seq i) (seq j) = color := by
  classical
  let pairColor (s : Finset Nat) : C :=
    if h : s.Nonempty then c (s.min' h) (s.max' h) else c 0 0
  obtain ⟨M, color, hinf, hcolor⟩ := ramsey pairColor
  refine ⟨Nat.nth (fun n => n ∈ M), color, Nat.nth_strictMono hinf, ?_⟩
  intro i j hij
  have hlt := (Nat.nth_strictMono (p := fun n => n ∈ M) hinf) hij
  have ha := Nat.nth_mem_of_infinite (p := fun n => n ∈ M) hinf i
  have hb := Nat.nth_mem_of_infinite (p := fun n => n ∈ M) hinf j
  have hsub : (↑({Nat.nth (fun n => n ∈ M) i, Nat.nth (fun n => n ∈ M) j} : Finset Nat) : Set Nat) ⊆ M := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
      Set.singleton_subset_iff] using And.intro ha hb
  have hcard : ({Nat.nth (fun n => n ∈ M) i, Nat.nth (fun n => n ∈ M) j} : Finset Nat).card = 2 :=
    Finset.card_pair (ne_of_lt hlt)
  have hc := hcolor _ hsub hcard
  simpa [pairColor, Finset.min'_pair, Finset.max'_pair, min_eq_left (le_of_lt hlt),
    max_eq_right (le_of_lt hlt)] using hc

end NishtAbel2024V2.SCTPort
