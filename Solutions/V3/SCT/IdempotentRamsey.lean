import Solutions.V3.SCT.RamseyBridge
import Mathlib.Data.Finite.Prod

namespace NishtAbel2024V2.SCTPort

universe u

/-- Ramsey extraction of a homogeneous idempotent interval value. -/
theorem homogeneous_idempotent_intervals {Name Graph : Type} {Carrier : Type u} [Finite Name] [Finite Graph]
    (name : Nat → Name) (graph : Nat → Nat → Graph) (val : Graph → Carrier)
    (comp : Carrier → Carrier → Carrier)
    (hcomp : ∀ i j k, i < j → j < k → val (graph i k) = comp (val (graph j k)) (val (graph i j)))
    (ramsey : ∀ (color : Finset Nat → Name × Name × Graph),
      ∃ (M : Set Nat) (b : Name × Name × Graph), M.Infinite ∧
        ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b) :
    ∃ (seq : Nat → Nat) (f : Name) (G : Graph), StrictMono seq ∧
      (∀ i, name (seq i) = f) ∧
      (∀ i j, i < j → graph (seq i) (seq j) = G) ∧ comp (val G) (val G) = val G := by
  obtain ⟨seq, v, hmono, hpair⟩ :=
    homogeneous_pair_subsequence (fun i j => (name i, name j, graph i j)) ramsey
  refine ⟨seq, v.1, v.2.2, hmono, ?_, ?_, ?_⟩
  · intro i
    exact congrArg (fun p : Name × Name × Graph => p.1) (hpair i (i + 1) (Nat.lt_succ_self i))
  · intro i j hij
    exact congrArg (fun p : Name × Name × Graph => p.2.2) (hpair i j hij)
  · have h01 : graph (seq 0) (seq 1) = v.2.2 :=
      congrArg (fun p : Name × Name × Graph => p.2.2) (hpair 0 1 (by decide))
    have h12 : graph (seq 1) (seq 2) = v.2.2 :=
      congrArg (fun p : Name × Name × Graph => p.2.2) (hpair 1 2 (by decide))
    have h02 : graph (seq 0) (seq 2) = v.2.2 :=
      congrArg (fun p : Name × Name × Graph => p.2.2) (hpair 0 2 (by decide))
    calc
      comp (val v.2.2) (val v.2.2) = comp (val (graph (seq 1) (seq 2))) (val (graph (seq 0) (seq 1))) := by rw [h12, h01]
      _ = val (graph (seq 0) (seq 2)) := (hcomp _ _ _ (hmono (by decide)) (hmono (by decide))).symm
      _ = val v.2.2 := by rw [h02]

end NishtAbel2024V2.SCTPort
