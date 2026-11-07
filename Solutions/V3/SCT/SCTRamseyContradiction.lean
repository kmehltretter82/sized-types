import Solutions.V3.SCT.IdempotentRamsey
import Solutions.V3.SCT.SCTWellFounded

namespace NishtAbel2024V2.SCTPort

universe u

/-- Once finite interval colors have the concatenation, closure and conformance
properties, Ramsey's theorem rules out an infinite invocation chain. -/
theorem no_chain_from_interval_coloring {S : Type u} {Name Graph : Type}
    [Finite Name] [Finite Graph]
    (ltRel leRel : S → S → Prop) (wf : WellFounded ltRel)
    (family : InvGraphFamily) (valid : SCTValid family)
    (name : Nat → Name) (nameVal : Name → FunName)
    (graph : Nat → Nat → Graph) (graphVal : Graph → InvGraph)
    (sizes : Nat → List S)
    (hcomp : ∀ i j k, i < j → j < k →
      graphVal (graph i k) = (graphVal (graph j k)).comp (graphVal (graph i j)))
    (hclosed : ∀ i j, i < j →
      InvGraphClosure family (nameVal (name i)) (nameVal (name j)) (graphVal (graph i j)))
    (hconform : ∀ i j, i < j →
      ConformsU ltRel leRel (graphVal (graph i j)) (sizes j) (sizes i))
    (ramsey : ∀ (color : Finset Nat → Name × Name × Graph),
      ∃ (M : Set Nat) (b : Name × Name × Graph), M.Infinite ∧
        ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b) : False := by
  obtain ⟨seq, f, G, hmono, hname, hgraph, hidem⟩ :=
    homogeneous_idempotent_intervals name graph graphVal InvGraph.comp hcomp ramsey
  have hclose : InvGraphClosure family (nameVal f) (nameVal f) (graphVal G) := by
    have h := hclosed (seq 0) (seq 1) (hmono (by decide))
    rw [hname 0, hname 1, hgraph 0 1 (by decide)] at h
    exact h
  apply no_infinite_idempotent_chain ltRel leRel wf family valid (nameVal f) (graphVal G) hclose hidem (fun n => sizes (seq n))
  intro n
  have h := hconform (seq n) (seq (n + 1)) (hmono (Nat.lt_succ_self n))
  rw [hgraph n (n + 1) (Nat.lt_succ_self n)] at h
  exact h

end NishtAbel2024V2.SCTPort
