import Solutions.V3.SCT.SCTRamseyContradiction
import Solutions.V3.SCT.ClosureFinite
import Mathlib.Data.Finite.Prod

namespace NishtAbel2024V2.SCTPort

universe u

/-- Instantiate the finite-color contradiction with actual invocation graphs. -/
theorem no_chain_from_finite_intervals {S : Type u} (ltRel leRel : S → S → Prop)
    (wf : WellFounded ltRel) (family : InvGraphFamily) (valid : SCTValid family)
    (dom : List FunName) (name : Nat → FunName) (hdom : ∀ n, name n ∈ dom)
    (interval : Nat → Nat → InvGraph) (sizes : Nat → List S)
    (hcomp : ∀ i j k, i < j → j < k →
      interval i k = (interval j k).comp (interval i j))
    (hclosed : ∀ i j, i < j → InvGraphClosure family (name i) (name j) (interval i j))
    (hconform : ∀ i j, i < j →
      ConformsU ltRel leRel (interval i j) (sizes j) (sizes i))
    (ramsey : ∀ {C : Type} [Finite C] (color : Finset Nat → C),
      ∃ (M : Set Nat) (b : C), M.Infinite ∧
        ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b) : False := by
  classical
  let names : Set FunName := {f | f ∈ dom}
  let : Finite names := dom.finite_toSet.to_subtype
  let graphs : Set InvGraph := {G | ∃ f g, InvGraphClosure family f g G}
  let : Finite graphs := (finite_closure_graphs family valid.1).to_subtype
  let coloredName (n : Nat) : names := ⟨name n, hdom n⟩
  let coloredGraph (i j : Nat) : graphs :=
    if h : i < j then ⟨interval i j, ⟨name i, name j, hclosed i j h⟩⟩
    else ⟨interval 0 1, ⟨name 0, name 1, hclosed 0 1 (by decide)⟩⟩
  apply no_chain_from_interval_coloring ltRel leRel wf family valid coloredName Subtype.val coloredGraph Subtype.val sizes
  · intro i j k hij hjk
    simpa [coloredGraph, hij, hjk, lt_trans hij hjk] using hcomp i j k hij hjk
  · intro i j hij
    simpa [coloredName, coloredGraph, hij] using hclosed i j hij
  · intro i j hij
    simpa [coloredGraph, hij] using hconform i j hij
  · exact ramsey

end NishtAbel2024V2.SCTPort
