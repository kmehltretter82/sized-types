import Solutions.V4.Main
import Solutions.V3.SCT.Ramsey

/-! # V4: the main theorems, with Ramsey's theorem discharged -/

namespace NishtAbel2024V4

theorem ramseyPairs : RamseyPairs := by
  intro C _ color
  obtain ⟨M, b, _, hInf, hcolor⟩ :=
    NishtAbel2024V3.RamseyPort.SeparableQuotient.InfiniteRamsey.homogeneous_subset_oai 2 color Set.univ
      Set.infinite_univ
  exact ⟨M, b, hInf, hcolor⟩

/-- Theorem 15, V4 (V3 plus type polymorphism and bounded size quantifiers inside types):
soundness of type-based termination checking. -/
theorem theorem_15 (W sig Ξ : List FunDecl)
    (hW : ∀ d ∈ sig ++ Ξ, d ∈ W)
    (hnames : (W.map FunDecl.name).Nodup)
    (hclosed : ∀ d ∈ W, (Tm.lam d.clauses).Closed)
    (htyped : BlockTy sig Ξ)
    (hsig : SemValid W sig) :
    SemValid W Ξ :=
  theorem_15_proof ramseyPairs W sig Ξ hW hnames hclosed htyped hsig

/-- Theorem 5, V4: typed programs are strongly normalizing. -/
theorem theorem_5 (blocks : List (List FunDecl)) (main : Tm) (A : Ty)
    (htyped : ProgramTy blocks main A) :
    SN blocks.flatten main :=
  theorem_5_proof ramseyPairs blocks main A htyped

end NishtAbel2024V4

#print axioms NishtAbel2024V4.theorem_15
#print axioms NishtAbel2024V4.theorem_5
