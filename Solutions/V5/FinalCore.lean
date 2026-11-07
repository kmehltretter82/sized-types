import Solutions.V5.Main
import Solutions.V3.SCT.Ramsey

/-! # V5: the semantic core with Ramsey's theorem discharged -/

namespace NishtAbel2024V5

theorem ramseyPairs : RamseyPairs := by
  intro C _ color
  obtain ⟨M, b, _, hInf, hcolor⟩ :=
    NishtAbel2024V3.RamseyPort.SeparableQuotient.InfiniteRamsey.homogeneous_subset_oai 2 color
      Set.univ Set.infinite_univ
  exact ⟨M, b, hInf, hcolor⟩

theorem theorem_4_core (W sig Ξ : List FunDecl) (hW : ∀ d ∈ sig ++ Ξ, d ∈ W)
    (hnames : (W.map FunDecl.name).Nodup) (hclosed : ∀ d ∈ W, (Tm.lam d.clauses).Closed)
    (htyped : BlockTy sig Ξ) (hsig : SemValid W sig) : SemValid W Ξ :=
  theorem_4_proof ramseyPairs W sig Ξ hW hnames hclosed htyped hsig

theorem theorem_5_core (blocks : List (List FunDecl)) (main : Tm) (A : Ty)
    (htyped : ProgramTy blocks main A) : SN blocks.flatten main :=
  theorem_5_proof ramseyPairs blocks main A htyped

end NishtAbel2024V5

#print axioms NishtAbel2024V5.theorem_4_core
#print axioms NishtAbel2024V5.theorem_5_core
#print axioms NishtAbel2024V5.sizeLt_sound2
#print axioms NishtAbel2024V5.fundamental
