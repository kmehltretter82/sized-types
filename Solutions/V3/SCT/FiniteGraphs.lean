import Definitions.Def_NishtAbel2024V2_Syntax
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

namespace NishtAbel2024V2.SCTPort

universe u

instance : Finite EdgeRel := Finite.of_injective (fun e : EdgeRel => match e with | .lt => false | .le => true) (by intro a b h; cases a <;> cases b <;> simp_all)

def graphFromCode (N : Nat) (a b : Fin (N+1)) (m : Fin N → Fin N → Option EdgeRel) : InvGraph :=
  ⟨a.val, b.val, InvGraph.canonicalEdges a.val b.val fun i j =>
    if hi : i < N then if hj : j < N then m ⟨i, hi⟩ ⟨j, hj⟩ else none else none⟩

theorem finite_normalized_graphs (N : Nat) :
    {G : InvGraph | G.leftArity ≤ N ∧ G.rightArity ≤ N ∧ G = G.normalize}.Finite := by
  classical
  let _ : Fintype EdgeRel := Fintype.ofFinite EdgeRel
  let codes := Set.range (fun c : Fin (N+1) × Fin (N+1) × (Fin N → Fin N → Option EdgeRel) => graphFromCode N c.1 c.2.1 c.2.2)
  have hfin : codes.Finite := by
    simpa only [Set.image_univ] using Set.Finite.image _ (Set.finite_univ (α := Fin (N+1) × Fin (N+1) × (Fin N → Fin N → Option EdgeRel)))
  apply hfin.subset
  intro G hG
  rcases hG with ⟨hleft, hright, hnorm⟩
  refine ⟨(⟨G.leftArity, by omega⟩, ⟨G.rightArity, by omega⟩, fun i j => G.edgeAt i.val j.val), ?_⟩
  dsimp [graphFromCode]
  calc
    _ = G.normalize := by
      simp only [InvGraph.normalize, InvGraph.mk.injEq, true_and]
      unfold InvGraph.canonicalEdges
      apply List.flatMap_congr
      intro i hi
      apply List.filterMap_congr
      intro j hj
      have hiN : i < N := by simp only [List.mem_range] at hi; omega
      have hjN : j < N := by simp only [List.mem_range] at hj; omega
      simp [hiN, hjN]
    _ = G := hnorm.symm

end NishtAbel2024V2.SCTPort
