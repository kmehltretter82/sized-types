import Definitions.Def_NishtAbel2024V2_Syntax
import Solutions.V3.SCT.GraphCompat

namespace NishtAbel2024V2.SCTPort

universe u

theorem canonical_mem (n m i j : Nat) (f : Nat → Nat → Option EdgeRel) (r : EdgeRel) :
    (i, j, r) ∈ InvGraph.canonicalEdges n m f ↔ i < n ∧ j < m ∧ f i j = some r := by
  simp [InvGraph.canonicalEdges, List.mem_flatMap, List.mem_filterMap, List.mem_range,
    Option.map_eq_some_iff, Prod.mk.injEq]
  grind

private theorem fold_ne_none {α : Type} (f : α → EdgeRel) (xs : List α) (r : EdgeRel) :
    xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) (some r) ≠ none := by
  induction xs generalizing r with
  | nil => simp
  | cons x xs ih =>
    cases r <;> cases h : f x <;> simp_all [EdgeRel.combine]

private theorem fold_eq_none_iff {α : Type} (f : α → EdgeRel) (xs : List α) :
    xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) none = none ↔ xs = [] := by
  cases xs with
  | nil => simp
  | cons x xs =>
    simp only [List.foldl_cons, List.cons_ne_nil, iff_false]
    have hn := fold_ne_none f xs (f x)
    cases h : f x <;> simpa [EdgeRel.combine, h] using hn

private theorem fold_choose {α : Type} (f : α → EdgeRel) (xs : List α)
    (a : Option EdgeRel) (r : EdgeRel)
    (h : xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) a = some r) :
    a = some r ∨ ∃ x ∈ xs, f x = r := by
  induction xs generalizing a with
  | nil => simpa using h
  | cons x xs ih =>
    have h' := ih (EdgeRel.combine a (some (f x))) h
    cases a <;> cases r <;> cases hfx : f x <;> simp_all [EdgeRel.combine] <;> grind

private theorem edgeAt_mem (G : InvGraph) (i j : Nat) (r : EdgeRel)
    (h : G.edgeAt i j = some r) : (i, j, r) ∈ G.edges := by
  have h' := fold_choose (fun (e : Nat × Nat × EdgeRel) => e.2.2)
    (G.edges.filter (fun e => e.1 == i && e.2.1 == j)) none r h
  simp only [reduceCtorEq, false_or, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h'
  rcases h' with ⟨⟨x, y, z⟩, ⟨hx, rfl, rfl⟩, rfl⟩
  exact hx

private theorem edgeAt_ne_none_of_mem (G : InvGraph) (i j : Nat) (r : EdgeRel)
    (hm : (i, j, r) ∈ G.edges) : G.edgeAt i j ≠ none := by
  intro h
  have hf := (fold_eq_none_iff (fun (e : Nat × Nat × EdgeRel) => e.2.2)
    (G.edges.filter (fun e => e.1 == i && e.2.1 == j))).mp h
  have hm' : (i, j, r) ∈ G.edges.filter (fun e => e.1 == i && e.2.1 == j) := by
    simp [hm]
  rw [hf] at hm'
  exact List.not_mem_nil hm'

theorem canonical_lookup (n m : Nat) (f : Nat → Nat → Option EdgeRel) (i j : Nat)
    (hi : i < n) (hj : j < m) :
    (InvGraph.mk n m (InvGraph.canonicalEdges n m f)).edgeAt i j = f i j := by
  let G : InvGraph := ⟨n, m, InvGraph.canonicalEdges n m f⟩
  change G.edgeAt i j = f i j
  cases he : G.edgeAt i j with
  | none =>
    cases hf : f i j with
    | none => rfl
    | some r =>
      have hm : (i, j, r) ∈ G.edges := (canonical_mem n m i j f r).2 ⟨hi, hj, hf⟩
      exact False.elim (edgeAt_ne_none_of_mem G i j r hm he)
  | some r =>
    have hm : (i, j, r) ∈ G.edges := edgeAt_mem G i j r he
    exact ((canonical_mem n m i j f r).1 hm).2.2.symm

end NishtAbel2024V2.SCTPort
