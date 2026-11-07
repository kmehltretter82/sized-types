import Definitions.Def_NishtAbel2024V2_Syntax
import Mathlib.Data.List.Basic
import Solutions.V3.SCT.CanonicalLookup

namespace NishtAbel2024V2.SCTPort

universe u

/-- Composition of optional edge labels; absence absorbs composition. -/
def edgeMul : Option EdgeRel → Option EdgeRel → Option EdgeRel
  | some a, some b => some (a.seq b)
  | _, _ => none

theorem edgeMul_assoc (a b c : Option EdgeRel) :
    edgeMul (edgeMul a b) c = edgeMul a (edgeMul b c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

theorem combine_assoc (a b c : Option EdgeRel) :
    EdgeRel.combine (EdgeRel.combine a b) c = EdgeRel.combine a (EdgeRel.combine b c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

theorem combine_comm (a b : Option EdgeRel) :
    EdgeRel.combine a b = EdgeRel.combine b a := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rfl

theorem edgeMul_left_distrib (a b c : Option EdgeRel) :
    edgeMul a (EdgeRel.combine b c) = EdgeRel.combine (edgeMul a b) (edgeMul a c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

theorem edgeMul_right_distrib (a b c : Option EdgeRel) :
    edgeMul (EdgeRel.combine a b) c = EdgeRel.combine (edgeMul a c) (edgeMul b c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

theorem edgeMul_sum_right (a : Option EdgeRel) (xs : List (Option EdgeRel)) :
    edgeMul a (xs.foldr EdgeRel.combine none) =
      (xs.map (edgeMul a)).foldr EdgeRel.combine none := by
  induction xs with
  | nil => rcases a with _ | (_ | _) <;> rfl
  | cons x xs ih =>
    simp only [List.foldr_cons, List.map_cons, edgeMul_left_distrib, ih]

theorem edgeMul_sum_left (xs : List (Option EdgeRel)) (a : Option EdgeRel) :
    edgeMul (xs.foldr EdgeRel.combine none) a =
      (xs.map (fun x => edgeMul x a)).foldr EdgeRel.combine none := by
  induction xs with
  | nil => rcases a with _ | (_ | _) <;> rfl
  | cons x xs ih =>
    simp only [List.foldr_cons, List.map_cons, edgeMul_right_distrib, ih]

theorem combine_interchange (a b c d : Option EdgeRel) :
    EdgeRel.combine (EdgeRel.combine a b) (EdgeRel.combine c d) =
    EdgeRel.combine (EdgeRel.combine a c) (EdgeRel.combine b d) := by
  rw [combine_assoc, ← combine_assoc b c d, combine_comm b c, combine_assoc, ← combine_assoc]

theorem sum_map_combine {α : Type} (xs : List α) (f g : α → Option EdgeRel) :
    (xs.map (fun x => EdgeRel.combine (f x) (g x))).foldr EdgeRel.combine none =
    EdgeRel.combine ((xs.map f).foldr EdgeRel.combine none) ((xs.map g).foldr EdgeRel.combine none) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons, ih]
    exact combine_interchange _ _ _ _

theorem finite_sum_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Option EdgeRel) :
    (xs.map (fun x => (ys.map (f x)).foldr EdgeRel.combine none)).foldr EdgeRel.combine none =
    (ys.map (fun y => (xs.map (fun x => f x y)).foldr EdgeRel.combine none)).foldr EdgeRel.combine none := by
  induction xs with
  | nil =>
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_nil, List.foldr_nil] at ih
      simp only [List.map_nil, List.foldr_nil, List.map_cons, List.foldr_cons]
      rw [← ih]
      rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih, ← sum_map_combine]

theorem combine_none_right (a : Option EdgeRel) : EdgeRel.combine a none = a := by
  rcases a with _ | (_ | _) <;> rfl

theorem combine_foldl_eq_foldr (xs : List (Option EdgeRel)) :
    xs.foldl EdgeRel.combine none = xs.foldr EdgeRel.combine none := by
  have h : ∀ acc, xs.foldl EdgeRel.combine acc = EdgeRel.combine acc (xs.foldr EdgeRel.combine none) := by
    induction xs with
    | nil => intro acc; simp only [List.foldl_nil, List.foldr_nil, combine_none_right]
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, List.foldr_cons, ih, combine_assoc]
  rw [h none]
  rcases xs.foldr EdgeRel.combine none with _ | (_ | _) <;> rfl

/-- Without compatible middle arities, associativity can fail, even for finite graphs. -/
theorem comp_not_assoc_without_arity :
    ∃ G₁ G₂ G₃ : InvGraph, (G₁.comp G₂).comp G₃ ≠ G₁.comp (G₂.comp G₃) := by
  refine ⟨⟨1, 1, [(0, 0, .le)]⟩, ⟨0, 1, [(0, 0, .le)]⟩, ⟨1, 1, [(0, 0, .le)]⟩, ?_⟩
  decide

def edgeSum (n : Nat) (f : Nat → Option EdgeRel) : Option EdgeRel :=
  ((List.range n).map f).foldr EdgeRel.combine none

theorem edgeSum_congr {n : Nat} {f g : Nat → Option EdgeRel}
    (h : ∀ i < n, f i = g i) : edgeSum n f = edgeSum n g := by
  unfold edgeSum
  congr 1
  apply List.map_congr_left
  intro x hx
  exact h x (List.mem_range.mp hx)

theorem matrix_assoc (A B C : InvGraph)
    (hab : A.rightArity = B.leftArity) (_hbc : B.rightArity = C.leftArity)
    (compLookup : ∀ (X Y : InvGraph) (i j : Nat),
      i < X.leftArity → j < Y.rightArity →
      (X.comp Y).edgeAt i j = edgeSum X.rightArity (fun k => edgeMul (X.edgeAt i k) (Y.edgeAt k j)))
    (i j : Nat) (hi : i < A.leftArity) (hj : j < C.rightArity) :
    edgeSum A.rightArity (fun k => edgeMul (A.edgeAt i k) ((B.comp C).edgeAt k j)) =
    edgeSum B.rightArity (fun k => edgeMul ((A.comp B).edgeAt i k) (C.edgeAt k j)) := by
  calc
    _ = edgeSum A.rightArity (fun k => edgeSum B.rightArity (fun l => edgeMul (A.edgeAt i k) (edgeMul (B.edgeAt k l) (C.edgeAt l j)))) := by
      apply edgeSum_congr
      intro k hk
      rw [compLookup B C k j (hab ▸ hk) hj]
      unfold edgeSum
      simpa only [List.map_map, Function.comp_def] using edgeMul_sum_right (A.edgeAt i k) ((List.range B.rightArity).map (fun l => edgeMul (B.edgeAt k l) (C.edgeAt l j)))
    _ = edgeSum B.rightArity (fun l => edgeSum A.rightArity (fun k => edgeMul (edgeMul (A.edgeAt i k) (B.edgeAt k l)) (C.edgeAt l j))) := by
      unfold edgeSum
      simp only [edgeMul_assoc]
      exact finite_sum_swap _ _ _
    _ = _ := by
      apply edgeSum_congr
      intro l hl
      rw [compLookup A B i l hi hl]
      unfold edgeSum
      simpa only [List.map_map, Function.comp_def] using (edgeMul_sum_left ((List.range A.rightArity).map (fun k => edgeMul (A.edgeAt i k) (B.edgeAt k l))) (C.edgeAt l j)).symm

def compEdges (A B : InvGraph) (i j : Nat) : Option EdgeRel :=
  (List.range A.rightArity).foldl
    (fun acc k => match A.edgeAt i k, B.edgeAt k j with
      | some r₁, some r₂ => EdgeRel.combine acc (some (EdgeRel.seq r₁ r₂))
      | _, _ => acc) none

theorem compEdges_eq (A B : InvGraph) (i j : Nat) :
    compEdges A B i j = edgeSum A.rightArity (fun k => edgeMul (A.edgeAt i k) (B.edgeAt k j)) := by
  unfold compEdges edgeSum
  have hstep : ∀ acc k, (match A.edgeAt i k, B.edgeAt k j with
      | some r₁, some r₂ => EdgeRel.combine acc (some (EdgeRel.seq r₁ r₂))
      | _, _ => acc) = EdgeRel.combine acc (edgeMul (A.edgeAt i k) (B.edgeAt k j)) := by
    intro acc k
    rcases acc with _ | (_ | _) <;> rcases A.edgeAt i k with _ | (_ | _) <;> rcases B.edgeAt k j with _ | (_ | _) <;> rfl
  simp only [hstep, ← List.foldl_map, combine_foldl_eq_foldr]

theorem comp_def (A B : InvGraph) :
    A.comp B = ⟨A.leftArity, B.rightArity, InvGraph.canonicalEdges A.leftArity B.rightArity (compEdges A B)⟩ := rfl

theorem comp_assoc_of_lookup (A B C : InvGraph)
    (hab : A.rightArity = B.leftArity) (hbc : B.rightArity = C.leftArity)
    (compLookup : ∀ (X Y : InvGraph) (i j : Nat),
      i < X.leftArity → j < Y.rightArity →
      (X.comp Y).edgeAt i j = edgeSum X.rightArity (fun k => edgeMul (X.edgeAt i k) (Y.edgeAt k j))) :
    (A.comp B).comp C = A.comp (B.comp C) := by
  rw [comp_def (A.comp B) C, comp_def A (B.comp C)]
  simp only [InvGraph.comp, InvGraph.mk.injEq, true_and]
  change InvGraph.canonicalEdges A.leftArity C.rightArity (compEdges (A.comp B) C) =
    InvGraph.canonicalEdges A.leftArity C.rightArity (compEdges A (B.comp C))
  unfold InvGraph.canonicalEdges
  apply List.flatMap_congr
  intro i hi
  apply List.filterMap_congr
  intro j hj
  have hi' : i < A.leftArity := List.mem_range.mp hi
  have hj' : j < C.rightArity := List.mem_range.mp hj
  have h := (matrix_assoc A B C hab hbc compLookup i j hi' hj').symm
  rw [compEdges_eq, compEdges_eq]
  change Option.map _ (edgeSum B.rightArity _) = Option.map _ (edgeSum A.rightArity _)
  rw [h]

theorem comp_assoc_of_canonical_lookup (A B C : InvGraph)
    (hab : A.rightArity = B.leftArity) (hbc : B.rightArity = C.leftArity)
    (lookup : ∀ (l r : Nat) (f : Nat → Nat → Option EdgeRel) (i j : Nat),
      i < l → j < r → (InvGraph.mk l r (InvGraph.canonicalEdges l r f)).edgeAt i j = f i j) :
    (A.comp B).comp C = A.comp (B.comp C) := by
  apply comp_assoc_of_lookup A B C hab hbc
  intro X Y i j hi hj
  rw [comp_def, lookup X.leftArity Y.rightArity (compEdges X Y) i j hi hj, compEdges_eq]

theorem comp_assoc_compatible (A B C : InvGraph)
    (hab : A.rightArity = B.leftArity) (hbc : B.rightArity = C.leftArity) :
    (A.comp B).comp C = A.comp (B.comp C) := by
  exact comp_assoc_of_canonical_lookup A B C hab hbc canonical_lookup

end NishtAbel2024V2.SCTPort
