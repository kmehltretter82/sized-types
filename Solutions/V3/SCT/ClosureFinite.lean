import Solutions.V3.SCT.FiniteGraphs

namespace NishtAbel2024V2.SCTPort

universe u

def CanonicalGraph (G : InvGraph) : Prop :=
  ∃ lookup, G.edges = InvGraph.canonicalEdges G.leftArity G.rightArity lookup

theorem closure_invariants (𝒢 : InvGraphFamily) (hwf : 𝒢.ArityWf)
    {f g : FunName} {G : InvGraph} (h : InvGraphClosure 𝒢 f g G) :
    G.leftArity = 𝒢.arity g ∧ G.rightArity = 𝒢.arity f ∧ CanonicalGraph G := by
  induction h with
  | @base f g G hmem =>
    have hg := hwf.2 f g G hmem
    refine ⟨?_, ?_, ?_⟩
    · simpa [InvGraph.normalize] using hg.1
    · simpa [InvGraph.normalize] using hg.2.1
    · exact ⟨G.edgeAt, rfl⟩
  | @comp f h g G₁ G₂ h₁ h₂ ih₁ ih₂ =>
    exact ⟨ih₁.1, ih₂.2.1, ⟨_, rfl⟩⟩

theorem finite_canonical_graphs (N : Nat) :
    {G : InvGraph | G.leftArity ≤ N ∧ G.rightArity ≤ N ∧ CanonicalGraph G}.Finite := by
  classical
  let _ : Fintype EdgeRel := Fintype.ofFinite EdgeRel
  let codes := Set.range (fun c : Fin (N+1) × Fin (N+1) × (Fin N → Fin N → Option EdgeRel) => graphFromCode N c.1 c.2.1 c.2.2)
  have hfin : codes.Finite := by
    simpa only [Set.image_univ] using Set.Finite.image _ (Set.finite_univ (α := Fin (N+1) × Fin (N+1) × (Fin N → Fin N → Option EdgeRel)))
  apply hfin.subset
  intro G hG
  rcases hG with ⟨hleft, hright, lookup, hlookup⟩
  refine ⟨(⟨G.leftArity, by omega⟩, ⟨G.rightArity, by omega⟩, fun i j => lookup i.val j.val), ?_⟩
  dsimp [graphFromCode]
  cases G with
  | mk left right edges =>
    simp only [InvGraph.mk.injEq, true_and] at *
    rw [hlookup]
    unfold InvGraph.canonicalEdges
    apply List.flatMap_congr
    intro i hi
    apply List.filterMap_congr
    intro j hj
    have hiN : i < N := by simp only [List.mem_range] at hi; omega
    have hjN : j < N := by simp only [List.mem_range] at hj; omega
    simp [hiN, hjN]

theorem closure_support (𝒢 : InvGraphFamily) (dom : List FunName)
    (hsupp : ∀ f g, 𝒢.graphs f g ≠ [] → f ∈ dom ∧ g ∈ dom)
    {f g : FunName} {G : InvGraph} (h : InvGraphClosure 𝒢 f g G) :
    f ∈ dom ∧ g ∈ dom := by
  induction h with
  | base hmem => exact hsupp _ _ (List.ne_nil_of_mem hmem)
  | comp _ _ ih₁ ih₂ => exact ⟨ih₂.1, ih₁.2⟩

private theorem arity_bounded (arity : FunName → Nat) (dom : List FunName) (f : FunName)
    (hf : f ∈ dom) : arity f ≤ (dom.map arity).foldr max 0 := by
  induction dom with
  | nil => simp at hf
  | cons a dom ih =>
    simp only [List.mem_cons] at hf
    simp only [List.map_cons, List.foldr_cons]
    rcases hf with rfl | hf
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hf) (Nat.le_max_right _ _)

theorem finite_closure_graphs (𝒢 : InvGraphFamily) (hwf : 𝒢.ArityWf) :
    {G : InvGraph | ∃ f g, InvGraphClosure 𝒢 f g G}.Finite := by
  obtain ⟨dom, hsupp⟩ := hwf.1
  let N := (dom.map 𝒢.arity).foldr max 0
  apply (finite_canonical_graphs N).subset
  intro G hG
  obtain ⟨f, g, hg⟩ := hG
  obtain ⟨hgf, hgg⟩ := closure_support 𝒢 dom hsupp hg
  obtain ⟨hl, hr, hc⟩ := closure_invariants 𝒢 hwf hg
  exact ⟨hl ▸ arity_bounded 𝒢.arity dom g hgg,
         hr ▸ arity_bounded 𝒢.arity dom f hgf, hc⟩

end NishtAbel2024V2.SCTPort
