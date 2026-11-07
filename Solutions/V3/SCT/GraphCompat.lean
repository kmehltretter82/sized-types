import Definitions.Def_NishtAbel2024V2_Syntax

namespace NishtAbel2024V2.SCTPort

universe u

/-- Universe-polymorphic copy of `ConformsToGraph`. -/
def ConformsU {S : Type u} (ltRel leRel : S → S → Prop) (G : InvGraph) (s s' : List S) : Prop :=
  s.length = G.leftArity ∧
  s'.length = G.rightArity ∧
  ∀ (i j : Nat) (hi : i < s.length) (hj : j < s'.length),
    (G.edgeAt i j = some .lt → ltRel (s.get ⟨i, hi⟩) (s'.get ⟨j, hj⟩)) ∧
    (G.edgeAt i j = some .le → leRel (s.get ⟨i, hi⟩) (s'.get ⟨j, hj⟩))

private theorem fold_choose {α : Type} (f : α → EdgeRel) (xs : List α)
    (a : Option EdgeRel) (r : EdgeRel)
    (h : xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) a = some r) :
    a = some r ∨ ∃ x ∈ xs, f x = r := by
  induction xs generalizing a with
  | nil => simpa using h
  | cons x xs ih =>
    have h' := ih (EdgeRel.combine a (some (f x))) h
    cases a <;> cases r <;> cases hfx : f x <;> simp_all [EdgeRel.combine] <;> grind
    done

private theorem edgeAt_mem (G : InvGraph) (i j : Nat) (r : EdgeRel)
    (h : G.edgeAt i j = some r) : (i, j, r) ∈ G.edges := by
  have h' := fold_choose (fun (e : Nat × Nat × EdgeRel) => e.2.2)
    (G.edges.filter (fun e => e.1 == i && e.2.1 == j)) none r h
  simp only [reduceCtorEq, false_or, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h'
  rcases h' with ⟨⟨x, y, z⟩, ⟨hx, rfl, rfl⟩, rfl⟩
  exact hx
  done

private theorem fold_choose_optional {α : Type} (f : α → Option EdgeRel) (xs : List α)
    (a : Option EdgeRel) (r : EdgeRel)
    (h : xs.foldl (fun acc x => EdgeRel.combine acc (f x)) a = some r) :
    a = some r ∨ ∃ x ∈ xs, f x = some r := by
  induction xs generalizing a with
  | nil => simpa using h
  | cons x xs ih =>
    have h' := ih (EdgeRel.combine a (f x)) h
    cases a <;> cases hfx : f x <;> cases r <;> simp_all [EdgeRel.combine] <;> grind
    done

private theorem comp_edge_witness (G₁ G₂ : InvGraph) (i j : Nat)
    (hi : i < G₁.leftArity) (hj : j < G₂.rightArity) (r : EdgeRel)
    (h : (G₁.comp G₂).edgeAt i j = some r) :
    ∃ k < G₁.rightArity, ∃ r₁ r₂,
      G₁.edgeAt i k = some r₁ ∧ G₂.edgeAt k j = some r₂ ∧
      EdgeRel.seq r₁ r₂ = r := by
  have he := edgeAt_mem (G₁.comp G₂) i j r h
  simp only [InvGraph.comp, InvGraph.canonicalEdges, List.mem_flatMap, List.mem_filterMap, List.mem_range] at he
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at he
  rcases he with ⟨i', _, j', _, r', hf, rfl, rfl, rfl⟩
  have step (acc : Option EdgeRel) (k : Nat) :
      (match G₁.edgeAt i' k, G₂.edgeAt k j' with
       | some a, some b => EdgeRel.combine acc (some (a.seq b))
       | _, _ => acc) =
      EdgeRel.combine acc (do let a ← G₁.edgeAt i' k; let b ← G₂.edgeAt k j'; some (a.seq b)) := by
    cases acc with
    | none => cases G₁.edgeAt i' k <;> cases G₂.edgeAt k j' <;> rfl
    | some a => cases a <;> cases G₁.edgeAt i' k <;> cases G₂.edgeAt k j' <;> rfl
  have heq : (fun acc k => match G₁.edgeAt i' k, G₂.edgeAt k j' with
      | some a, some b => EdgeRel.combine acc (some (a.seq b))
      | _, _ => acc) =
      (fun acc k => EdgeRel.combine acc (do let a ← G₁.edgeAt i' k; let b ← G₂.edgeAt k j'; some (a.seq b))) := by
    funext acc k
    exact step acc k
  have samefold := congrArg (fun f => List.foldl f none (List.range G₁.rightArity)) heq
  have hf' := samefold.symm.trans hf
  have hw := fold_choose_optional (fun k => do let a ← G₁.edgeAt i' k; let b ← G₂.edgeAt k j'; some (a.seq b)) (List.range G₁.rightArity) none r' hf'
  simp only [reduceCtorEq, false_or, List.mem_range] at hw
  rcases hw with ⟨k, hk, hk'⟩
  cases e₁ : G₁.edgeAt i' k <;> cases e₂ : G₂.edgeAt k j' <;> simp_all <;> grind
  done

theorem graph_compat {S : Type u} (ltRel leRel : S → S → Prop)
    (hle : ∀ x y, ltRel x y → leRel x y)
    (htt : ∀ x y z, leRel x y → leRel y z → leRel x z)
    (htl : ∀ x y z, ltRel x y → leRel y z → ltRel x z)
    (hlt : ∀ x y z, leRel x y → ltRel y z → ltRel x z)
    (G₁ G₂ : InvGraph) (a b c : List S)
    (h₁ : ConformsU ltRel leRel G₁ a b)
    (h₂ : ConformsU ltRel leRel G₂ b c) :
    ConformsU ltRel leRel (G₁.comp G₂) a c := by
  rcases h₁ with ⟨ha, hb₁, h₁⟩
  rcases h₂ with ⟨hb₂, hc, h₂⟩
  refine ⟨ha, hc, ?_⟩
  intro i j hi hj
  constructor
  · intro h
    obtain ⟨k, hk, r₁, r₂, e₁, e₂, es⟩ := comp_edge_witness G₁ G₂ i j (ha ▸ hi) (hc ▸ hj) .lt h
    have hk' : k < b.length := by omega
    have ha' := h₁ i k hi hk'
    have hc' := h₂ k j hk' hj
    cases r₁ <;> cases r₂ <;> simp_all [EdgeRel.seq] <;> grind
    done
  · intro h
    obtain ⟨k, hk, r₁, r₂, e₁, e₂, es⟩ := comp_edge_witness G₁ G₂ i j (ha ▸ hi) (hc ▸ hj) .le h
    have hk' : k < b.length := by omega
    have ha' := h₁ i k hi hk'
    have hc' := h₂ k j hk' hj
    cases r₁ <;> cases r₂ <;> simp_all [EdgeRel.seq] <;> grind

end NishtAbel2024V2.SCTPort
