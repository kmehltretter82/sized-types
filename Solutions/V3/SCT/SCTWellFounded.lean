import Definitions.Def_NishtAbel2024V2_Syntax
import Solutions.V3.SCT.GraphCompat

namespace NishtAbel2024V2.SCTPort

universe u

/-- A homogeneous chain with a strict diagonal contradicts ordinal well-foundedness. -/
theorem no_infinite_strict_diagonal_chain {S : Type u} (ltRel leRel : S → S → Prop)
    (wf : WellFounded ltRel) (G : InvGraph) (s : Nat → List S) (k : Nat)
    (hk : k < G.leftArity) (hedge : G.edgeAt k k = some .lt)
    (hchain : ∀ n, ConformsU ltRel leRel G (s (n + 1)) (s n)) : False := by
  have hlen : ∀ n, k < (s (n + 1)).length := by
    intro n
    simpa only [(hchain n).1] using hk
  let chain : Nat → S := fun n => (s (n + 1)).get ⟨k, hlen n⟩
  have hdescending : ∀ n, ltRel (chain (n + 1)) (chain n) := by
    intro n
    exact ((hchain (n + 1)).2.2 k k (hlen (n + 1)) (hlen n)).1 hedge
  have impossible (x : S) (hacc : Acc ltRel x) : ∀ n, chain n = x → False := by
    induction hacc with
    | intro x _ ih =>
      intro n hn
      exact ih (chain (n + 1)) (hn ▸ hdescending n) (n + 1) rfl
  exact impossible (chain 0) (wf.apply (chain 0)) 0 rfl

/-- An idempotent graph in a valid closure cannot label an infinite conforming chain. -/
theorem no_infinite_idempotent_chain {S : Type u} (ltRel leRel : S → S → Prop)
    (wf : WellFounded ltRel) (family : InvGraphFamily) (valid : SCTValid family)
    (f : FunName) (G : InvGraph) (closed : InvGraphClosure family f f G)
    (idempotent : G.comp G = G) (s : Nat → List S)
    (hchain : ∀ n, ConformsU ltRel leRel G (s (n + 1)) (s n)) : False := by
  obtain ⟨k, hk, hedge⟩ := valid.2 f G closed idempotent
  exact no_infinite_strict_diagonal_chain ltRel leRel wf G s k hk hedge hchain

end NishtAbel2024V2.SCTPort
