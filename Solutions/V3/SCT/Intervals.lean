import Definitions.Def_NishtAbel2024V2_Syntax
import Solutions.V3.SCT.GraphCompat
import Solutions.V3.SCT.GraphAssoc

namespace NishtAbel2024V2.SCTPort

universe u

/-- `segment g i n` composes the `n + 1` consecutive graphs starting at `i`.
The later graph is on the left because it compares callee sizes to caller sizes. -/
def segment (g : Nat → InvGraph) (i : Nat) : Nat → InvGraph
  | 0 => g i
  | n + 1 => (g (i + n + 1)).comp (segment g i n)

def interval (g : Nat → InvGraph) (i j : Nat) : InvGraph :=
  segment g i (j - i - 1)

theorem segment_closed (family : InvGraphFamily) (name : Nat → FunName)
    (g : Nat → InvGraph)
    (hbase : ∀ i, InvGraphClosure family (name i) (name (i + 1)) (g i))
    (i n : Nat) :
    InvGraphClosure family (name i) (name (i + n + 1)) (segment g i n) := by
  induction n with
  | zero => simpa [segment] using hbase i
  | succ n ih =>
    simpa [segment, Nat.add_assoc] using InvGraphClosure.comp (hbase (i + n + 1)) ih

theorem interval_closed (family : InvGraphFamily) (name : Nat → FunName)
    (g : Nat → InvGraph)
    (hbase : ∀ i, InvGraphClosure family (name i) (name (i + 1)) (g i))
    (i j : Nat) (hij : i < j) :
    InvGraphClosure family (name i) (name j) (interval g i j) := by
  have h := segment_closed family name g hbase i (j - i - 1)
  have hid : i + (j - i - 1) + 1 = j := by omega
  simpa [interval, hid] using h

theorem segment_conforms {S : Type u} (ltRel leRel : S → S → Prop)
    (hle : ∀ x y, ltRel x y → leRel x y)
    (htt : ∀ x y z, leRel x y → leRel y z → leRel x z)
    (htl : ∀ x y z, ltRel x y → leRel y z → ltRel x z)
    (hlt : ∀ x y z, leRel x y → ltRel y z → ltRel x z)
    (g : Nat → InvGraph) (sizes : Nat → List S)
    (hbase : ∀ i, ConformsU ltRel leRel (g i) (sizes (i + 1)) (sizes i))
    (i n : Nat) :
    ConformsU ltRel leRel (segment g i n) (sizes (i + n + 1)) (sizes i) := by
  induction n with
  | zero => simpa [segment] using hbase i
  | succ n ih =>
    simpa [segment, Nat.add_assoc] using
      graph_compat ltRel leRel hle htt htl hlt (g (i + n + 1)) (segment g i n)
        (sizes (i + n + 1 + 1)) (sizes (i + n + 1)) (sizes i) (hbase (i + n + 1)) ih

theorem interval_conforms {S : Type u} (ltRel leRel : S → S → Prop)
    (hle : ∀ x y, ltRel x y → leRel x y)
    (htt : ∀ x y z, leRel x y → leRel y z → leRel x z)
    (htl : ∀ x y z, ltRel x y → leRel y z → ltRel x z)
    (hlt : ∀ x y z, leRel x y → ltRel y z → ltRel x z)
    (g : Nat → InvGraph) (sizes : Nat → List S)
    (hbase : ∀ i, ConformsU ltRel leRel (g i) (sizes (i + 1)) (sizes i))
    (i j : Nat) (hij : i < j) :
    ConformsU ltRel leRel (interval g i j) (sizes j) (sizes i) := by
  have h := segment_conforms ltRel leRel hle htt htl hlt g sizes hbase i (j - i - 1)
  have hid : i + (j - i - 1) + 1 = j := by omega
  simpa [interval, hid] using h

theorem segment_arities (g : Nat → InvGraph) (arity : Nat → Nat)
    (hbase : ∀ i, (g i).leftArity = arity (i + 1) ∧ (g i).rightArity = arity i)
    (i n : Nat) :
    (segment g i n).leftArity = arity (i + n + 1) ∧
    (segment g i n).rightArity = arity i := by
  induction n with
  | zero => simpa [segment] using hbase i
  | succ n ih =>
    simpa [segment, InvGraph.comp, Nat.add_assoc] using ⟨(hbase (i + n + 1)).1, ih.2⟩

theorem segment_concat (g : Nat → InvGraph) (arity : Nat → Nat)
    (hbase : ∀ i, (g i).leftArity = arity (i + 1) ∧ (g i).rightArity = arity i)
    (assoc : ∀ A B C : InvGraph, A.rightArity = B.leftArity → B.rightArity = C.leftArity →
      (A.comp B).comp C = A.comp (B.comp C))
    (i n m : Nat) :
    segment g i (n + m + 1) = (segment g (i + n + 1) m).comp (segment g i n) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (g (i + (n + m + 1) + 1)).comp (segment g i (n + m + 1)) =
      ((g ((i + n + 1) + m + 1)).comp (segment g (i + n + 1) m)).comp (segment g i n)
    rw [ih]
    have idx : i + (n + m + 1) + 1 = i + n + 1 + m + 1 := by omega
    rw [idx]
    apply Eq.symm
    apply assoc
    · exact (hbase _).2.trans (segment_arities g arity hbase (i + n + 1) m).1.symm
    · exact (segment_arities g arity hbase (i + n + 1) m).2.trans
        (segment_arities g arity hbase i n).1.symm

theorem interval_concat (g : Nat → InvGraph) (arity : Nat → Nat)
    (hbase : ∀ i, (g i).leftArity = arity (i + 1) ∧ (g i).rightArity = arity i)
    (assoc : ∀ A B C : InvGraph, A.rightArity = B.leftArity → B.rightArity = C.leftArity →
      (A.comp B).comp C = A.comp (B.comp C))
    (i j k : Nat) (hij : i < j) (hjk : j < k) :
    interval g i k = (interval g j k).comp (interval g i j) := by
  have h := segment_concat g arity hbase assoc i (j - i - 1) (k - j - 1)
  have hstart : i + (j - i - 1) + 1 = j := by omega
  have hlen : (j - i - 1) + (k - j - 1) + 1 = k - i - 1 := by omega
  simpa [interval, hstart, hlen] using h

theorem interval_concat_of_conforms {S : Type u} (ltRel leRel : S → S → Prop)
    (g : Nat → InvGraph) (sizes : Nat → List S)
    (hbase : ∀ i, ConformsU ltRel leRel (g i) (sizes (i + 1)) (sizes i))
    (i j k : Nat) (hij : i < j) (hjk : j < k) :
    interval g i k = (interval g j k).comp (interval g i j) := by
  have harity : ∀ i, (g i).leftArity = (sizes (i + 1)).length ∧
      (g i).rightArity = (sizes i).length := by
    intro i
    exact ⟨(hbase i).1.symm, (hbase i).2.1.symm⟩
  exact interval_concat g (fun i => (sizes i).length) harity comp_assoc_compatible i j k hij hjk
end NishtAbel2024V2.SCTPort
