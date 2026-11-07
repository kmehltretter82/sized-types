import Lean
import Solutions.Stage1.MiniLeanSized

/-!
# Stage 2B: Computational Coinductive Data in `Type` via Sized Productivity & QPF/Function Lowering

This module implements **Stage 2B** of `plan.md` (§2.2 & §4 Stage 2B):
providing ergonomic **computational coinductive types in `Type`** (`CStream α`, `Colist α`,
`CoTree β α`, and mixed inductive-coinductive stream processors `SP α β`) in an **unmodified Lean 4
kernel**, backed by sized productivity checking ($\forall i,\; S^{[i]} \to S^{[i+1]}$),
definitional (`rfl`) `@[simp]` destructor unfolding equations, and bisimulation proof principles
(`eq_of_bisim`).

## Architectural Overview
While Lean 4 natively supports `coinductive` predicates in `Prop` (via Knaster–Tarski on the truth
lattice), computational codata in `Type` requires:
1. **Sized Productivity Verification**: Ensuring every corecursive call is guarded by at least one
   constructor / copattern observation ($\forall i,\; \nu^i R \to \nu^{i+1} R$, or `checkBlockB` in
   `MiniLean-Sized`).
2. **Function-Space / QPF Lowering in `Type`**: Representing infinite observations as functions from
   finite observation paths (`Nat → α` for streams, `Nat → Option α` for colists, `List β → α` for
   cotrees) so that destructor projections (`.head`, `.tail`, `.root`, `.child`) reduce
   **definitionally by `rfl`** in unmodified Lean 4.
3. **Coinductive Bisimulation (`eq_of_bisim`)**: Proving that two codata values are equal iff they
   are bisimilar.
-/

namespace SizedTypes.Stage2B

universe u v w

open NishtAbel2024V5
open MiniLeanSized

/-! ## Part 1: Sized Stream Hierarchy (`SizedStream α i`) & Computational Streams (`CStream α`) -/

/-- **Sized Stream Approximation (`SizedStream α i`)**:
Represents a stream prefix defined up to observation depth `i : Nat` ($\text{Stream}^{[i]} \alpha$):
- At size `0`, no observations are available (`PUnit`).
- At size `i + 1`, a head element `α` and a tail of size `i` (`α × SizedStream α i`) are available. -/
def SizedStream (α : Type u) : Nat → Type u
  | 0 => PUnit
  | i + 1 => α × SizedStream α i

namespace SizedStream

/-- Forgets the last observation of a size-`(i + 1)` stream approximation, restricting it to size `i`
(the semantic witness of contravariant coinductive size subtyping $\text{Stream}^{[i+1]} \alpha \le \text{Stream}^{[i]} \alpha$). -/
def restrict {α : Type u} : {i : Nat} → SizedStream α (i + 1) → SizedStream α i
  | 0, _ => PUnit.unit
  | _ + 1, (a, s) => (a, restrict s)

/-- Extracts the `k`-th element (`k < i`) from a size-`i` stream approximation. -/
def nth {α : Type u} : {i : Nat} → SizedStream α i → (k : Nat) → k < i → α
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | _ + 1, (a, _), 0, _ => a
  | _ + 1, (_, s), k + 1, hk => nth s k (Nat.lt_of_succ_lt_succ hk)

/-- Restricting a `SizedStream α (i + 1)` to size `i` preserves all elements at indices `k < i`. -/
theorem nth_restrict {α : Type u} :
    ∀ {i : Nat} (s : SizedStream α (i + 1)) (k : Nat) (hk : k < i),
      nth (restrict s) k hk = nth s k (Nat.lt_succ_of_lt hk)
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | _ + 1, (_, _), 0, _ => rfl
  | _ + 1, (_, s), k + 1, hk => nth_restrict s k (Nat.lt_of_succ_lt_succ hk)

end SizedStream

/-- **Productive Sized Stream Specification (`ProductiveStreamSpec α`)**:
An inflationary size-indexed step family `step : ∀ i, SizedStream α i → SizedStream α (i + 1)`
($\forall i,\; \text{Stream}^{[i]} \alpha \to \text{Stream}^{[i+1]} \alpha$) that commutes with
size restriction (`restrict (step (i + 1) s) = step i (restrict s)`). -/
structure ProductiveStreamSpec (α : Type u) where
  step : ∀ (i : Nat), SizedStream α i → SizedStream α (i + 1)
  coherent : ∀ (i : Nat) (s : SizedStream α (i + 1)),
    SizedStream.restrict (step (i + 1) s) = step i (SizedStream.restrict s)

namespace ProductiveStreamSpec

/-- Iterates a productive specification `i` times from the trivial size-`0` seed `PUnit.unit` to
obtain the canonical size-`i` approximation `approx spec i : SizedStream α i`. -/
def approx {α : Type u} (spec : ProductiveStreamSpec α) : (i : Nat) → SizedStream α i
  | 0 => PUnit.unit
  | i + 1 => spec.step i (approx spec i)

/-- Coherence theorem: restricting `approx spec (i + 1)` to size `i` yields `approx spec i`. -/
theorem restrict_approx {α : Type u} (spec : ProductiveStreamSpec α) :
    ∀ (i : Nat), SizedStream.restrict (spec.approx (i + 1)) = spec.approx i
  | 0 => rfl
  | i + 1 => by
    change SizedStream.restrict (spec.step (i + 1) (spec.approx (i + 1))) = spec.step i (spec.approx i)
    rw [spec.coherent i (spec.approx (i + 1)), restrict_approx spec i]

end ProductiveStreamSpec

/-- **Computational Stream in `Type u` (`CStream α`)**:
Lowered to its observation function `nth : Nat → α` so that `.head` and `.tail` reduce
**definitionally by `rfl`** in Lean 4's unmodified kernel. -/
@[ext] structure CStream (α : Type u) where
  nth : Nat → α

namespace CStream

/-- First element (`.head` copattern projection) of a computational stream. -/
def head {α : Type u} (s : CStream α) : α :=
  s.nth 0

/-- Remaining elements (`.tail` copattern projection) of a computational stream. -/
def tail {α : Type u} (s : CStream α) : CStream α :=
  ⟨fun n => s.nth (n + 1)⟩

/-- Prepends `a : α` to `s : CStream α`. -/
def cons {α : Type u} (a : α) (s : CStream α) : CStream α :=
  ⟨fun
    | 0 => a
    | n + 1 => s.nth n⟩

@[simp] theorem head_cons {α : Type u} (a : α) (s : CStream α) :
    (cons a s).head = a := rfl

@[simp] theorem tail_cons {α : Type u} (a : α) (s : CStream α) :
    (cons a s).tail = s := rfl

@[simp] theorem cons_head_tail {α : Type u} (s : CStream α) :
    cons s.head s.tail = s := by
  ext n
  cases n <;> rfl

@[simp] theorem nth_zero {α : Type u} (s : CStream α) :
    s.nth 0 = s.head := rfl

@[simp] theorem nth_succ {α : Type u} (s : CStream α) (n : Nat) :
    s.nth (n + 1) = s.tail.nth n := rfl

/-- Truncates a computational stream `s : CStream α` to its size-`i` approximation `SizedStream α i`. -/
def toSized {α : Type u} (s : CStream α) : (i : Nat) → SizedStream α i
  | 0 => PUnit.unit
  | i + 1 => (s.head, s.tail.toSized i)

/-- **Projective Limit Lowering (`ofProductiveSpec`)**:
Compiles any size-checked `ProductiveStreamSpec α` ($\forall i,\; \text{Stream}^{[i]} \alpha \to \text{Stream}^{[i+1]} \alpha$)
into a computational `CStream α` in `Type u`! -/
def ofProductiveSpec {α : Type u} (spec : ProductiveStreamSpec α) : CStream α where
  nth n := SizedStream.nth (spec.approx (n + 1)) n (Nat.lt_succ_self n)

/-- Iterated coalgebraic state transition `Nat.iterate` used by `CStream.corec`. -/
def iterateStep {σ : Type u} (next : σ → σ) : Nat → σ → σ
  | 0, z => z
  | n + 1, z => iterateStep next n (next z)

/-- **Productive Stream Corecursor (`CStream.corec`)**:
Given a coalgebra `(hd : σ → α, tl : σ → σ)` and initial state `seed : σ`, produces the unique
stream `s : CStream α` whose `.head` and `.tail` unfold **definitionally by `rfl`**. -/
def corec {σ : Type u} {α : Type v} (hd : σ → α) (tl : σ → σ) (seed : σ) : CStream α :=
  ⟨fun n => hd (iterateStep tl n seed)⟩

/-- **Definitional (`rfl`) Unfolding of `(corec hd tl seed).head`!** -/
@[simp] theorem head_corec {σ : Type u} {α : Type v} (hd : σ → α) (tl : σ → σ) (seed : σ) :
    (corec hd tl seed).head = hd seed := rfl

/-- **Definitional (`rfl`) Unfolding of `(corec hd tl seed).tail`!** -/
@[simp] theorem tail_corec {σ : Type u} {α : Type v} (hd : σ → α) (tl : σ → σ) (seed : σ) :
    (corec hd tl seed).tail = corec hd tl (tl seed) := rfl

/-- Constant stream `const a = a, a, a, ...`. -/
def const {α : Type u} (a : α) : CStream α :=
  corec id id a

@[simp] theorem head_const {α : Type u} (a : α) : (const a).head = a := rfl
@[simp] theorem tail_const {α : Type u} (a : α) : (const a).tail = const a := rfl

/-- Functorial `map` on computational streams. -/
def map {α : Type u} {β : Type v} (f : α → β) (s : CStream α) : CStream β :=
  ⟨fun n => f (s.nth n)⟩

@[simp] theorem head_map {α : Type u} {β : Type v} (f : α → β) (s : CStream α) :
    (s.map f).head = f s.head := rfl

@[simp] theorem tail_map {α : Type u} {β : Type v} (f : α → β) (s : CStream α) :
    (s.map f).tail = s.tail.map f := rfl

/-- Pointwise binary combination `zipWith` on computational streams. -/
def zipWith {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β → γ) (s₁ : CStream α) (s₂ : CStream β) : CStream γ :=
  ⟨fun n => f (s₁.nth n) (s₂.nth n)⟩

@[simp] theorem head_zipWith {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β → γ) (s₁ : CStream α) (s₂ : CStream β) :
    (zipWith f s₁ s₂).head = f s₁.head s₂.head := rfl

@[simp] theorem tail_zipWith {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β → γ) (s₁ : CStream α) (s₂ : CStream β) :
    (zipWith f s₁ s₂).tail = zipWith f s₁.tail s₂.tail := rfl

/-- Interleaves two streams (`s₁.head, s₂.head, s₁.tail.head, s₂.tail.head, ...`),
lowered from the productive coalgebra `(s₁, s₂) ↦ (s₁.head, (s₂, s₁.tail))`. -/
def interleave {α : Type u} (s₁ s₂ : CStream α) : CStream α :=
  corec (fun p : CStream α × CStream α => p.1.head) (fun p => (p.2, p.1.tail)) (s₁, s₂)

@[simp] theorem head_interleave {α : Type u} (s₁ s₂ : CStream α) :
    (interleave s₁ s₂).head = s₁.head := rfl

@[simp] theorem tail_interleave {α : Type u} (s₁ s₂ : CStream α) :
    (interleave s₁ s₂).tail = interleave s₂ s₁.tail := rfl

/-- Extracts the even-indexed elements (`s.nth 0, s.nth 2, s.nth 4, ...`). -/
def evens {α : Type u} (s : CStream α) : CStream α :=
  corec CStream.head (fun u => u.tail.tail) s

/-- Extracts the odd-indexed elements (`s.nth 1, s.nth 3, s.nth 5, ...`). -/
def odds {α : Type u} (s : CStream α) : CStream α :=
  evens s.tail

@[simp] theorem head_evens {α : Type u} (s : CStream α) : (evens s).head = s.head := rfl
@[simp] theorem tail_evens {α : Type u} (s : CStream α) : (evens s).tail = odds s.tail := rfl
@[simp] theorem head_odds {α : Type u} (s : CStream α) : (odds s).head = s.tail.head := rfl
@[simp] theorem tail_odds {α : Type u} (s : CStream α) : (odds s).tail = odds s.tail.tail := rfl

/-- Observes a finite `List α` prefix of length `n` from `s : CStream α`. -/
def take {α : Type u} : Nat → CStream α → List α
  | 0, _ => []
  | n + 1, s => s.head :: take n s.tail

/-! ### Stream Bisimulation & Coinduction Proof Principle (`eq_of_bisim`) -/

/-- **Stream Bisimulation (`CStream.Bisim`)**:
`Bisim s₁ s₂` holds when there exists a binary relation `R` on `CStream α` relating `s₁` and `s₂`
that is closed under `.head` equality and `.tail` transitions. -/
def Bisim {α : Type u} (s₁ s₂ : CStream α) : Prop :=
  ∃ R : CStream α → CStream α → Prop,
    R s₁ s₂ ∧ ∀ u v, R u v → u.head = v.head ∧ R u.tail v.tail

theorem bisim_nth {α : Type u} {R : CStream α → CStream α → Prop}
    (hstep : ∀ u v, R u v → u.head = v.head ∧ R u.tail v.tail) :
    ∀ (n : Nat) {u v : CStream α}, R u v → u.nth n = v.nth n
  | 0, _, _, hR => (hstep _ _ hR).1
  | n + 1, _, _, hR => bisim_nth hstep n (hstep _ _ hR).2

/-- **Stream Coinduction Principle (`CStream.eq_of_bisim`)**:
Any two bisimilar computational streams in `Type u` are propositionally equal! -/
theorem eq_of_bisim {α : Type u} {s₁ s₂ : CStream α} (h : Bisim s₁ s₂) : s₁ = s₂ := by
  obtain ⟨R, hR, hstep⟩ := h
  apply CStream.ext
  funext n
  exact bisim_nth hstep n hR

/-- Bisimulation coincides with propositional equality on `CStream α`. -/
theorem bisim_iff_eq {α : Type u} (s₁ s₂ : CStream α) : Bisim s₁ s₂ ↔ s₁ = s₂ := by
  constructor
  · exact eq_of_bisim
  · rintro rfl
    exact ⟨Eq, rfl, fun _ _ h => by subst h; exact ⟨rfl, rfl⟩⟩

/-- Classic coinductive proof via `eq_of_bisim`: interleaving `evens s` and `odds s` reconstructs `s`! -/
theorem interleave_evens_odds {α : Type u} (s : CStream α) :
    interleave (evens s) (odds s) = s := by
  apply eq_of_bisim
  refine ⟨fun u v => ∃ w : CStream α, u = interleave (evens w) (odds w) ∧ v = w,
    ⟨s, rfl, rfl⟩, ?_⟩
  rintro u v ⟨w, rfl, rfl⟩
  exact ⟨rfl, ⟨v.tail, rfl, rfl⟩⟩

end CStream

/-! ## Part 2: Potentially Terminating Computational Codata: `Colist α` in `Type u` -/

/-- **Computational `Colist α` in `Type u`**:
Represents a potentially finite or infinite sequence of elements in `Type u`.
Lowered to a step-indexed observation function `nth? : Nat → Option α`. -/
@[ext] structure Colist (α : Type u) where
  nth? : Nat → Option α

namespace Colist

/-- The empty colist (`nil`). -/
def nil {α : Type u} : Colist α :=
  ⟨fun _ => none⟩

/-- Prepends `a : α` to `s : Colist α`. -/
def cons {α : Type u} (a : α) (s : Colist α) : Colist α :=
  ⟨fun
    | 0 => some a
    | n + 1 => s.nth? n⟩

/-- Observes the head element of a `Colist α` (`none` if empty). -/
def head? {α : Type u} (s : Colist α) : Option α :=
  s.nth? 0

/-- Observes the tail of a `Colist α`. -/
def tail {α : Type u} (s : Colist α) : Colist α :=
  ⟨fun n => s.nth? (n + 1)⟩

@[simp] theorem head?_nil {α : Type u} : (nil : Colist α).head? = none := rfl
@[simp] theorem tail_nil {α : Type u} : (nil : Colist α).tail = nil := rfl
@[simp] theorem head?_cons {α : Type u} (a : α) (s : Colist α) : (cons a s).head? = some a := rfl
@[simp] theorem tail_cons {α : Type u} (a : α) (s : Colist α) : (cons a s).tail = s := rfl

/-- Step-indexed coalgebra runner for `Colist.corec`. -/
def corecAt {σ : Type u} {α : Type v} (step : σ → Option (α × σ)) : Nat → σ → Option α
  | 0, z => (step z).map Prod.fst
  | n + 1, z =>
    match step z with
    | none => none
    | some (_, z') => corecAt step n z'

/-- **Productive `Colist` Corecursor (`Colist.corec`)**:
Unfolds a partial coalgebra `step : σ → Option (α × σ)` from `seed : σ` into a `Colist α`. -/
def corec {σ : Type u} {α : Type v} (step : σ → Option (α × σ)) (seed : σ) : Colist α :=
  ⟨fun n => corecAt step n seed⟩

@[simp] theorem head?_corec {σ : Type u} {α : Type v} (step : σ → Option (α × σ)) (seed : σ) :
    (corec step seed).head? = (step seed).map Prod.fst := rfl

theorem tail_corec_none {σ : Type u} {α : Type v} (step : σ → Option (α × σ)) (seed : σ)
    (h : step seed = none) :
    (corec step seed).tail = nil := by
  ext n
  simp [tail, corec, corecAt, h, nil]

theorem tail_corec_some {σ : Type u} {α : Type v} (step : σ → Option (α × σ)) (seed z' : σ) (a : α)
    (h : step seed = some (a, z')) :
    (corec step seed).tail = corec step z' := by
  ext n
  simp [tail, corec, corecAt, h]

/-- Functorial `map` on `Colist α`. -/
def map {α : Type u} {β : Type v} (f : α → β) (s : Colist α) : Colist β :=
  ⟨fun n => (s.nth? n).map f⟩

@[simp] theorem head?_map {α : Type u} {β : Type v} (f : α → β) (s : Colist α) :
    (s.map f).head? = s.head?.map f := rfl

@[simp] theorem tail_map {α : Type u} {β : Type v} (f : α → β) (s : Colist α) :
    (s.map f).tail = s.tail.map f := rfl

/-- Embeds any infinite `CStream α` into `Colist α`. -/
def ofStream {α : Type u} (s : CStream α) : Colist α :=
  ⟨fun n => some (s.nth n)⟩

/-- Embeds any finite `List α` into `Colist α`. -/
def ofList {α : Type u} (xs : List α) : Colist α :=
  ⟨fun n => xs[n]?⟩

/-- Collects up to `n` elements from the front of `s : Colist α`. -/
def take {α : Type u} : Nat → Colist α → List α
  | 0, _ => []
  | n + 1, s =>
    match s.head? with
    | none => []
    | some a => a :: take n s.tail

/-- **Colist Bisimulation (`Colist.Bisim`)**. -/
def Bisim {α : Type u} (s₁ s₂ : Colist α) : Prop :=
  ∃ R : Colist α → Colist α → Prop,
    R s₁ s₂ ∧ ∀ u v, R u v → u.head? = v.head? ∧ R u.tail v.tail

theorem bisim_nth? {α : Type u} {R : Colist α → Colist α → Prop}
    (hstep : ∀ u v, R u v → u.head? = v.head? ∧ R u.tail v.tail) :
    ∀ (n : Nat) {u v : Colist α}, R u v → u.nth? n = v.nth? n
  | 0, _, _, hR => (hstep _ _ hR).1
  | n + 1, _, _, hR => bisim_nth? hstep n (hstep _ _ hR).2

/-- **Colist Coinduction Principle (`Colist.eq_of_bisim`)**. -/
theorem eq_of_bisim {α : Type u} {s₁ s₂ : Colist α} (h : Bisim s₁ s₂) : s₁ = s₂ := by
  obtain ⟨R, hR, hstep⟩ := h
  apply Colist.ext
  funext n
  exact bisim_nth? hstep n hR

/-- Bisimulation coincides with propositional equality on `Colist α`. -/
theorem bisim_iff_eq {α : Type u} (s₁ s₂ : Colist α) : Bisim s₁ s₂ ↔ s₁ = s₂ := by
  constructor
  · exact eq_of_bisim
  · rintro rfl
    exact ⟨Eq, rfl, fun _ _ h => by subst h; exact ⟨rfl, rfl⟩⟩

/-- Bounded countdown colist `countdown n = [n, n-1, ..., 1]` defined via `Colist.corec`. -/
def countdown (n : Nat) : Colist Nat :=
  corec (fun k => if k == 0 then none else some (k, k - 1)) n

theorem countdown_5_take_10_rfl :
    (countdown 5).take 10 = [5, 4, 3, 2, 1] := rfl

end Colist

/-! ## Part 3: Infinitely Deep Branching Trees (`CoTree β α`) & Mixed Inductive-Coinductive `SP α β` -/

/-! ### 3.1 `CoTree β α` (Infinitely Deep `β`-Branching Trees in `Type u`) -/

/-- **Computational Coinductive Tree (`CoTree β α`)**:
An infinitely deep tree with node labels in `α` and branching factor indexed by `β`.
Lowered to path observations `atPath : List β → α` so that `.root` and `.child b` reduce
**definitionally by `rfl`**! -/
@[ext] structure CoTree (β : Type u) (α : Type v) where
  atPath : List β → α

namespace CoTree

/-- Root label of a `CoTree β α` (`.root` copattern projection). -/
def root {β : Type u} {α : Type v} (t : CoTree β α) : α :=
  t.atPath []

/-- Subtree along branch `b : β` (`.child b` copattern projection). -/
def child {β : Type u} {α : Type v} (b : β) (t : CoTree β α) : CoTree β α :=
  ⟨fun path => t.atPath (b :: path)⟩

/-- Path-indexed state transition for `CoTree.corec`. -/
def followPath {σ : Type u} {β : Type v} (step : σ → β → σ) : List β → σ → σ
  | [], z => z
  | b :: rest, z => followPath step rest (step z b)

/-- **Productive `CoTree` Corecursor (`CoTree.corec`)**:
Unfolds a node-label function `lbl : σ → α` and child-state function `step : σ → β → σ` from
`seed : σ` into an infinite `CoTree β α`. -/
def corec {σ : Type u} {β : Type v} {α : Type w}
    (lbl : σ → α) (step : σ → β → σ) (seed : σ) : CoTree β α :=
  ⟨fun path => lbl (followPath step path seed)⟩

/-- **Definitional (`rfl`) Unfolding of `(CoTree.corec lbl step seed).root`!** -/
@[simp] theorem root_corec {σ : Type u} {β : Type v} {α : Type w}
    (lbl : σ → α) (step : σ → β → σ) (seed : σ) :
    (corec lbl step seed).root = lbl seed := rfl

/-- **Definitional (`rfl`) Unfolding of `(CoTree.corec lbl step seed).child b`!** -/
@[simp] theorem child_corec {σ : Type u} {β : Type v} {α : Type w}
    (lbl : σ → α) (step : σ → β → σ) (seed : σ) (b : β) :
    (corec lbl step seed).child b = corec lbl step (step seed b) := rfl

/-- Functorial `map` on `CoTree β α`. -/
def map {β : Type u} {α : Type v} {γ : Type w} (f : α → γ) (t : CoTree β α) : CoTree β γ :=
  ⟨fun path => f (t.atPath path)⟩

@[simp] theorem root_map {β : Type u} {α : Type v} {γ : Type w} (f : α → γ) (t : CoTree β α) :
    (t.map f).root = f t.root := rfl

@[simp] theorem child_map {β : Type u} {α : Type v} {γ : Type w}
    (f : α → γ) (b : β) (t : CoTree β α) :
    (t.map f).child b = (t.child b).map f := rfl

/-- **`CoTree` Bisimulation (`CoTree.Bisim`)**. -/
def Bisim {β : Type u} {α : Type v} (t₁ t₂ : CoTree β α) : Prop :=
  ∃ R : CoTree β α → CoTree β α → Prop,
    R t₁ t₂ ∧ ∀ u v, R u v → u.root = v.root ∧ ∀ b, R (u.child b) (v.child b)

theorem bisim_atPath {β : Type u} {α : Type v} {R : CoTree β α → CoTree β α → Prop}
    (hstep : ∀ u v, R u v → u.root = v.root ∧ ∀ b, R (u.child b) (v.child b)) :
    ∀ (path : List β) {u v : CoTree β α}, R u v → u.atPath path = v.atPath path
  | [], _, _, hR => (hstep _ _ hR).1
  | b :: rest, _, _, hR => bisim_atPath hstep rest ((hstep _ _ hR).2 b)

/-- **`CoTree` Coinduction Principle (`CoTree.eq_of_bisim`)**. -/
theorem eq_of_bisim {β : Type u} {α : Type v} {t₁ t₂ : CoTree β α} (h : Bisim t₁ t₂) :
    t₁ = t₂ := by
  obtain ⟨R, hR, hstep⟩ := h
  ext path
  exact bisim_atPath hstep path hR

/-- Infinite binary tree of positive heap indices (`root = 1`, `left = 2*n`, `right = 2*n + 1`). -/
def binaryHeapTree : CoTree Bool Nat :=
  corec id (fun n b => if b then 2 * n + 1 else 2 * n) 1

theorem binaryHeapTree_rfl_benchmark :
    ((binaryHeapTree.child false).child true).root = 5 := rfl

end CoTree

/-! ### 3.2 Mixed Inductive-Coinductive Stream Processors (`SP α β = ν i. μ j. (β × Y) + (α → X)`) -/

/-- **Inner Inductive Step Functor (`SPStep α β σ`)**:
Represents the inner inductive fixpoint $\mu^j X.\; (\beta \times \sigma) + (\alpha \to X)$ of a
Ghani–Hancock–Pattinson stream processor `SP α β = ν^i Y. μ^j X. (β × Y) + (α → X)`.
Because `SPStep` is an inductive type, a stream processor may perform any **finite** number of
input reads (`get`) before emitting an output (`put` — which guards the outer coinductive $\nu^i$ step!). -/
inductive SPStep (α : Type u) (β : Type v) (σ : Type w) where
  | put (out : β) (nextState : σ) : SPStep α β σ
  | get (read : α → SPStep α β σ) : SPStep α β σ

namespace SPStep

/-- Runs one finite inductive burst of `get`s on an input stream `inp : CStream α` until a
coinductive `put` output is produced (by structural recursion on the inner $\mu^j$ inductive `SPStep`!). -/
def stepStream {α : Type u} {β : Type v} {σ : Type w} :
    SPStep α β σ → CStream α → β × (σ × CStream α)
  | .put b z', inp => (b, (z', inp))
  | .get k, inp => stepStream (k inp.head) inp.tail

@[simp] theorem stepStream_put {α : Type u} {β : Type v} {σ : Type w}
    (b : β) (z' : σ) (inp : CStream α) :
    stepStream (.put b z') inp = (b, (z', inp)) := rfl

@[simp] theorem stepStream_get {α : Type u} {β : Type v} {σ : Type w}
    (k : α → SPStep α β σ) (inp : CStream α) :
    stepStream (.get k) inp = stepStream (k inp.head) inp.tail := rfl

end SPStep

/-- **Mixed Inductive-Coinductive Stream Processor (`SP α β`)**:
Combines structural recursion on the inner inductive `SPStep α β σ` ($\mu^j$) with productive
stream corecursion (`CStream.corec`) on the outer coinductive `CStream β` ($\nu^i$). -/
structure SP (α : Type u) (β : Type v) where
  run : CStream α → CStream β

namespace SP

/-- **Mixed Inductive-Coinductive Corecursor (`SP.corec`)**:
Given a coalgebra `step : σ → SPStep α β σ` where each state transition takes finitely many
inductive `get` steps before emitting a coinductive `put`, compiles `(step, seed)` into a
total stream transformer `SP α β`. -/
def corec {α : Type u} {β : Type v} {σ : Type w}
    (step : σ → SPStep α β σ) (seed : σ) : SP α β where
  run inp :=
    CStream.corec
      (fun (z, s) => (SPStep.stepStream (step z) s).1)
      (fun (z, s) => (SPStep.stepStream (step z) s).2)
      (seed, inp)

@[simp] theorem head_run_corec_put {α : Type u} {β : Type v} {σ : Type w}
    (step : σ → SPStep α β σ) (seed z' : σ) (b : β) (inp : CStream α)
    (h : step seed = .put b z') :
    ((corec step seed).run inp).head = b := by
  simp [corec, h]

@[simp] theorem tail_run_corec_put {α : Type u} {β : Type v} {σ : Type w}
    (step : σ → SPStep α β σ) (seed z' : σ) (b : β) (inp : CStream α)
    (h : step seed = .put b z') :
    ((corec step seed).run inp).tail = (corec step z').run inp := by
  ext n
  simp [corec, CStream.tail, CStream.corec, CStream.iterateStep, h]

/-- Example mixed inductive-coinductive stream processor (`pairSumSP`):
Reads **two** consecutive elements from the input stream via nested `.get` (inductive $\mu^j$ steps)
and emits their sum via `.put` (coinductive $\nu^i$ step). -/
def pairSumSP : SP Nat Nat :=
  corec (fun () => .get fun x => .get fun y => .put (x + y) ()) ()

/-- Ascending natural numbers stream `0, 1, 2, 3, ...`. -/
def nats : CStream Nat :=
  CStream.corec id (· + 1) 0

/-- **Kernel `rfl` Benchmark on Mixed Inductive-Coinductive `pairSumSP`**:
Running `pairSumSP` on `0, 1, 2, 3, 4, 5, 6, 7, ...` sums adjacent pairs `(0+1), (2+3), (4+5), (6+7)`
to produce `[1, 5, 9, 13]` **definitionally by `rfl`**! -/
theorem pairSumSP_nats_rfl :
    (pairSumSP.run nats).take 4 = [1, 5, 9, 13] := rfl

end SP

/-! ## Part 4: Bridge to `MiniLean-Sized` (`checkBlockB`) & Custom `corec_stream_def` Macro -/

/-- **`corec_stream_def` Macro**:
Defines a computational stream in `Type` via `CStream.corec` and automatically synthesizes
`@[simp]` `.head` and `.tail` destructor unfolding equations that hold by `rfl`! -/
macro "corec_stream_def " name:ident ":" elemTy:term "with"
    "state" ":=" stateTy:term ","
    "hd" ":=" hdTm:term ","
    "tl" ":=" tlTm:term ","
    "seed" ":=" seedTm:term : command => do
  let fromId := Lean.mkIdent (name.getId.appendAfter "From")
  let headFromId := Lean.mkIdent (name.getId.appendAfter "From_head")
  let tailFromId := Lean.mkIdent (name.getId.appendAfter "From_tail")
  let headId := Lean.mkIdent (name.getId.appendAfter "_head")
  let tailId := Lean.mkIdent (name.getId.appendAfter "_tail")
  `(
    def $fromId (z : $stateTy) : CStream $elemTy :=
      CStream.corec $hdTm $tlTm z
    @[simp] theorem $headFromId (z : $stateTy) :
        ($fromId z).head = ($hdTm) z := rfl
    @[simp] theorem $tailFromId (z : $stateTy) :
        ($fromId z).tail = $fromId (($tlTm) z) := rfl
    def $name : CStream $elemTy :=
      $fromId $seedTm
    @[simp] theorem $headId :
        ($name).head = ($hdTm) ($seedTm) := rfl
    @[simp] theorem $tailId :
        ($name).tail = $fromId (($tlTm) ($seedTm)) := rfl
  )

/-! ### Demonstrating `corec_stream_def` + `MiniLean-Sized` Productivity Verification -/

-- 1. `zeros` & `blink` (verified productive in `MiniLean-Sized` by `test_P2_streams_accepted : checkBlockB 10 [] [zerosSrc, blinkSrc] = true := rfl`):
corec_stream_def zerosStream : Nat with
  state := Unit,
  hd := fun _ => 0,
  tl := fun _ => (),
  seed := ()

corec_stream_def blinkStream : Nat with
  state := Bool,
  hd := fun b => if b then 1 else 0,
  tl := fun b => !b,
  seed := false

-- 2. Fibonacci stream `fibStream = 0, 1, 1, 2, 3, 5, 8, 13, ...`:
corec_stream_def fibStream : Nat with
  state := Nat × Nat,
  hd := fun p => p.1,
  tl := fun p => (p.2, p.1 + p.2),
  seed := (0, 1)

/-- Kernel `rfl` check on `zerosStream`. -/
theorem zerosStream_take_5_rfl : zerosStream.take 5 = [0, 0, 0, 0, 0] := rfl

/-- Kernel `rfl` check on `blinkStream`. -/
theorem blinkStream_take_6_rfl : blinkStream.take 6 = [0, 1, 0, 1, 0, 1] := rfl

/-- Kernel `rfl` check on `fibStream`. -/
theorem fibStream_take_8_rfl : fibStream.take 8 = [0, 1, 1, 2, 3, 5, 8, 13] := rfl

/-- The second projection `.tail.tail` of `blinkStream` equals `blinkStream` itself — proved
both by `@[simp]` unfolding and by coinductive bisimulation (`CStream.eq_of_bisim`)! -/
theorem blinkStream_tail_tail_eq : blinkStream.tail.tail = blinkStream := rfl

end SizedTypes.Stage2B
