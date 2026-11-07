# Sized Types & Type-Based Termination in Lean 4

Sound type-based termination, modular size-change inference, and computational coinduction in Lean 4 — combining **machine-checked metatheory (`0 sorry`)**, **formal soundness audits**, **verified elaboration**, and **prototype implementation**.

---

## Highlights & Current Status

### 1. Complete Mechanization of Nisht & Abel (2024) (`NishtAbel2024V5`) — **Proved (`0 sorry`)**
We provide a complete, `0 sorry` Lean 4 formalization and soundness proof of **Kanstantsin Nisht & Andreas Abel (2024)**, *Type-Based Termination Checking in Agda* (Chalmers MSc Thesis & TYPES 2024), using only Lean's standard axioms (`[propext, Classical.choice, Quot.sound]`):

- **Full Calculus ($\text{System } F_\omega^{\text{cop,SCT}}$, Chapter 4)** — [`Definitions/Def_NishtAbel2024V5_Syntax.lean`](Definitions/Def_NishtAbel2024V5_Syntax.lean):
  - First-class size algebra (`∞ + n`, `i + n`, meets `a ∧ b`, bound normalization `a^↑`),
  - Polarized higher-kinded variance (`κ ::= * | π κ₁ → κ₂` over `◦ ≤ +, − ≤ ⊤`),
  - Higher-kinded type operators (`λ(X : ι). F`, `F G`) and impredicative type polymorphism (`∀(X : κ). B`, `∃(X : κ). B`),
  - Bounded size quantifiers (`∀(j < a). B`, `∃(j < a). B`),
  - Positive and mixed-variance inductive ($\mu^a S$) and coinductive ($\nu^a R$) fixpoints,
  - Copattern spines, mutual declaration blocks, and Lee–Jones–Ben-Amram size-change invocation graphs (`SCTValid`).
- **Ordinal Reducibility Semantics & Lexicographic Measure Embedding (Chapter 5)** — [`Definitions/Def_NishtAbel2024V5_Semantics.lean`](Definitions/Def_NishtAbel2024V5_Semantics.lean), [`Solutions/V5/`](Solutions/V5/):
  - Interprets `∞` at the cardinal-successor initial ordinal $\Omega = (\text{Order.succ }(\#\text{Tm})).\text{ord}$ so higher-order / infinitely branching fixpoints stabilize ([`Solutions/V5/Stable.lean`](Solutions/V5/Stable.lean)),
  - Proves Infinite Ramsey's Theorem via ultrafilters ([`Solutions/V3/SCT/Ramsey.lean`](Solutions/V3/SCT/Ramsey.lean)) and well-foundedness of semantic size-change call relations (**Theorem 1**, `callRel_wf`),
  - Proves two-valuation size soundness, higher-kinded reducibility (`KRel`), and polarized subtyping soundness (**Theorem 2**),
  - Proves the Fundamental Lemma of expression and copattern clause typing (**Theorem 3**),
  - Proves strong normalization (`SN`) of mutual blocks and complete programs (**Theorem 4**, **Lemma 2**, **Theorem 5**),
  - Proves conservative embedding of Abel & Pientka's lexicographic mutual measure calculus $F_\omega^{\text{cop}}$ into $F_\omega^{\text{cop,SCT}}$ (**Theorem 6**, [`Solutions/V5/Theorem6.lean`](Solutions/V5/Theorem6.lean)).
- **Modular Size Inference & Constraint Solver (Chapter 6)** — [`Definitions/Def_NishtAbel2024V5_Inference.lean`](Definitions/Def_NishtAbel2024V5_Inference.lean), [`Solutions/V5/`](Solutions/V5/):
  - Polarized signature encoding (`Encode`), pattern/copattern spine rigid-variable inference (`InferPat`, `InferSpine`), bidirectional type comparison (`Compare`), and call-site constraint generation (`InferTm`, `CheckTm`, `CheckClause`),
  - Executable SCC constraint solver (`solve`, **Algorithm 1**) and verified scope/coherence decision procedures (`sizeLtB`, `sizeLeB`, `checkScope`, `checkCoherent`),
  - Complete proofs of **Theorems 7–15** and **Lemmas 3–5** ([`Solutions/V5/Final.lean`](Solutions/V5/Final.lean)), culminating in **Theorem 15** (`theorem_15`: every mutual block accepted by Algorithm 2 is well-typed in $F_\omega^{\text{cop,SCT}}$ and strongly normalizing).
- **Worked 5-Function Recursive/Corecursive Block** — [`Solutions/V5/Example.lean`](Solutions/V5/Example.lean):
  - End-to-end verification (`example_block_valid`) of a block containing `copy` (inductive `Nat`), `zeros` (coinductive `Stream` via copatterns), polymorphic `len` (`List`), bounded-size `count`, and higher-kinded/mixed-variance `evalT`.

### 2. Progressive Subcalculi (`V3`, `V4`) & Machine-Checked Soundness Audits
- **[`Solutions/V3/`](Solutions/V3/)**: Core first-order positive calculus + self-contained Infinite Ramsey & SCT well-foundedness library ([`Solutions/V3/SCT/`](Solutions/V3/SCT/)).
- **[`Solutions/V4/`](Solutions/V4/)**: Adds impredicative type polymorphism (`∀X`, `∃X`) and bounded size quantifiers (`∀(j < a)`, `∃(j < a)`).
- **[`Solutions/Audits/`](Solutions/Audits/) & [`docs/SOUNDNESS_AUDITS_AND_REPAIRS.md`](docs/SOUNDNESS_AUDITS_AND_REPAIRS.md)**: Machine-checked (`0 sorry`) counterexamples exposing subtle pitfalls in naive formalizations (clause-binder capture, $\infty = \omega$ closure ordinal, $\infty + n$ bound normalization, higher-order $\beta$-redex kinding, repeated negative $\mu$-indices, and forward-reference cycles) together with the 8 design repairs implemented in V5 ([`Solutions/V5/DESIGN.md`](Solutions/V5/DESIGN.md)).

---

## Repository Structure

```text
.
├── Definitions/
│   ├── Def_NishtAbel2024V5_Syntax.lean      # Full V5 calculus syntax, kinds, subtyping, SCT graphs
│   ├── Def_NishtAbel2024V5_Semantics.lean   # V5 operational semantics & Ω-indexed reducibility model
│   ├── Def_NishtAbel2024V5_Inference.lean   # V5 signature encoding, inference, SCC solver, Algorithm 2
│   ├── Def_NishtAbel2024V4_*.lean           # V4 subcalculus (type & bounded-size polymorphism)
│   ├── Def_NishtAbel2024V3_*.lean           # V3 core subcalculus
│   └── Def_NishtAbel2024*.lean              # V1/V2 historical definitions used by counterexample audits
├── Solutions/
│   ├── V5/
│   │   ├── Final.lean                       # Top-level proofs of Theorems 1–15, Lemmas 2–5, and example
│   │   ├── Example.lean                     # Worked 5-function inductive/coinductive block
│   │   ├── DESIGN.md                        # Architecture & 8 soundness repairs over the literal text
│   │   └── *.lean                           # Modular proof layers (Size, KindSound, SubSound, Fundamental, Inf*)
│   ├── V4/                                  # V4 proofs, worked example, and DESIGN.md
│   ├── V3/
│   │   ├── SCT/                             # Ultrafilter Infinite Ramsey & SCT well-foundedness proofs
│   │   └── *.lean                           # V3 proofs, worked example, and DESIGN.md
│   └── Audits/                              # Standalone 0-sorry counterexamples to V1/V2 formulations
├── docs/
│   ├── SOUNDNESS_AUDITS_AND_REPAIRS.md      # Synthesis of counterexamples & V5 metatheoretical fixes
│   └── audits/                              # Detailed writeups for individual counterexamples
├── plan.md                                  # Overall project roadmap (Formalization + Lean 4 Implementation)
├── RANT.md                                  # Background assessment on sized types in proof assistants
└── Nisht-Abel-2024-msc.pdf                  # Reference thesis (Nisht 2024, supervised by Andreas Abel)
```

---

## Building the Proofs

The project uses **Lean `v4.33.1`** and **Mathlib** (pinned in [`lake-manifest.json`](lake-manifest.json)).

```bash
# Fetch cached Mathlib build artifacts (optional but recommended)
lake exe cache get

# Build the full V5 theorem suite and verify standard axioms
lake build Solutions.V5.Final
```

At the end of [`Solutions/V5/Final.lean`](Solutions/V5/Final.lean), `#print axioms` confirms that all main theorems (`theorems_2_and_3`, `theorems_4_5_and_6`, `theorems_7_8_9_and_lemmas_3_4_5`, `theorems_10_11_and_12`, `theorems_13_and_14`, `theorem_15`, and `example_block_valid`) depend only on `[propext, Classical.choice, Quot.sound]`.

---

## Roadmap: Next Phases (See [`plan.md`](plan.md))

With the Nisht & Abel (2024) metatheory and inference pipeline fully mechanized in `NishtAbel2024V5`, the remaining phases in [`plan.md`](plan.md) focus on:

1. **Explicit Agda Soundness Regression Suite (Milestone 1.1)**: Standalone negative test files for Agda Issue #3026 ($\infty < \infty$) and Agda Issue #7178 (mixed inductive/coinductive positivity & non-upward-closed codata sizes).
2. **Verified Elaboration / Lowering Theorem (Milestone 1.2)**: Syntactic translation $\Gamma \vdash_{\text{sized}} t : A \implies \Gamma^\circ \vdash_{\text{Lean}} E(t) : A^\circ$ targeting standard Lean 4 kernel constructs (`brecOn` when spine-structural to preserve `rfl`; `WellFounded.fix` / `Acc` otherwise).
3. **Executable Bidirectional Prototype & Lean 4 Elaborator Pass (Stages 1, 2A, 2B)**: Turning the relational V5 inference pipeline (`Encode`, `InferPat`, `InferSpine`, `Compare`, `InferTm`, `CheckTm`) alongside the verified executable solver (`solve`, `sizeLtB`, `sizeLeB`) into an executable checker for compositional higher-order termination and computational codata in `Type`.
