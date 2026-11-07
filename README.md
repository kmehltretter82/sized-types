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
│   ├── Milestones/
│   │   ├── Milestone1_1_AgdaBugBenchmarks.lean      # Mechanized Agda #3026 & #7178 benchmarks + V5 blocking proofs
│   │   ├── Milestone1_2_VerifiedElaboration.lean    # Verified elaboration E(t), dual lowering, SCT WF lowering
│   │   └── Milestone1_3_LargeSizesAndModularity.lean # Parametric large sizes vs. Choice (FSCD 2026) & modular SCT library checker
│   ├── Stage1/
│   │   └── MiniLeanSized.lean               # Executable bidirectional size-change checker + soundness + regression suite
│   ├── Stage2/
│   │   ├── Stage2A_CompositionalTermination.lean # Stage 2A: SCT-to-Lean bridge, dual lowering, custom commands
│   │   └── Stage2B_ComputationalCodata.lean # Stage 2B: Computational codata (CStream, Colist, CoTree, SP), bisimulation, corec macro
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

### 3. Milestones 1.1, 1.2 & 1.3: Agda Soundness Benchmarks, Verified Elaboration & Parametric Large Sizes (`0 sorry`)
- **[`Solutions/Milestones/Milestone1_1_AgdaBugBenchmarks.lean`](Solutions/Milestones/Milestone1_1_AgdaBugBenchmarks.lean) (Milestone 1.1)**:
  - **Class A (Agda Issue #3026 — $\infty < \infty$)**: Negative contradiction benchmarks (`agda3026_wf_contradiction`, `agda3026_bad_inductive_contradiction`), operational non-normalization (`agda3026_loop_not_sn`), and positive blocking theorems in `NishtAbel2024V5` (`v5_not_sizeLt_infty_infty`, `v5_sizeLtB_inf_self_false`, `v5_rejects_agda3026_self_instantiation`).
  - **Class B (Agda Issue #7178 — Mixed Inductive/Coinductive Positivity & Size Variance without $\infty < \infty$)**: Finite-size ($0 < 1$) negative contradiction benchmarks (`agda7178_finite_size_nonpos_subtyping_contradiction`, `agda7178_mutual_ind_coind_variance_contradiction`), positive blocking theorems in `NishtAbel2024V5` (`v5_rejects_negative_functor_at_pos_polarity`, `v5_encode_forbids_shared_mu_nu_size`), and positive acceptance of valid mixed blocks (`v5_accepts_valid_mixed_block`).
- **[`Solutions/Milestones/Milestone1_2_VerifiedElaboration.lean`](Solutions/Milestones/Milestone1_2_VerifiedElaboration.lean) (Milestone 1.2)**:
  - **Verified Elaboration & Erasure Theorem (`elaborate_sound_and_coherent`)**: Translates size-checked derivations $\Gamma \vdash_{\text{sized}} t : A$ (including bounded course-of-values recursion `fixNat` and size-preserving `minus`) into standard, size-erased Lean 4 terms $\Gamma^\circ \to A^\circ$ and proves logical-relation coherence with the size-indexed semantics.
  - **Dual Lowering & Kernel `rfl` Reduction**: Proves semantic equivalence between `WellFounded.fix` lowering and spine-structural lowering (`divStructural_eq_divWF`, `mapRoseSized_erase_eq`), verifies kernel `rfl` reduction on concrete Euclidean division (`divErased_10_2_rfl`) and higher-order rose-tree traversals (`mapRose_rfl_benchmark`), and provides the general SCT mutual-block elaborator (`elaborateSCTBlock`, `elaborateSCTBlock_eq`) powered by `NishtAbel2024V5` Theorem 1 (`callRel_wf`).
- **[`Solutions/Milestones/Milestone1_3_LargeSizesAndModularity.lean`](Solutions/Milestones/Milestone1_3_LargeSizesAndModularity.lean) (Milestone 1.3)**:
  - **Parametric Large Sizes vs. `Classical.choice` (Laarakker, Otten & van den Berg, FSCD 2026)**: Formalizes relator-parametric inductive fixpoints (`LargeMu RF`, `fold_natural`, `fold_mkIn`) and stage-indexed parametric coinductive fixpoints (`StageNu F`, `ParamStageNu CF`, `unfold`). Proves both the negative interaction theorem (`choice_plus_prop_size_eq_synthesizes_size_inspector`, `unrestricted_choice_breaks_stage_coherence`) and the positive restriction theorem (`unsized_choice_commutes_with_erasure`, `v5_unsizedB_enforces_size_invariance`).
  - **Modular Size-Change Summarization & Anti-Blowup Theorem (Abel & Nisht 2024 vs. Chan, Li & Bowman 2023)**: Implements the multi-module library checker `checkLibraryB`, proves global soundness (`checkLibraryB_sound`) and compositional separate compilation (`checkLibraryB_append`), proves the cubic complexity separation (`modular_le_global_cost`, `modular_strict_saving_two_blocks`, `uniform_library_quadratic_speedup`), and verifies a 3-module cross-calling library by kernel `rfl` (`test_modular_library_accepted`).

### 4. Stage 1: `MiniLean-Sized` — Executable Bidirectional Type & Termination Checker (`0 sorry`)
- **[`Solutions/Stage1/MiniLeanSized.lean`](Solutions/Stage1/MiniLeanSized.lean) (Stage 1)**:
  - **Complete Executable Algorithm 2 Pipeline**: Implements executable boolean/option checkers for `Unsized` (`unsizedB`), polarized higher-kinded kind inference (`inferKindB`, `checkKindB`, `ekindingB`, `allPosFunctorsB`), signature encoding (`encodeTyB`, `encodeDeclB`, `encodeBlockB`), pattern & copattern spine inference (`inferPatB`, `inferSpineB`), bidirectional type comparison with $\beta$-reduction (`compareTyB2`), bidirectional term & clause inference (`inferTmB`, `checkTmB`, `checkClauseB`), and certified Size-Change Termination closure (`checkSCTB`, `checkBlockB`).
  - **End-to-End Soundness Theorem (`checkBlockB_sound`)**: Proves (`0 sorry`) that `checkBlockB fuel sig Ξ = true` implies `Algorithm2Accepts sig Ξ Ξannot`, declarative typing in System $F_\omega^{\text{cop,SCT}}$ (`BlockTy sig Ξannot`), and semantic strong normalization / productivity (`SemValid W Ξannot` via Theorem 15).
  - **Kernel-Checked (`rfl`) Regression Suite**: Accepts structural recursion (`test_P1_copy_accepted`), productive stream combinators (`test_P2_streams_accepted`), polymorphic list recursion (`test_P3_len_accepted`), mutual recursion (`test_P4_evenOdd_accepted`), higher-order polymorphic rose-tree traversal (`test_P5_mapRose_accepted`), and mixed-variance $\beta$-redex blocks (`test_P6_evalBush_accepted`), while statically rejecting Agda #3026 (`test_N1_agda3026_rejected`), unguarded streams (`test_N2_nonProductiveStream_rejected`), Agda #7178 negative fixpoints (`test_N3_agda7178_negFix_rejected`), and non-terminating mutual cycles (`test_N4_badMutual_rejected`).

### 5. Stage 2A & 2B: Lean 4 Compositional Termination & Computational Codata in `Type` (`0 sorry`)
- **[`Solutions/Stage2/Stage2A_CompositionalTermination.lean`](Solutions/Stage2/Stage2A_CompositionalTermination.lean) (Stage 2A)**:
  - **Verified `MiniLean-Sized` to Lean 4 Bridge (`checkBlockB_sctValid`, `checkBlockB_callRel_wf`, `checkBlockB_natCallRel_wf`, `elaborateNatSCTBlock`)**: Directly turns `checkBlockB fuel sig Ξ = true` (proved by `rfl`) into kernel-checked `SCTValid` and `WellFounded` certificates for both ordinal (`CallRel`) and `Nat`-indexed (`NatCallRel`) call relations.
  - **Dual Lowering Pipeline (`lowerNatBrecOn_eq_lowerNatWF`) & Kernel `rfl` Benchmarks**: Lowers size-bounded definitions via `Nat.brecOn` (preserving kernel `rfl` reduction on `divBrecOn_10_2_rfl`, `gcdBrecOn_1071_462_rfl`, `log2BrecOn_16_rfl`), structurally bounded higher-order rose-tree combinators (`filterTransformChildren`, `pruneMapRose_rfl_benchmark`), and general mutual SCT `WellFounded.fix` lowering (`evenOddSCT`, `evenSCT_succ`, `oddSCT_succ`).
  - **Custom Lean 4 Elaboration Macros (`sized_block_cert`, `sized_brec_def`)**: Runs `MiniLean-Sized` at elaboration time, formats inferred size-change graphs, and emits `_accepted`, `_sct`, and `_wf` certificates alongside `@[simp]` unfolding equations (`copyCert`, `streamsCert`, `mapRoseCert`, `sizedStepSum_10_2_rfl`).
- **[`Solutions/Stage2/Stage2B_ComputationalCodata.lean`](Solutions/Stage2/Stage2B_ComputationalCodata.lean) (Stage 2B)**:
  - **Full Computational Codata Suite in `Type u`**:
    - `CStream α` (infinite streams lowered from sized approximations `SizedStream α i` and inflationary `ProductiveStreamSpec α`, with definitional `rfl` destructor equations for `cons`, `corec`, `const`, `map`, `zipWith`, `interleave`, `evens`, `odds`),
    - `Colist α` (potentially terminating finite-or-infinite codata with `nil`, `cons`, `head?`, `tail`, `corec`, `map`, `countdown_5_take_10_rfl`),
    - `CoTree β α` (infinitely deep branching trees with `root`, `child`, `corec`, `map`, `binaryHeapTree_rfl_benchmark`),
    - `SP α β` (Ghani–Hancock–Pattinson mixed inductive-coinductive stream processors with `SPStep`, `SP.corec`, `head_run_corec_put`, `tail_run_corec_put`, `pairSumSP_nats_rfl`).
  - **Coinduction Proof Principles (`eq_of_bisim`, `bisim_iff_eq`)**: Proves bisimulation sound and complete for `CStream α`, `Colist α`, and `CoTree β α`, demonstrated on `CStream.interleave_evens_odds` and `blinkStream_tail_tail_eq`.
  - **Custom `corec_stream_def` Command Macro**: Elaborates productive corecursive stream definitions (`zerosStream`, `blinkStream`, `fibStream`) and synthesizes `@[simp]` `.head`/`.tail` unfolding equations with kernel `rfl` evaluation (`fibStream_take_8_rfl`).
