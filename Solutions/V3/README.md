# V3 (restricted calculus): plan and status

Local only; nothing is published until `theorem_15` is proved.

Statements: `Theorems/Thm_NishtAbel2024V3.lean`
- `theorem_15`: block soundness.
- `theorem_5`: programs are strongly normalizing.

Definitions: `Definitions/Def_NishtAbel2024V3_{Syntax,Semantics}.lean`. They reuse `InvGraph` and `SCTValid` from V2.

Design (restricted fragment of F_ω^{cop,SCT}):
- No type operators, polymorphism or kinds. Type variables are de Bruijn μ/ν recursion variables, and functors must be positive.
- Sizes are `∞ | i+n`. They appear only in types and contexts, never in runtime terms (Curry-style typing), so size substitution cannot capture.
- Term variables are named. The semantics substitutes only closed terms, and reduction is weak (never under λ), so term substitution cannot capture.
- Clause selection is first-match with blocking, so head reduction is deterministic.
- `∞ = Ω = (succ #Tm).ord`. μ/ν stage sequences stabilize below Ω because their sets are subsets of a countable type.
- Semantic types: intro-based sets (unit, ×, μ) and elimination-based sets (→, ν) over closed SN terms.

Proof modules (planned order):
1. `Basic`: spines, matching, head-step extension, neutrality of redexes.
2. `Closed`: free variables, closed substitution, composition, reduction preserves closedness.
3. `SNLemmas`: well-foundedness of argument-spine reduction.
4. `Cand`: candidates; every `interp` is a candidate.
5. `Monotone`: positivity gives monotonicity; μ/ν stage monotonicity; stabilization below Ω.
6. `SizeSem`: size soundness, size-substitution and independence lemmas for `interp`.
7. `TySubst`: `interp (A[T/k]) = interp A (η with ⟦T⟧ at k)`.
8. `SubTy`: semantic subtyping.
9. `Match`: soundness of pattern and spine matching.
10. `Fundamental`: expression and clause soundness under guarded block validity.
11. `SCT`: port of the V1 SCT chain plus Ramsey to well-foundedness of the ordinal call relation.
12. `Main`: `theorem_15`, then `theorem_5`.

## Status (2026-11-06)

Compiled with no `sorry`: `Basic`, `Closed`, `Reduct`, `Cand`, `Monotone`, `Stable` (stabilization below Ω via `Cardinal.not_injective_limitation_set`), `Interp`, `Wf`.

Next:
- `Match`: pattern soundness and subtyping soundness.
- `Spine`: semantic spines, plus alignment through a size-renaming invariant `T_clause = T_spine.substSize π`.
- `ClauseHead`: membership of a clause-headed term, by induction on (max clause length − spine length) with SN induction on the arguments.
- `Fundamental`, `SCT`, `Main`.

## Status update (2026-11-06, later)

Also compiled with no `sorry`:
- `Match`, `Spine` (alignment via size renaming), `ClauseHead`, `FundAux`.
- `Fundamental` (Theorem 3 for expressions and clauses under guarded block validity).
- The ported SCT chain in `SCT/` (V1 lemmas moved to the V2 graph definitions, universe-polymorphic) and `SCT/Ramsey.lean` (ultrafilter proof of infinite Ramsey).

`Main.lean` (written) holds `callRel_wf` (Theorem 1 on ordinal tuples), `theorem_15_proof` and `theorem_5_proof`.

Definition changes made during the proof:
- `PolIn` replaces the mutual `PosIn`/`NegIn`.
- `globalFun` and `localFun` require `SizeCtxWf g.sizeParams`.
- `theorem_15` assumes a closed world (`∀ d ∈ W, (Tm.lam d.clauses).Closed`).

## Done (2026-11-06)

`Solutions/V3/Final.lean` proves `NishtAbel2024V3.theorem_15` and `theorem_5`, with statements identical to `Theorems/Thm_NishtAbel2024V3.lean`. Axioms: `[propext, Classical.choice, Quot.sound]`. Checking `Final.lean` loads all of Mathlib (because of `SCT/Ramsey.lean`) and takes about 20 minutes on this machine. `Main.lean` alone takes about 10 seconds.

## Non-vacuity example (2026-11-06)

`Solutions/V3/Example.lean` compiles with no `sorry`. It defines `copy : ∀(i<∞). Nat^i → Nat^∞` (structural recursion through a constructor pattern) and `zeros : ∀(i<∞). Stream^i` (copatterns with a guarded self-call). It proves `BlockTy [] block` with an SCT-valid graph family, and from that `SemValid block block` via `theorem_15_proof`.
