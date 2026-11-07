# Nisht–Abel V3: the restricted calculus and its soundness theorem

Definitions: `Definitions/Def_NishtAbel2024V3_{Syntax,Semantics}.lean`.
Statements: `Theorems/Thm_NishtAbel2024V3.lean`.
Proofs: `Solutions/V3/*.lean`.

## What the main theorem says

`theorem_15` (block soundness). Let `W` be a run-time world with distinct names and closed
clause bodies, containing `Σ` and `Ξ`. Suppose `Ξ` is typed against `Σ` with an invocation-graph
family `G` satisfying the size-change criterion (`SCTValid G`), and `Σ` is semantically valid in
`W`. Then every function of `Ξ`, at every valid instance of its size parameters, belongs to the
interpretation of its type. Members of every interpreted type are closed strongly normalizing
terms. For a function type, this means every application to good arguments terminates in a
member of the result type.

`theorem_5` (programs). The main term of a typed program (blocks typed in order, distinct names)
is strongly normalizing.

## What is kept from the thesis

- Sized inductive (`μ^a S`) and coinductive (`ν^a R`) types, with `∞` and `i + n` sizes, and
  subtyping by sizes (μ covariant, ν contravariant).
- Copattern matching: patterns `x | () | (p, p) | c p`, projections `.d`, nested clauses
  `λ{D⃗}`, and mutual blocks of functions `f : ∀Ψ. A = D⃗` with bounded size parameters.
- Size-change termination: invocation graphs, their composition closure, and the
  Lee–Jones–Ben-Amram criterion. These definitions are reused unchanged from V2
  (`InvGraph`, `InvGraphFamily`, `SCTValid`).
- The semantic method: reducibility candidates, ordinal-indexed stages for μ and ν, guarded
  validity of block calls, and well-founded induction over the semantic call relation
  (Theorem 1 via Ramsey).

## What is restricted or changed (differences from the thesis)

1. **No type operators, no type polymorphism, no kinds.** Type variables are de Bruijn indices
   and occur only as recursion variables of μ/ν. Every functor must be positive in its recursion
   variable (`PolIn`), as in Agda. Mixed-variance functors (`◦* → *`) are excluded.
2. **Sizes**: `∞ | i + n`. The formal minimum `⊓` and `∞ + n` are not part of the language.
   `μ^∞`/`ν^∞` are fixed points, so constructors and projections may use size `∞` at size `∞`
   (`SizeBelow`).
3. **Curry-style typing.** Run-time terms carry no sizes. Sized constructors, sized projections
   and size arguments of calls are chosen in typing derivations, and copattern and constructor
   patterns bind size variables directly. The thesis's encoding through `∃`/`∀` size types and
   packs is replaced by this equivalent direct form.
4. **Weak reduction on closed terms.** Reduction never goes under `λ{D⃗}`. Strong normalization
   is about closed terms, which are the only terms the semantics substitutes.
5. **First-match clause selection with blocking.** A clause fires when it matches and every
   earlier clause definitely mismatches. An undecided earlier clause blocks. Head reduction is
   deterministic. The thesis lets any matching clause fire.
6. **Inference (Algorithms 1–2) is not part of V3.** The V2 "postchecked" Algorithm 2 reduced
   to declarative typing anyway. V3's theorem is about the declarative SCT-typed system that
   Algorithm 2 targets.

## Why the V2 defects cannot recur

- **Capture (accepted V2 disproof):** term substitution only ever substitutes closed values
  (`SemCtx` requires closed values). Reduction is weak, so no open term is substituted under a
  binder. Types contain no size binders, so size substitution cannot capture, and type
  substitution only substitutes closed types.
- **Higher-kinded interpretation:** there are no type operators.
- **`∞ = ω`:** `∞` is `Ω = (succ #Tm).ord`. Every μ/ν stage sequence is monotone (or antitone)
  in a countable set, so it stabilizes below `Ω`
  (`Stable.lean`, via Mathlib's `Cardinal.not_injective_limitation_set`).
- **Ill-formed callee size contexts (V1 Theorem 13 disproof pattern):** calls require
  `SizeCtxWf g.sizeParams`.
- **Forward references in old signatures (V1 Theorem 4 disproof):** validity of `Σ` is assumed
  in the same world `W` in which `Ξ` is proved valid.

## Proof structure

| File | Content |
|---|---|
| `Basic` | spines, matching, determinism and extension of head steps, neutral terms |
| `Closed`, `Reduct` | closed substitution and its composition, closedness of reducts |
| `Cand` | candidates; every well-formed type denotes one |
| `Monotone` | positivity gives monotonicity; μ/ν stages are monotone in the ordinal |
| `Stable` | `Ω` is a limit, and stages stabilize below `Ω` |
| `Interp` | size soundness (Theorem 2), size and type substitution lemmas |
| `Wf` | well-formedness of unfoldings, weakening, size and type substitution commutation |
| `Match` | subtyping soundness, pattern-matching soundness |
| `Spine` | semantic spines, alignment of copattern typing with semantic spines up to size renaming |
| `ClauseHead` | clause-headed terms applied to any valid spine are in the right set |
| `Fundamental` | Theorem 3 for expressions and clauses under guarded block validity |
| `SCT/*` | V1's size-change chain moved to the V2 graph definitions; Ramsey's theorem |
| `Main` | Theorem 1 on ordinal tuples; `theorem_15_proof`; `theorem_5_proof` |
