# Nisht–Abel V4: V3 plus type polymorphism and bounded size quantifiers

Definitions: `Definitions/Def_NishtAbel2024V4_{Syntax,Semantics}.lean`.
Statements: `Theorems/Thm_NishtAbel2024V4.lean`. They are identical in form to V3's.
Proofs: `Solutions/V4/*.lean`. `Final.lean` states `theorem_15` and `theorem_5` exactly.
The V3 size-change chain and Ramsey proof (`Solutions/V3/SCT/`) are reused unchanged.

## Status (2026-11-06)

Everything is proved with no `sorry`, `admit` or `axiom`.
`lake build Solutions.V4.Final` prints:

    'NishtAbel2024V4.theorem_15' depends on axioms: [propext, Classical.choice, Quot.sound]
    'NishtAbel2024V4.theorem_5' depends on axioms: [propext, Classical.choice, Quot.sound]

`Example.lean` checks a four-function block against `BlockTy` and derives `SemValid block block`.
The block is:
- `copy`;
- `zeros`;
- a polymorphic `len : ∀(i<∞). ∀X. List^i X → Nat^∞`;
- `count : ∀(i<∞). ∀(j<i). Nat^j → Nat^∞`, which uses a size instantiation copattern.

Nothing is published.

## What V4 adds to V3

Types:

    A ::= () | A × A | A → A | X (bound) | X (free) | μ^a S | ν^a R
        | ∀X. A | ∃X. A | ∀(j < a). A | ∃(j < a). A

Binding is **locally nameless** for both type variables and sizes:
- Bound type variables are de Bruijn indices (`Ty.var k`). μ, ν, ∀X and ∃X each bind one.
- Free type variables are names (`Ty.fvar X`). The type context `Θ` lists them.
- Bound sizes are `Size.bvar k n` (index plus offset). ∀(j<a) and ∃(j<a) each bind one.
- Free sizes are `Size.var i n`. The size context `Ψ` lists them with their bounds.

Instantiation always substitutes locally closed things:
- `Ty.substTy` substitutes a closed type for a bound type variable.
- `Ty.openSz` substitutes a free size for a bound size.
- `Ty.substFTy` substitutes closed types for free type variables.
- `Ty.substSize` substitutes free sizes for free sizes.

None of these can capture. This is the V2 defect class, and V4 excludes it by construction.

Terms gain `pack t` (an introduction form) and the instantiation elimination `r ·`.

Typing:
- Expressions: `instT` (`r : ∀X.B` gives `r · : B[T/X]` for any well-formed closed `T`); `instS` (`r : ∀(j<a).B` gives `r · : B[b/j]` for `b < a`); `packT`; `packS`.
- Patterns: `pack p` against `∃X.B` binds a fresh free type variable, and against `∃(j<a).B` binds a fresh size variable `j < a`.
- Copatterns: `·` against `∀X.B` binds a fresh free type variable, and against `∀(j<a).B` binds a fresh size variable `j < a`.

Semantics:
- `∀X.B` is the set of closed SN terms `t` with `t · ∈ ⟦B⟧(𝒳)` for **every reducibility candidate** `𝒳`. `∃X.B` contains the terms that reduce only to packs of members of `⟦B⟧(𝒳)` for some candidate `𝒳`.
- `∀(j<a).B` quantifies over all ordinals `β < ⟦a⟧`. `∃(j<a).B` is the matching pack set.
- `interp W ρ θ A ζ η` takes four valuations: `ρ` for free sizes, `θ` for free type variables, `ζ` for bound sizes and `η` for bound type variables.

## The one definition change found during the proof

`globalFun` and `localFun` now require `TyWf g.sizeParams [] 0 0 g.ty`: a referenced function's type must have no free type variables, as in the thesis.

Without this premise the V4 statement would be false. The argument below is by hand and not checked in Lean. Take a signature function `g : X → ()` with the self-looping clause `g x = g x`, and `X` free:
- `SemValid` evaluates `g`'s type at the empty type environment, where `⟦X⟧ = ∅`.
- So the condition on `g` is vacuous, and `g` is valid.
- A block function `f : ∀X. X → ()` with clause `f · x = g x` type-checks, because it uses `g` under the bound `X`.
- But `f · () = g () = g () = …` loops, so `f` is not valid.

Block functions already had closed types, because `DeclTy` requires `TyWf d.sizeParams [] 0 0 d.ty`.

## How the proof handles the new features

- **Candidates for type variables.** `TEnvOK W Θ θ` says every free type variable denotes a candidate. `interp_cand` shows every well-formed type denotes a candidate under such `θ` and `η`. ∀X uses `instSet_cand`, which is universe-polymorphic. ∃X and ∃(j<a) are intro sets.
- **Substitution lemmas** (`Interp.lean`):
  - `interp_substTy`, `interp_openSz`, `interp_substSize` and `interp_substFTy` turn syntactic substitution into an update of the matching valuation.
  - `interp_agree` shows `interp` depends only on the variables a type is well-formed in.
- **Spines** (`Spine.lean`). Semantic spines have four steps:
  - argument;
  - projection, which picks `β` below the bound and names it by a fresh size;
  - type instantiation, which picks a candidate and names it by a fresh type variable;
  - size instantiation.

  Copattern typing is aligned with semantic spines by a `Renaming` invariant with a size renaming `πS` and a type-variable renaming `πT` (`spine_align`).
- **Clause heads** (`ClauseHead.lean`). A new difficulty arises at a position whose type is a free type variable, interpreted as an arbitrary candidate. A stuck clause-headed term there must be *neutral*. That fails if some longer clause could still fire after more eliminations. `spine_shape` proves from clause typing that a longer clause with no mismatch so far forces an elimination type (→, ν, ∀X, ∀(j<a)) at the end of the spine. At every other type, `selectClause_append_none` shows a stuck term stays stuck under extension, so it is neutral. `clause_head` takes this as its `hshape` hypothesis.
- **Fundamental lemma.** `CtxOK` carries `θ` with `TEnvOK`. The new cases:
  - `instT` instantiates at the candidate `⟦T⟧`.
  - `instS` instantiates at `⟦b⟧ < ⟦a⟧`.
  - `packT` and `packS` show pack membership through `steps_pack_inv`.

## What is still excluded (compared with the thesis)

All of V3's other restrictions remain. They are listed in `Solutions/V3/DESIGN.md`:
- positive functors only;
- sizes `∞ | i+n`;
- Curry-style sizes;
- weak reduction on closed terms;
- first-match clauses;
- no inference algorithm.

Also excluded:
- **Type operators and kinds** (`F_ω`): type variables have kind `*` only.
- **Mixed-variance functors.**
- Algorithms 1–2 (inference).

## Proof structure

| File | Content |
|---|---|
| `Basic`, `Closed`, `Reduct` | as V3, plus `pack` and `·` |
| `Cand` | candidates; `instSet_cand` for ∀X and ∀(j<a) |
| `Monotone`, `Stable` | as V3, plus monotonicity for the quantifier sets |
| `Interp` | size soundness; size, type and free-type substitution; agreement |
| `Wf` | weakening, opening, commutation of all four substitutions, freshness |
| `Match` | `TEnvOK`, `SemCtx`, fresh openings, pattern soundness with packs |
| `Spine` | semantic spines with four steps, `Renaming`, `spine_align` |
| `ClauseHead` | `spine_shape`, neutrality of stuck heads, `clause_head` |
| `FundAux`, `Fundamental` | Theorem 3 with type environments |
| `Main`, `Final` | Theorem 1 (reused), `theorem_15`, `theorem_5` |
| `Example` | `copy`, `zeros`, `len` (∀X), `count` (∀(j<i)) |
