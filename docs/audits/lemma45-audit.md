# Lemmas 4–5: original formalization audit

The sixth conjunct, Lemma 5, of frozen theorem
`60c982ad-4712-4445-8689-70bbff93fcd9` is false under its stated
`SignatureFixpointHygiene` premise. The no-placeholder proof
`Solutions/Lemma45DuplicateMuAudit.lean` establishes its exact negation as
`original_lemma5_false`. A balanced-parenthesis comparison verified that the
negated proposition is identical to the frozen sixth conjunct modulo
whitespace. The checked file's SHA-256 is
`d0ad811cc6cb8e0004604e32a274c8565425037d29511cad76c6b430cd4ff5a7`.
On the original-definition VM, Lean `-DautoImplicit=false` exited 0 and
`#print axioms` reported `[propext, Quot.sound]`, with no `sorryAx`.

Take `Ψ₁ = [1 : mixed < ∞]`, `M = μ¹⟨⟩`, and
`A₀ = M → (M → 1)`. Eliminate the first argument with a variable pattern,
then stop. The exact inference rules yield `Γ = [(0, M)]`, `Ψ₂ = []`, and
`A'' = M → 1`. The existing negative hygiene requires an appropriate
occurrence *witness* and absence of the opposing `ν` occurrence; the example
satisfies it. Both syntactic `μ¹` occurrences in the initial type are in
negative positions, so requiring every occurrence to have the intended
polarity would not eliminate this example. Empty constructor
branch lists make its additional branch-hygiene obligations vacuous.

At the end, the `μ¹` occurrence in `Γ` is positive, while the one in `A''`
is negative. Thus both the first and second cases in `SpineRigidVarClass`
hold, violating their explicit mutual-exclusion clauses. The counterexample
uses no overloaded variable names; adding uniqueness of context names would
not repair it. Workspace independently checked in
`Solutions/Lemma5DuplicateUnreachable.lean` that no original `EncodeType`
derivation can produce this initial type: encoding's generated-size
disjointness excludes this reuse. Restricting to encoded outputs is a
possible direction to investigate, not a proved repair. Other restrictions
on sharing inductive sizes between domains may also matter. No publication or
replacement premise is proposed here.

The source is Kanstantsin Nisht, *Type-Based Termination Checking in Agda*,
§6.2, Lemma 5, printed pp. 46–47. The thesis describes an intended
size-annotated type and exclusivity of the four classes. The frozen Lean
premise uses existential `NegFixpointPolClean`; no claim is made here that
the thesis's intended source types admit this particular witness. A faithful
replacement requires a separate source interpretation and proof; changing
the premise would not prove the original statement.

The fifth conjunct, Lemma 4, is also false under its stated
`PositiveFixpointHygiene` premise. The independent file
`Solutions/Lemma45BoundCollisionAudit.lean` proves the exact negation as
`original_lemma4_false`. A balanced-parenthesis comparison found the
negated proposition identical to the frozen fifth conjunct modulo
whitespace. The checked file's SHA-256 is
`501d85e63a9d6a88e33f5a028558478b2f41dbbc88ecdbaa6b4caab9783682c8`.
The VM check exited 0 under `-DautoImplicit=false`; its axiom audit is
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

The pattern matches a pair. The left component's type locally binds size
name `1` in a universal quantifier and contains `ν¹` in a negative
position; the right component matches a constructor and generates a fresh
rigid index also named `1`. Freshness is checked against the ambient size
context and the constructor's local material, and the pair rule does not
exclude a right-generated name from the left type's collected names. The
resulting term context has a negative `ν¹` occurrence from the left type and
a positive `μ¹` occurrence from the right. The formal occurrence relation
and collector treat the bound identifier as that same numeric name. Both
classification alternatives are witnessed, so their explicit exclusivity
fails. The file checks `PositiveFixpointHygiene` and the entire `InferPat`
derivation, rather than assuming either one.

This counterexample exploits the gap between numeric identifiers in the
formal judgments and the thesis's globally fresh size-variable convention.
It establishes failure of the exact Lean implication; a source-level
alpha-equivalence or globally fresh-name repair would require separate
definitions and proof. It is independent of the duplicated-`μ` Lemma 5
counterexample above.

Subsequent repair audit: the stronger local theorem in
`Solutions/CorrectedLemma4TopWfReachableFalse.lean` rules out a proposed
Lemma 4 repair even with actual source pattern-type encoding, source
kinding/pattern typing, global name reservation, the existing hygiene,
well-formed generated sizes and declarations, context consistency, and
unique generated names. The generated index survives only under an operator
with unused (`top`) argument variance. The original raw-name collector
counts it, but the exact positive/negative occurrence tests do not put it
in either nonempty class. The checked theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`. See `corrected-lemma4-top-wf-audit.md`
for the concrete construction and `topwf-independent-review.md` for the
independent review. Its scope is the stated pattern repair implication;
full signature/spine and Algorithm 2 reachability remain unproved.
