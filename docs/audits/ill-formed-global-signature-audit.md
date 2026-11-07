Take an ambient global function `g` whose size-parameter context and result type are

$$
\Psi_g=[i:<i],\qquad A_g=1.
$$

This deliberately ill-formed global declaration is permitted by the formal statement's unrestricted global-signature variable. Use unit source and encoded types, an empty pattern spine, and empty local size contexts and constraints. The checked result is the negation of the complete bundled proposition:

$$
\neg(P_{13}\land P_{14}\land P_{\mathrm{cor}}).
$$

The contradiction comes from the first conjunct. Call inference introduces a fresh flexible size argument for `g` without checking the global declaration's size context. On the empty constraints, the actual solver chooses infinity, and the resulting substitution satisfies the stated coherence premise. The call is global, so the local recursive-call conformance premise holds.

The elaborated call cannot have the required expression typing. The declarative global-call rule requires `SizeSubstWf`, whose first argument obligation would place infinity strictly below the unbound variable in the self-referential size bound. Induction on the original `SizeLt` rules rules this out. Inversion also excludes a local-call derivation, since the local and global function names differ. The standalone proof imports only the original Inference definition and has no theorem imports.

A separate checked local result shows that the same example also meets the empty local size-context well-formedness and unit signature-hygiene premises of the bundled corollary and refutes that conjunct. The submitted proof refutes the entire conjunction through its first conjunct; it does not establish that the middle Theorem 14 conjunct is false. A source formulation that assumes a well-formed ambient signature is outside the scope of this counterexample.
