## Counterexample

Let $G = \forall Y{:}{*}.\; Y \to Y$ and take the empty signature $\Sigma = [\,]$ and the one-function block

$$
\Xi \;=\; \Xi_{\mathrm{annot}} \;=\; \bigl[\, f : G \to G \;=\; \{\, x \to N\;G\;N \,\} \,\bigr],
\qquad
N \;=\; \bigl(\lambda\{\, y \to \lambda\{\, Z\;x \to y\;Z\;x \,\}\,\} : G \to G\bigr)\; x .
$$

(In the Lean terms, $x$ is term variable `0`, $y$ is `1` and $Z$ is type variable `5`.) All three hypotheses of `theorem_15` hold, but `SemMutualBlockValid [] Ξannot` fails, because $\lambda\vec D$ for $f$ is not strongly normalizing.

## Idea

`Term.substTerms` removes a clause's bound names from the substitution but never renames the binder. `SemMutualBlockValid` asks for `SN (sig ++ Ξ) [] (.lamClauses decl.clauses)`. Full reduction (`RedStep.lamClauses`) reduces inside clause bodies, where the substituted terms are open. Contracting $N$ under the binder $x$ substitutes the free $x$ for $y$ underneath the inner binder $x$, which captures it.

## Hypotheses

* **Scope.** No term mentions a function, so `scopeBlockExtension [] Ξannot` holds.
* **Ambient validity.** `SemSigValidIn [] Ξannot` holds vacuously.
* **Postchecked Algorithm 2.** No type contains $\mu$ or $\nu$, so `EncodeType` is the identity on $G \to G$ and on the two local annotations. No constraints or flexible variables arise, and the solver and `applyFlex` act as the identity. There are no calls, so the empty graph family is `SCTValid`. The Lean file gives the full `InferSpine`/`CheckTerm` derivation (`body_infer`) and the declarative postcheck `ExprCheck` derivation (`body_check`). The only comparisons are $G \le G$ and $Z \le Z$; they produce no constraints (`G_cmp`, `G_sub`, `var5_sub`).

## Reduction

Under the clause binder $x$ (congruence `RedStep.lamClauses`, `ClausesRedStep.head`, `ClauseRedStep.body`):

$$
N \;\longrightarrow\; \lambda\{y \to \lambda\{Z\,x \to y\,Z\,x\}\}\; x
\;\longrightarrow\; \lambda\{Z\,x \to x\,Z\,x\} \;=:\; \delta .
$$

The first step is `WhdStep.ascr`. The second is `WhdStep.lamClause` with $\sigma = [(y, x)]$, and `Clause.substTerms` keeps $(y,x)$ under the inner binder $x$ because only $x$ is filtered. Doing this at both occurrences of $N$ gives

$$
N\;G\;N \;\longrightarrow^{4}\; \delta\;G\;\delta \;\longrightarrow\; \delta\;G\;\delta ,
$$

where the last step matches the spine $[G, \delta]$ against $[Z, x]$ with $\tau = [(Z,G)]$ and $\sigma = [(x,\delta)]$. So $\lambda\{x \to N\,G\,N\}$ reaches a term that reduces to itself. An accessible element has no reflexive step (`acc_irrefl`), so `SN` fails and the second conjunct of the conclusion is false.

## Scope

This refutes the formal V2 statement, not the thesis. The thesis treats substitution as capture-avoiding. A repair needs capture-avoiding substitution, or reduction restricted so that it never substitutes under a binder that captures. The axiom audit of `solution` is `[propext, Quot.sound]`.
