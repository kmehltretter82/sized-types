# Higher-order type application and kind preservation

The original `InferTerm.appTy` rule can return a type that is not kindable, even when the term context is well formed, its polymorphic type is genuinely encoded from a well-kinded unannotated source type, and the type argument is itself well-kinded and genuinely encoded. The result is caused by an uncontracted type-level β-redex introduced inside substitution. This is a concrete obstruction to a general inferred-output kinding lemma for the original definitions under those premises.

The example in `Solutions/HigherOrderInferenceAudit.lean` uses the empty kinding context and a term variable with type

```
k = ◦* → *
T = ∀ₖ (λH : k. H 1)
G = λZ : *. 1
```

Both `T` and `G` are unannotated and kinded in the original unannotated `Fω` relation; both also satisfy the original sized `KindCheck`. `T` is encoded by the original signature encoder at target polarity `−` and current polarity `+`, and `G` is encoded by the actual mixed-polarity type-argument encoder. No size variables are generated. The singleton term context `x : T` is proved `TermCtxWf`.

The original `InferTerm.appTy` applied to `x G` produces

```
(λZ : *. 1) 1
```

rather than `1`. The reason is exact: `body.normApp G` substitutes `G` for `H` in the body `H 1`, but `substTyVar` reconstructs the inner application without normalizing it. The result cannot be checked at `*`: checking an application requires inferring its head, while the original `KindInfer` has no lambda constructor. The original declarative `ExprInfer.appTy` rule also produces this same unkindable type in this instance. Contracting the inner redex separately yields `1`, which is kindable.

The module checks a structural beta-normality predicate for the two inputs and proves that the produced result is not beta-normal. Thus requiring beta-normal inputs alone does not make the present operation closed under type application. The file's `wellformed_encoded_appTy_failure` conjunction records actual encoding, source kinding, a well-formed term context, actual inference, and failure of output kinding. It uses `[propext, Quot.sound]`; all assertions compile without placeholders on VM B. The exact four-file project-local closure is `higher-order-inference-audit.sha256`, verified against VM B. Source SHA-256: `777f13336ecb9c2f00102e0d75b7877c9adc3eb5b1636bdd213df0c4ffd46830`.

This is distinct from `HigherOrderCommonAudit.lean`, which is a V2 shared-refined-binder counterexample involving a bounded quantifier and explicitly does not establish unannotated-source reachability. The present witness uses the original platform definitions and no bounded quantifier, and proves actual source-type encoding. It is not an exact disproof of a named platform theorem or a complete Algorithm 2 program. The platform's source `Fω` expression-typing judgment is not established by this file; the file proves the source type and type argument are kinded and shows actual original inference and declarative sized inference.

## Source and repair implications

Kanstantsin Nisht's [thesis](https://knisht.github.io/agda/msc.pdf), §4.2.2 p. 24, describes `F @ G` as normalizing application and says the types of interest are in normal form. Section 6.3.1 p. 49 uses `F @ᵢ G'` in the inference rule for type application. Section 6.1 pp. 41–42 excludes higher-order **size** quantification, while the grammar and Appendix A pp. I–II retain higher-kinded type operators. These passages support repairing type-level application while preserving higher-order type arguments; they do not establish this particular implementation's correctness or make the Lean counterexample a disproof of the thesis.

A narrowly scoped candidate repair is a kind-directed hereditary type substitution/normalizing application that recursively contracts redexes exposed by substitution, with capture-avoiding binding. A total implementation must carry enough kind and well-kindedness information to justify termination and kind preservation; simply replacing every reconstructed application with an unrestricted recursive `normApp` is not a proved terminating definition. A de Bruijn representation or a proven alpha-renaming/fresh-name discipline is also needed: the existing `safeNormApp` rejects some captures but is partial and does not implement hereditary normalization. This repair should preserve arbitrary higher-kinded operators and all existing fixpoint/branch constructors rather than silently restricting inputs to first order or positive-only functors.

Before integrating the candidate, prove at least: (1) source and sized type kind preservation and beta-normality of its result; (2) alpha/capture correctness, including size/type namespace interactions and unchanged size-bound behavior; (3) agreement with existing `normApp` where substitution creates no beta-redex and no capture; (4) compatibility with encoding and with application in pattern, spine, subtyping, inference and declarative typing rules; and (5) how comparison origins and constraint-direction proofs are transported across the repaired normal forms. None of those general repair claims is proved by the example.
