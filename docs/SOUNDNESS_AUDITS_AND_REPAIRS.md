# Soundness Audits, Counterexamples, and Metatheoretical Repairs (V1 → V5)

During the Lean 4 formalization of **Nisht & Abel (2024)** (*Type-Based Termination Checking in Agda*), we uncovered several subtle specification and soundness pitfalls in naive transcriptions of the paper's inference and typing rules, constructed machine-checked counterexamples (`0 sorry`, standard Lean axioms only) in [`Solutions/Audits/`](../Solutions/Audits/), and engineered a completely sound, capture-avoiding, ordinal-stabilized architecture in **`NishtAbel2024V5`** ([`Solutions/V5/DESIGN.md`](../Solutions/V5/DESIGN.md)).

---

## 1. Variable Capture Under Clause Binders (`V2CaptureCounterexample.lean`)

- **Counterexample**: [`Solutions/Audits/V2CaptureCounterexample.lean`](../Solutions/Audits/V2CaptureCounterexample.lean) (notes: [`docs/audits/v2-capture-counterexample.md`](audits/v2-capture-counterexample.md))
- **Issue**: When term substitution into copattern clauses (`Clause.substTerms`) filters out bound names without renaming binders, and operational reduction steps underneath clause abstractions (`λ{D⃗}`), a size-free well-typed block
  $$f : (\forall Y.\; Y \to Y) \to (\forall Y.\; Y \to Y) = \{ x \to N\;G\;N \}$$
  passes Algorithm 2 with no recursive calls or size constraints, yet reduces via binder capture to a self-looping term $\delta\;G\;\delta \longrightarrow \delta\;G\;\delta$.
- **V3–V5 Repair**:
  1. **Locally nameless representation** for both type variables (`Ty.var k` vs. `Ty.fvar X`) and size variables (`Size.bvar k n` vs. `Size.var i n`), where only locally closed types/sizes are ever substituted and binders open with fresh free names.
  2. **Weak closed reduction** on run-time terms (`Tm`), never reducing under `λ{D⃗}` until applied to a matching elimination spine.

---

## 2. Closure Ordinal of Higher-Order / Infinitely Branching Fixpoints ($\infty = \omega$ vs. $\Omega$)

- **Issue**: Interpreting the top size $\infty$ at $\omega$ (or order type $\omega^2$) is insufficient for higher-order or infinitely branching inductive/coinductive functors (e.g., `lim : (D → X) → X` or nested `Bush^a`), whose monotone/antitone approximations do not stabilize at $\omega$.
- **V3–V5 Repair** ([`Solutions/V5/Stable.lean`](../Solutions/V5/Stable.lean)):
  - Interprets $\infty + n$ as $\Omega + n$, where $\Omega = (\text{Order.succ }(\#\text{Tm})).\text{ord}$ is the initial ordinal of the successor cardinal of the term type `Tm`.
  - By cardinal limitation (`Cardinal.not_injective_limitation_set`), every monotone ($\mu$) or antitone ($\nu$) stage sequence over `Set Tm` stabilizes strictly below $\Omega$ (`muSet_ge_omega`, `nuSet_ge_omega`).

---

## 3. Bound Normalization $a^\uparrow$ and $\infty + n$ Arithmetic

- **Counterexample**: [`Solutions/Audits/Theorem14SolverAudit.lean`](../Solutions/Audits/Theorem14SolverAudit.lean)
- **Issue**: Treating $\infty + 1 = \infty$ syntactically while assuming $i < \infty$ for all size variables conflicts with ordinal arithmetic when a variable is bounded by $(\infty + n)^\uparrow = \infty + 1$ (allowing valuation $\Omega$). Furthermore, shifted global signatures can emit unsatisfiable constant constraints such as $\infty + 2 \le \infty$.
- **V5 Repair** ([`Solutions/V5/Size.lean`](../Solutions/V5/Size.lean), [`Solutions/V5/InfCheck.lean`](../Solutions/V5/InfCheck.lean)):
  - `ValidVal` requires only $\rho(i) < \llbracket a \rrbracket_\rho$ for $(i < a) \in \Psi$ (without a global $\rho(i) < \Omega$ side condition).
  - `SizeLt.var_inf` derives $i + n < \infty + m$ only when the declared bound $a$ of $i$ satisfies $a < \infty + 1$.
  - Constructors, projections, and fixpoint subtyping compare against normalized bounds $a^\uparrow$ (`(∞ + n)^↑ = ∞ + 1`), bridged at stages $\ge \Omega$ by ordinal stabilization.
  - Algorithm 2 verifies solver output via sound executable checkers `checkScope` and `checkCoherent` (`sizeLtB`, `sizeLeB`).

---

## 4. Higher-Order Type Application and Uncontracted $\beta$-Redexes (`HigherOrderInferenceAudit.lean`)

- **Counterexample**: [`Solutions/Audits/HigherOrderInferenceAudit.lean`](../Solutions/Audits/HigherOrderInferenceAudit.lean) (notes: [`docs/audits/higher-order-inference-audit.md`](audits/higher-order-inference-audit.md))
- **Issue**: Applying a polymorphic term of type $\forall (H : {}^\circ * \to *).\; H\;1$ to the type operator $\lambda Z{:}{*}.\; 1$ via naive structural substitution produces the uncontracted inner $\beta$-redex $(\lambda Z{:}{*}.\; 1)\;1$, which fails bidirectional kind checking when lambdas are checked rather than inferred.
- **V5 Repair** ([`Definitions/Def_NishtAbel2024V5_Syntax.lean`](../Definitions/Def_NishtAbel2024V5_Syntax.lean), [`Solutions/V5/Interp.lean`](../Solutions/V5/Interp.lean)):
  - Annotates type-operator applications `Ty.app F G ι` with the argument's simple kind `ι : SKind`, includes explicit $\beta$-conversion rules in `SubTy` and `Compare`, and interprets type variables in a simple-kind-indexed polymorphic semantic domain `PSem = (ι : SKind) → Sem ι` so substitution `interp_substTy` is unconditionally sound without dependent casts across variance subkinding.

---

## 5. Polarity Classification, Repeated $\mu$-Occurrences, and Mixed-Variance Functors (`Disproof1012OccurrencePolarity.lean`)

- **Counterexamples & Audits**:
  - [`Solutions/Audits/Disproof1012OccurrencePolarity.lean`](../Solutions/Audits/Disproof1012OccurrencePolarity.lean)
  - [`docs/audits/lemma45-audit.md`](audits/lemma45-audit.md)
- **Issue**:
  1. If a signature shares a single $\mu$-size variable across two negative domain positions (e.g., $\mu^i F \to \mu^i F \to C$), spine elimination leaves $i$ occurring both positively in $\Gamma$ and negatively in the residual type $C$, violating naive four-way mutual-exclusion statements of Lemma 5.
  2. Comparing $\mu^a S \le \mu^b S'$ across *different* functors $S \ne S'$ requires monotonicity of at least one functor; mixed-variance functors ($\pi = \circ$) only admit size-changing subtyping when the functors are mutually subtype-equivalent.
- **V5 Repair** ([`Solutions/V5/InfEncode.lean`](../Solutions/V5/InfEncode.lean), [`Solutions/V5/InfGraph.lean`](../Solutions/V5/InfGraph.lean), [`Solutions/V5/SubSound.lean`](../Solutions/V5/SubSound.lean)):
  - Disjoint namespaces for rigid size variables (`RigidName`, even `Nat`) and flexible size variables (`FlexName`, odd `Nat`).
  - `Encode` threads a fresh-name supply establishing `NamesDisjoint` and `paramPol` exclusivity (`lemma_3`, `lemma_4`, `lemma_5`).
  - Separates `mu_pos`/`nu_pos` (functor-changing subtyping when the larger functor is positive) from `mu_eqv`/`nu_eqv` (size-changing subtyping for mutually equivalent mixed-variance functors).

---

## 6. Ambient World Scoping, Forward References, and Well-Formed Signatures

- **Counterexamples**:
  - [`Solutions/Audits/Theorem4ForwardReference.lean`](../Solutions/Audits/Theorem4ForwardReference.lean) & [`Solutions/Audits/Theorem15FutureReference.lean`](../Solutions/Audits/Theorem15FutureReference.lean) ([`docs/audits/forward-reference-audit.md`](audits/forward-reference-audit.md))
  - [`Solutions/Audits/Theorem13IllFormedGlobal.lean`](../Solutions/Audits/Theorem13IllFormedGlobal.lean) ([`docs/audits/ill-formed-global-signature-audit.md`](audits/ill-formed-global-signature-audit.md))
  - [`Solutions/Audits/Disproof23DuplicateDecls.lean`](../Solutions/Audits/Disproof23DuplicateDecls.lean)
- **Issue**: Without a fixed ambient run-time world `W`, distinct declaration names (`Nodup`), and closed/well-formed global signatures (`SizeCtxWf d.sizeParams ∧ KindingC d.sizeParams [] d.ty .star`), an old declaration can reference a not-yet-defined function name (stuck in $\Sigma$, hence vacuously `SN` in $\Sigma$) that later forms a non-terminating cycle when $\Xi$ is appended, or an ill-formed global bound $[i < i]$ can block declarative call typing.
- **V5 Repair** ([`Solutions/V5/Main.lean`](../Solutions/V5/Main.lean), [`Solutions/V5/InfMain.lean`](../Solutions/V5/InfMain.lean)):
  - Parameterizes semantic validity `SemValid W` by a closed ambient run-time world `W` with `(W.map FunDecl.name).Nodup` and requires well-formed closed signatures (`SizeCtxWf` and `KindingC ... [] d.ty .star`) for all declarations in $\Sigma$ and $\Xi$.
