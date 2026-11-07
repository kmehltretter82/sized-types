# V5 (full version) — working status

Goal (user, 2026-11-07, /goal): "continue on route 1 and make a full version of the proof. This one we
will upload to prove2me". V5 = full thesis calculus + inference, every step proved.

## Design decisions (see Definitions/Def_NishtAbel2024V5_*.lean and Solutions/V5/DESIGN.md)
- Sizes: `inf n` (∞+n), `var i n`, `bvar k n`, `meet a b`; `a.up` = bound normalization.
  ⟦∞+n⟧ = Ω+n, meets are min. ValidVal: ρ i < ⟦bound⟧ only (no global < Ω).
  SizeLt rules: inf_inf, var_var, bound (via a+n < b+1), var_inf (only if bound < ∞+1), meet_l/r,
  lt_meet, trans. SizeLe a b := SizeLt a (b+1).
- Kinds `star | arr π κ₁ κ₂`, Pol `mix|pos|neg|top`, SKind (simple kinds), SubKind.
  Sizes are not type-level (separate ∀(j<a)/∃(j<a) binders; thesis forbids sizes as operator params).
- Types: unit, prod, arr, var, fvar, lam ι F, app F G ι (argument's simple kind), mu/nu (list of
  functors binding rec var 0), allT κ B, exT κ B, allS a B, exS a B.
- Kinding Ψ Δ Δb m A κ with polarized contexts (π⁻¹Δ). μ/ν functor: polarity pos (under Δ) or mix
  (under ◦⁻¹Δ). Typing contexts are all-mix (`TyCtx.toK`).
- SubTy Ψ Δ A B κ on locally closed types, binders opened with fresh names; β rules; app with
  variance; lam; allT/exT with subkinding; allS/exS; mu_pos/nu_pos (different functors need positive
  larger functor) and mu_eqv/nu_eqv (equivalent functors, any variance).
- Semantics: `Sem : SKind → Type`, PSem = (ι : SKind) → Sem ι for type variables (substitution
  needs no kinding), Good/SemLe via KRel W κ ι (indexed by simple kind; no casts for subkinding).
- Terms Curry-style as V4; TypingEnv has `localOK` (call admissibility); `sctCallOK` from graphs.
- Constructors/projections use b < a.up (Ω handled by stabilization `muSet_ge_omega`).

## Completed & Verified (all build with 0 sorry, standard axioms only)
1. **Semantic core (`Solutions/V5/`)**:
   - `Basic`, `Closed`, `Reduct`, `Cand`, `Monotone`, `Stable`, `Kind`, `Size` (Theorem 2:
     `sizeLt_sound2`, `sizeLe_sound2`, `sizeWf_sound`), `Interp`, `KindSound` (`kinding_sound`),
     `Wf`, `KindWf`, `SubSound` (`subTy_sound`), `Match`, `Spine`, `ClauseHead`, `FundAux`,
     `Fundamental` (Theorem 3: `fundamental`), `Main` (Theorem 1 `callRel_wf`, Theorem 4
     `theorem_4_proof`, Lemma 2 `blocks_valid`, Theorem 5 `theorem_5_proof`), `FinalCore`.
2. **Lexicographic measures (Theorem 6)**:
   - `LexSCT`, `Theorem6` (`theorem_6_proof : LexBlockTy sig Ξ → BlockTy sig Ξ`).
3. **Inference algorithm & soundness (Theorems 7–15, Lemmas 3–5)**:
   - `InfCheck` (executable size-order checker soundness `sizeLtB_sound`, `sizeLeB_sound`,
     `checkScope_sound`, `checkCoherent_sound`),
   - `InfErase` (erased kinding bridge `kinding_of_erase`),
   - `InfCompare` (algorithmic comparison implies subtyping `compare_sound`),
   - `InfPat` (Theorems 8 & 9: `inferPat_sound`, `inferSpine_sound`, and their `φ`-substituted
     counterparts),
   - `InfAux` (encoding and flexible-substitution helpers),
   - `InfSound` (Theorem 13: `inference_sound` across `InferTm`, `CheckTm`, `CheckClauses`,
     `CheckClause`),
   - `InfEncode` (Theorem 7 `theorem_7`, `EncodedDecl.wf`, and Lemma 3 `lemma_3`),
   - `InfGraph` (Lemmas 4 & 5 `lemma_4`, `lemma_5`; Theorem 10 `theorem_10`; Theorems 11 & 12
     `theorems_11_and_12`),
   - `InfMain` (Theorem 14 `theorem_14`, `algorithm2_typing`, Theorem 15 `theorem_15_proof`).
4. **Worked example, statements file, final bundle, and design documentation**:
   - `Solutions/V5/Example.lean`: 5-function block (`copy`, `zeros`, `len`, `count`, `evalT`)
     exercising inductive/coinductive types, polymorphism, bounded size quantifiers, mixed-variance
     functors, and higher-kinded type operators (`block_typed`, `block_valid`).
   - `Theorems/Thm_NishtAbel2024V5.lean`: all 6 milestone bundles (`theorems_2_and_3`,
     `theorems_4_5_and_6`, `theorems_7_8_9_and_lemmas_3_4_5`, `theorems_10_11_and_12`,
     `theorems_13_and_14`, `theorem_15`).
   - `Solutions/V5/Final.lean`: proves all 6 bundles plus `example_block_valid`, printing only
     `[propext, Classical.choice, Quot.sound]`.
   - `Solutions/V5/DESIGN.md`: documents V5 architecture and all 8 departures/repairs from the
     thesis.
5. **Prove2Me Upload & Verification (`mission 2c50cc06-7b12-4799-9623-dfc673dd2704`) — COMPLETED**:
   - **Core V5 Definitions (`PUBLISHED`)**:
     - `NishtAbel2024V5_Syntax`: `98ac3e53-4d42-45ac-b677-604b6b56cc3b`
     - `NishtAbel2024V5_Semantics`: `47995e65-6240-4422-9bfa-392f75d48fc8`
     - `NishtAbel2024V5_Inference`: `4d9cec10-3734-41e4-83dd-49fbb649a45b`
   - **Support Layers (`PUBLISHED`)**:
     - `NishtAbel2024V5_SCT`: `c7bc85be-c75a-441e-998e-47ae6e3fd2f7`
     - `NishtAbel2024V5_SemBasic`: `306cb731-bae7-4f0e-858e-66749aedae19`
     - `NishtAbel2024V5_SemKinding`: `6dd968f3-2013-4e8f-b97f-11df16da2e5c`
     - `NishtAbel2024V5_SemSubSpine`: `3cb971e5-fa80-4821-8f25-7a63e5bd9ff5`
     - `NishtAbel2024V5_SemFundamental`: `0a1019e7-f577-4f03-86d2-fa1b3c823697`
     - `NishtAbel2024V5_InfCore`: `b6cb0ece-0876-461f-9c16-9bde5c83024b`
     - `NishtAbel2024V5_InfAlgorithm`: `1eefe7ee-d230-49de-9153-6bb7a4c021e9`
   - **Milestone & Main Theorems (`Proved` / `ACCEPTED` & linked to mission)**:
     - Milestone 1 (`7443f8e4-407d-4c83-9cbf-9b946db3e355`): `NishtAbel2024V5.theorems_2_and_3` (`2a0ec0ff-db1d-4786-b6e6-94aac6542d64`, accepted submission `ded24d07-95bc-4e61-afba-67695c0c10e0`)
     - Milestone 2 (`9c5ea14e-144d-471a-b228-94c3d449d829`): `NishtAbel2024V5.theorems_4_5_and_6` (`8b1722e3-40b1-45ab-977c-940db8e29cfe`, accepted submission `6d611823-fd9f-4123-9fdc-501a81556468`)
     - Milestone 3 (`1ade50e4-00f5-46fb-a17c-8b9db2c670c8`): `NishtAbel2024V5.theorems_7_8_9_and_lemmas_3_4_5` (`0c813074-bded-489e-ac86-5ae4b48033f9`, accepted submission `56f369b3-e34a-4442-8a37-115414cf1669`)
     - Milestone 4 (`f8cad769-fa34-4d38-80ad-ab47f2d1a69c`): `NishtAbel2024V5.theorems_10_11_and_12` (`eebcee21-ac49-4d2a-ae5c-691c4eabfc66`, accepted submission `098fe31b-5d9a-4856-a016-c603318b111e`)
     - Milestone 5 (`714877e0-000c-4184-a59d-c11f25741d73`): `NishtAbel2024V5.theorems_13_and_14` (`62fa83a5-4d72-42f5-9c6f-93550d5e0e52`, accepted submission `f93dac9d-3ca0-48d5-8624-5083fafa77fd`)
     - Main Goal (`main_statement`): `NishtAbel2024V5.theorem_15` (`f4053932-f55c-468b-b34d-263104461ce2`, accepted submission `ae929c20-6234-4b3f-9cf7-abdcaa32308b`)
