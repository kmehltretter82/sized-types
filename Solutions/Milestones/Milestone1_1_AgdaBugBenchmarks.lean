import Solutions.V5.Final

/-!
# Milestone 1.1: Mechanizing Both Classes of Agda Soundness Bugs (Negative & Positive Tests)

This module formalizes the two distinct classes of historical sized-type soundness bugs identified
in `plan.md` (§3, Milestone 1.1) and proves both:
1. **Negative Benchmarks (Contradiction & Non-Termination Derivations)**:
   - **Class A (Agda Issue #3026 / #6002 — Non-well-founded top size `∞ < ∞`)**:
     How `∞ < ∞` yields `False` via well-founded induction (`agda3026_wf_contradiction`) or a
     single-constructor sized inductive type (`agda3026_bad_inductive_contradiction`), and yields
     a 1-step operational loop violating `SN` in `NishtAbel2024V5` (`agda3026_loop_not_sn`).
   - **Class B (Agda Issue #7178 & Nisht 2024 — Mixed Inductive/Coinductive Positivity &
     Size Variance Bugs without `∞ < ∞`)**:
     How at purely finite sizes `0 < 1` (with *no* use of `∞`):
     (a) covariant size subtyping on a stage-indexed negative recursive functor `S(X) = X → ⊥`
         (`MuNeg`, modeling `NishtAbel2024V5`'s `muSet` stage iteration) derives `False`
         (`agda7178_finite_size_nonpos_subtyping_contradiction`), and
     (b) mutual inductive-coinductive definitions (`D7178` and `R7178`) that violate coinductive
         size contravariance / polarity separation (`R 0 → R 1`) derive `False` from the vacuous
         0-depth coinductive base case `r₀ : R 0`
         (`agda7178_mutual_ind_coind_variance_contradiction`).
2. **Positive Blocking Theorems in `NishtAbel2024V5`**:
   - **Blocking Class A**:
     - `v5_not_sizeLt_inf_self`: `¬ SizeLt Ψ (.inf n) (.inf n)` under any valid valuation `ρ`
       (and unconditionally in `Ψ = []`: `v5_not_sizeLt_infty_infty`).
     - `v5_sizeLtB_inf_self_false`: Executable checker `sizeLtB` rejects `∞ + n < ∞ + n`.
     - `v5_rejects_agda3026_self_instantiation`: Instantiating `f : ∀(i < ∞). A` at `∞` fails
       `SizeSubstWf` under any valid valuation.
   - **Blocking Class B**:
     - `v5_rejects_negative_functor_at_pos_polarity`: The negative functor `X → 1` is provably
       rejected at positive polarity `+`
       (`¬ Kinding Ψ Δ [(.pos, .star)] m (.arr (.var 0) .unit) .star`), statically blocking
       `SubTy.mu_pos` and `SubTy.nu_pos`.
     - `v5_encode_forbids_shared_mu_nu_size`: Polarized signature encoding (`Encode`) guarantees
       via `lemma_3` that no generated size parameter `i ∈ Ψ.dom` can ever index both an inductive
       `μ` and a coinductive `ν`.
   - **Accepting Valid Mixed Programs**:
     - `v5_accepts_valid_mixed_block`: Valid mutual blocks combining inductive recursion,
       coinductive copattern corecursion, polymorphism, and mixed-variance functors are accepted
       and strongly normalizing.
-/

namespace SizedTypes.Milestone1_1

open NishtAbel2024V5

/-! ## Part 1: Class A — Non-Well-Founded Top Size (`∞ < ∞`, Agda Issue #3026) -/

/-- **Class A Negative Benchmark 1 (Well-Founded Induction with `∞ < ∞` yields `False`)**:
In any size structure `(Sz, Lt, infty)` where `Lt infty infty` holds, the sized well-founded
induction principle immediately derives `False`. -/
theorem agda3026_wf_contradiction
    {Sz : Type} (Lt : Sz → Sz → Prop) (infty : Sz)
    (h_inf_lt_inf : Lt infty infty)
    (wf_ind : ∀ (P : Sz → Prop), (∀ i, (∀ j, Lt j i → P j) → P i) → ∀ i, P i) :
    False := by
  have h_not_lt_self : ∀ i, Lt i i → False :=
    wf_ind (fun i => Lt i i → False) (fun _ ih hii => ih _ hii hii)
  exact h_not_lt_self infty h_inf_lt_inf

/-- A sized inductive family with a single size-guarded constructor `mk : (∀ j < i, Bad3026 j) → Bad3026 i`,
modeling Agda Issue #3026's sized empty type `data Empty (i : Size) : Set where mk : (∀ j < i → Empty j) → Empty i`. -/
inductive Bad3026 {Sz : Type} (Lt : Sz → Sz → Prop) : Sz → Prop where
  | mk (i : Sz) (step : ∀ j, Lt j i → Bad3026 Lt j) : Bad3026 Lt i

/-- **Class A Negative Benchmark 2 (Sized Empty Inductive Type with `∞ < ∞` yields `False`)**:
If `Lt infty infty` holds, any family of inhabitants `∀ i, Bad3026 Lt i` (such as the corecursive
self-application `bad i = mk i (fun j _ => bad j)` instantiated at `infty`) yields `False` by
structural induction on `Bad3026`. -/
theorem agda3026_bad_inductive_contradiction
    {Sz : Type} {Lt : Sz → Sz → Prop} {infty : Sz}
    (h_inf_lt_inf : Lt infty infty) :
    (∀ i, Bad3026 Lt i) → False := by
  intro hall
  have h_elim : ∀ i, Bad3026 Lt i → (Lt i i → False) := by
    intro i hbad
    induction hbad with
    | mk i _ ih =>
      intro hii
      exact ih i hii hii
  exact h_elim infty (hall infty) h_inf_lt_inf

/-- In `NishtAbel2024V5`, the unguarded self-call declaration `f · = f` (`loop3026Decl`) steps to
itself in one operational step and is therefore not strongly normalizing (`¬ SN`). -/
def loop3026Decl : FunDecl :=
  { name := 0
    sizeParams := [(0, .inf 0)]
    ty := .unit
    clauses := [⟨[], .fn 0⟩] }

theorem agda3026_loop_steps_to_self :
    Step [loop3026Decl] (.fn 0) (.fn 0) :=
  Step.head rfl

theorem agda3026_loop_not_sn :
    ¬ SN [loop3026Decl] (.fn 0) := by
  intro hsn
  have hirrefl : ∀ t, SN [loop3026Decl] t → t = .fn 0 → False := by
    intro t hacc
    induction hacc with
    | intro x _ ih =>
      intro hx
      subst hx
      exact ih (.fn 0) agda3026_loop_steps_to_self rfl
  exact hirrefl (.fn 0) hsn rfl

/-- **Class A Positive Blocking Theorem 1 (`NishtAbel2024V5` refutes `∞ + n < ∞ + n`)**:
In `NishtAbel2024V5`, in any size context `Ψ` with a valid valuation `ρ` (`ValidVal Ψ ρ`),
`SizeLt Ψ (.inf n) (.inf n)` is provably impossible. -/
theorem v5_not_sizeLt_inf_self {Ψ : SizeCtx} {ρ : SizeVal} (hρ : ValidVal Ψ ρ) (n : Nat) :
    ¬ SizeLt Ψ (.inf n) (.inf n) := by
  intro hlt
  exact lt_irrefl _ (sizeLt_sound hρ hlt)

/-- The empty size context has a trivial valid valuation. -/
theorem validVal_nil (ρ : SizeVal) : ValidVal [] ρ := by
  intro _ h
  cases h

/-- In the empty context, `⊢ ∞ + n < ∞ + n` (and in particular `⊢ ∞ < ∞`) is impossible. -/
theorem v5_not_sizeLt_infty_infty :
    ¬ SizeLt [] Size.infty Size.infty :=
  v5_not_sizeLt_inf_self (validVal_nil (fun _ => 0)) 0

/-- **Class A Positive Blocking Theorem 2 (Executable size checker rejects `∞ + n < ∞ + n`)**:
The executable decision procedure `sizeLtB` returns `false` on `(.inf n, .inf n)` for every fuel
and size context. -/
theorem v5_sizeLtB_inf_self_false (fuel : Nat) (Ψ : SizeCtx) (n : Nat) :
    sizeLtB fuel Ψ (.inf n) (.inf n) = false := by
  cases fuel <;> simp [sizeLtB]

/-- **Class A Positive Blocking Theorem 3 (`NishtAbel2024V5` rejects self-instantiation at `∞`)**:
If a recursive function `f` has signature size context `Ψ_f = [(i, ∞)]` (representing `∀(i < ∞). A`),
instantiating `f` with `[∞]` (`as = [Size.infty]`) fails `SizeSubstWf Ψ [Size.infty] [(i, Size.infty)]`
under any valid valuation `ρ` of `Ψ`. -/
theorem v5_rejects_agda3026_self_instantiation {Ψ : SizeCtx} {ρ : SizeVal} (hρ : ValidVal Ψ ρ) (i : Nat) :
    ¬ SizeSubstWf Ψ [Size.infty] [(i, Size.infty)] := by
  intro ⟨_, hlt⟩
  have hk : 0 < [(i, Size.infty)].length := by simp
  have ha : 0 < [Size.infty].length := by simp
  have h0 := hlt 0 hk ha
  simp [Size.infty, Size.subst] at h0
  exact v5_not_sizeLt_inf_self hρ 0 h0

/-! ## Part 2: Class B — Mixed Positivity & Mutual Inductive/Coinductive Bugs (Agda Issue #7178) -/

/-- **Class B Negative Benchmark 1 (Finite-Size Russell Paradox from Unsound Fixpoint Subtyping)**:
Models the stage-indexed semantics of a mixed-variance inductive fixpoint `μ^i (λX. X → ⊥)` at
purely finite sizes `0 < 1` (with *no* infinite size `∞`):
- At stage `0`, `MuNeg 0` is inhabited (`PUnit`).
- At stage `i + 1`, `MuNeg (i + 1)` packs a refutation of stage `i` (`MuNeg i → False`).
Notice that `MuNeg : Nat → Type` is completely well-founded when stages are kept distinct (`mu_eqv`).
However, if covariant size subtyping `coerce01 : MuNeg 0 → MuNeg 1` (`mu_pos`) is permitted on this
negative functor, `False` is immediately derivable at finite sizes `0 < 1`. -/
def MuNeg : Nat → Prop
  | 0 => True
  | i + 1 => MuNeg i → False

theorem agda7178_finite_size_nonpos_subtyping_contradiction
    (coerce01 : MuNeg 0 → MuNeg 1) :
    False := by
  have x0 : MuNeg 0 := trivial
  have x1 : MuNeg 1 := coerce01 x0
  exact x1 x0

/-- **Class B Negative Benchmark 2 (Mutual Inductive/Coinductive Size-Variance Paradox — Agda #7178)**:
Models the interaction between a sized inductive type `D7178` and a sized coinductive record `R7178`
at purely finite sizes `0 < 1` (without `∞`):
- `D7178 R i` is an inductive proposition packing a refutation `R i → False`.
- `R7178 D i` is a coinductive record whose destructor `force : ∀ j < i, D j` yields `D j` at
  strictly smaller sizes `j < i`.
At depth `0`, `r0 : R7178 D 0` is inhabited vacuously (`∀ j < 0, D j`). If a type system fails to
enforce contravariant upward-closure of coinductive sizes (or shares an inductive covariant size
parameter with `R7178`, permitting `inflateR : R7178 D 0 → R7178 D 1`), we immediately derive
`False` at finite sizes `0 < 1`. -/
inductive D7178 (R : Nat → Prop) (i : Nat) : Prop where
  | mk (refute : R i → False) : D7178 R i

structure R7178 (D : Nat → Prop) (i : Nat) : Prop where
  force : ∀ j, j < i → D j

theorem D7178.elim {R : Nat → Prop} {i : Nat} (d : D7178 R i) (r : R i) : False := by
  cases d with
  | mk f => exact f r

theorem agda7178_mutual_ind_coind_variance_contradiction
    (inflateR : R7178 (D7178 (fun k => R7178 (fun _ => False) k)) 0 →
                R7178 (D7178 (fun k => R7178 (fun _ => False) k)) 1) :
    False := by
  have r0_inner : R7178 (fun _ => False) 0 :=
    ⟨fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  have r0 : R7178 (D7178 (fun k => R7178 (fun _ => False) k)) 0 :=
    ⟨fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  have r1 := inflateR r0
  have d0 := r1.force 0 (by decide)
  exact d0.elim r0_inner

/-- Helper: in a singleton negative bound context `[(.neg, .star)]`, `.var 0` cannot be kinded at
any kind `κ`. -/
theorem not_kinding_var0_neg_bctx (Ψ : SizeCtx) :
    ∀ (Δ : KCtx) (Δb : BCtx) (m : Nat) (V : Ty) (κ : Kind),
      Kinding Ψ Δ Δb m V κ →
      Δb = [(.neg, .star)] →
      V = .var 0 →
      False := by
  intro Δ Δb m V κ hk
  induction hk with
  | var hlookup husable =>
    intro hΔb hV
    subst hΔb
    injection hV with hk0
    subst hk0
    simp at hlookup
    rcases hlookup with ⟨rfl, rfl⟩
    exact husable
  | sub _ _ ih =>
    intro hΔb hV
    exact ih hΔb hV
  | _ =>
    intro _ hV
    contradiction

/-- **Class B Positive Blocking Theorem 1 (`NishtAbel2024V5` rejects negative functors at `+` polarity)**:
In `NishtAbel2024V5`, the negative functor body `X → 1` (`Ty.arr (.var 0) .unit`, where `var 0` is
the recursion variable of `μ` or `ν`) is provably rejected at positive polarity `+`:
`¬ Kinding Ψ Δ [(.pos, .star)] m (.arr (.var 0) .unit) .star`.
This statically blocks `SubTy.mu_pos` and `SubTy.nu_pos` from applying functor-changing / covariant
subtyping to negative recursive functors. -/
theorem v5_rejects_negative_functor_at_pos_polarity
    (Ψ : SizeCtx) (Δ : KCtx) (m : Nat) :
    ¬ Kinding Ψ Δ [(.pos, .star)] m (.arr (.var 0) .unit) .star := by
  have haux :
      ∀ (Δ' : KCtx) (Δb' : BCtx) (m' : Nat) (A : Ty) (κ : Kind),
        Kinding Ψ Δ' Δb' m' A κ →
        Δb' = [(.pos, .star)] →
        A = .arr (.var 0) .unit →
        False := by
    intro Δ' Δb' m' A κ hk
    induction hk with
    | arr hdom _ _ _ =>
      intro hΔb hA
      subst hΔb
      injection hA with hA1 _
      exact not_kinding_var0_neg_bctx Ψ _ _ _ _ _ hdom rfl hA1
    | sub _ _ ih =>
      intro hΔb hA
      exact ih hΔb hA
    | _ =>
      intro _ hA
      contradiction
  intro hk
  exact haux Δ [(.pos, .star)] m (.arr (.var 0) .unit) .star hk rfl rfl

/-- **Class B Positive Blocking Theorem 2 (`NishtAbel2024V5` signature encoding forbids shared `μ`/`ν` sizes)**:
By `lemma_3`, when `Encode .neg ok .pos Δ Δb A Ψ A'` encodes a function signature `A`, no generated
size parameter `i ∈ Ψ.dom` can ever occur both as an inductive `μ`-index and as a coinductive
`ν`-index in `A'`. This statically prevents Agda #7178's shared inductive/coinductive size variable
inversion. -/
theorem v5_encode_forbids_shared_mu_nu_size
    {ok : Nat → Prop} {Δ : KCtx} {Δb : BCtx} {A A' : Ty} {Ψ : SizeCtx}
    (henc : Encode .neg ok .pos Δ Δb A Ψ A')
    {i : Nat} (hi : i ∈ Ψ.dom)
    (Δ₁ : KCtx) (Δb₁ : BCtx) (π₁ : Pol)
    (Δ₂ : KCtx) (Δb₂ : BCtx) (π₂ : Pol) :
    ¬ (SizeOcc .mu i Δ₁ Δb₁ π₁ A' ∧ SizeOcc .nu i Δ₂ Δb₂ π₂ A') := by
  rintro ⟨hmu, hnu⟩
  rcases lemma_3 henc i hi with ⟨_, _, hno_nu⟩ | ⟨_, _, hno_mu⟩
  · exact hno_nu Δ₂ Δb₂ π₂ hnu
  · exact hno_mu Δ₁ Δb₁ π₁ hmu

/-- **Class B Positive Benchmark (`NishtAbel2024V5` accepts valid mixed inductive-coinductive blocks)**:
While rejecting both Class A (#3026) and Class B (#7178) inconsistencies, `NishtAbel2024V5` accepts
and proves semantic strong normalization (`SemValid`) for the worked 5-function block in
`Solutions/V5/Example.lean` (`copy` on inductive `Nat`, `zeros` on coinductive `Stream`, polymorphic
`len`, bounded-size `count`, and mixed-variance `evalT`). -/
theorem v5_accepts_valid_mixed_block :
    SemValid Example.block Example.block :=
  NishtAbel2024V5.example_block_valid

end SizedTypes.Milestone1_1

#print axioms SizedTypes.Milestone1_1.agda3026_wf_contradiction
#print axioms SizedTypes.Milestone1_1.agda3026_bad_inductive_contradiction
#print axioms SizedTypes.Milestone1_1.agda3026_loop_not_sn
#print axioms SizedTypes.Milestone1_1.v5_not_sizeLt_infty_infty
#print axioms SizedTypes.Milestone1_1.v5_rejects_agda3026_self_instantiation
#print axioms SizedTypes.Milestone1_1.agda7178_finite_size_nonpos_subtyping_contradiction
#print axioms SizedTypes.Milestone1_1.agda7178_mutual_ind_coind_variance_contradiction
#print axioms SizedTypes.Milestone1_1.v5_rejects_negative_functor_at_pos_polarity
#print axioms SizedTypes.Milestone1_1.v5_encode_forbids_shared_mu_nu_size
#print axioms SizedTypes.Milestone1_1.v5_accepts_valid_mixed_block
