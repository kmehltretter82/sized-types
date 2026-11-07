import Solutions.V5.Final

/-!
# Milestone 1.2: The Verified Elaboration / Erasure Theorem & Dual Lowering (`WellFounded.fix` + `brecOn`)

This module implements and proves **Milestone 1.2** of `plan.md` (§2.1, §2.3, §3 Milestone 1.2):
$$\Gamma \vdash_{\text{sized}} t : A \implies \Gamma^\circ \vdash_{\text{Lean}} E(t) : A^\circ$$
together with the **Architectural Separation of Concerns** from `plan.md` (§1):
1. **Termination / Productivity**: Verified compositionally in types via size bounds `j < i` or
   size-change invocation graphs (`SCTValid G`).
2. **Elaboration to Standard Lean 4 Kernel Terms (`E(t)`)**: Translating size-checked definitions
   into unmodified Lean 4 without any new axioms (`[propext, Classical.choice, Quot.sound]`).
3. **Definitional Reduction (`rfl`) via Dual Lowering**:
   - **Path A (Spine-Structural / Course-of-Values Lowering)**: When the size index tracks an
     inductive spine (`Nat`, `Rose α`), bounded-size recursion lowers into structural course-of-values
     recursion, recovering **kernel `rfl` reduction** while proving semantic equivalence with the
     `WellFounded.fix` lowering.
   - **Path B (General SCT Mutual-Block `WellFounded.fix` Lowering)**: For arbitrary mutual blocks
     checked by an `SCTValid` size-change graph family `G` from `NishtAbel2024V5`, Theorem 1
     (`callRel_wf`) discharges `WellFounded (CallRel G)` to compile the mutual block into a single
     Lean 4 `WellFounded.fix` definition with a verified unfolding theorem.
-/

namespace SizedTypes.Milestone1_2

open NishtAbel2024V5
open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid FunName)

/-! ## Part 1: Intrinsic Sized Calculus & Verified Erasure Theorem (`Γ ⊢_sized t : A ⟹ Γ° ⊢_Lean E(t) : A°`) -/

/-- Object-level types of the core sized calculus, parameterized by a size scope `s`.
Includes `unit`, products, arrows, size-bounded natural numbers `nat sz`, and universal bounded-size
quantification `forallLt sz B` (`∀ j < sz, B(j)`). -/
inductive SizedTy : Nat → Type where
  | unit {s : Nat} : SizedTy s
  | nat {s : Nat} (sz : Fin s) : SizedTy s
  | prod {s : Nat} (A B : SizedTy s) : SizedTy s
  | arr {s : Nat} (A B : SizedTy s) : SizedTy s
  | forallLt {s : Nat} (sz : Fin s) (B : SizedTy (s + 1)) : SizedTy s

/-- **Erased Lean 4 Type (`A°`)**: strips all size indices and bounded size quantifiers, translating
every `SizedTy s` into a standard unannotated Lean 4 `Type`. -/
@[reducible] def SizedTy.erase : {s : Nat} → SizedTy s → Type
  | _, .unit => PUnit
  | _, .nat _ => Nat
  | _, .prod A B => A.erase × B.erase
  | _, .arr A B => A.erase → B.erase
  | _, .forallLt _ B => B.erase

/-- **Size-Indexed Semantic Type (`⟦A⟧_ρ`)**: interprets `nat sz` as the bounded subtype
`{ n : Nat // n ≤ ρ sz }` and `forallLt sz B` as the bounded dependent product
`∀ (j : Nat), j < ρ sz → ⟦B⟧_{(j :: ρ)}`. -/
@[reducible] def SizedTy.sem : {s : Nat} → (Fin s → Nat) → SizedTy s → Type
  | _, _, .unit => PUnit
  | _, ρ, .nat sz => { n : Nat // n ≤ ρ sz }
  | _, ρ, .prod A B => A.sem ρ × B.sem ρ
  | _, ρ, .arr A B => A.sem ρ → B.sem ρ
  | _, ρ, .forallLt sz B => ∀ (j : Nat), j < ρ sz → B.sem (Fin.cons j ρ)

/-- Logical relation `Rel A ρ v_sem v_erased` connecting the size-indexed semantic value
`v_sem : A.sem ρ` to its size-erased Lean 4 kernel value `v_erased : A.erase`. -/
def SizedTy.Rel : {s : Nat} → (A : SizedTy s) → (ρ : Fin s → Nat) → A.sem ρ → A.erase → Prop
  | _, .unit, _, _, _ => True
  | _, .nat _, _, v_sem, v_erased => v_sem.1 = v_erased
  | _, .prod A B, ρ, v_sem, v_erased =>
      A.Rel ρ v_sem.1 v_erased.1 ∧ B.Rel ρ v_sem.2 v_erased.2
  | _, .arr A B, ρ, f_sem, f_erased =>
      ∀ x_sem x_erased, A.Rel ρ x_sem x_erased → B.Rel ρ (f_sem x_sem) (f_erased x_erased)
  | _, .forallLt sz B, ρ, f_sem, v_erased =>
      ∀ (j : Nat) (hj : j < ρ sz), B.Rel (Fin.cons j ρ) (f_sem j hj) v_erased

/-- Typing contexts `Γ` in size scope `s`. -/
abbrev SizedCtx (s : Nat) := List (SizedTy s)

/-- Erased Lean 4 context `Γ°`. -/
@[reducible] def SizedCtx.erase {s : Nat} : SizedCtx s → Type
  | [] => PUnit
  | A :: Γ => A.erase × SizedCtx.erase Γ

/-- Size-indexed semantic context `⟦Γ⟧_ρ`. -/
@[reducible] def SizedCtx.sem {s : Nat} (ρ : Fin s → Nat) : SizedCtx s → Type
  | [] => PUnit
  | A :: Γ => A.sem ρ × SizedCtx.sem ρ Γ

/-- Pointwise logical relation on environments `γ_sem` and `γ_erased`. -/
def SizedCtx.Rel {s : Nat} (ρ : Fin s → Nat) :
    (Γ : SizedCtx s) → Γ.sem ρ → Γ.erase → Prop
  | [], _, _ => True
  | A :: Γ, (x_s, γ_s), (x_e, γ_e) => A.Rel ρ x_s x_e ∧ SizedCtx.Rel ρ Γ γ_s γ_e

/-- De Bruijn variable lookup in `Γ`. -/
inductive HasVar {s : Nat} : SizedCtx s → SizedTy s → Type where
  | zero {Γ : SizedCtx s} {A : SizedTy s} : HasVar (A :: Γ) A
  | succ {Γ : SizedCtx s} {A B : SizedTy s} : HasVar Γ A → HasVar (B :: Γ) A

def HasVar.evalErase {s : Nat} {Γ : SizedCtx s} {A : SizedTy s} :
    HasVar Γ A → Γ.erase → A.erase
  | .zero, (x, _) => x
  | .succ v, (_, γ) => v.evalErase γ

def HasVar.evalSem {s : Nat} {ρ : Fin s → Nat} {Γ : SizedCtx s} {A : SizedTy s} :
    HasVar Γ A → Γ.sem ρ → A.sem ρ
  | .zero, (x, _) => x
  | .succ v, (_, γ) => v.evalSem γ

theorem HasVar.rel {s : Nat} {ρ : Fin s → Nat} {Γ : SizedCtx s} {A : SizedTy s}
    (v : HasVar Γ A) {γ_s : Γ.sem ρ} {γ_e : Γ.erase}
    (hγ : SizedCtx.Rel ρ Γ γ_s γ_e) :
    A.Rel ρ (v.evalSem γ_s) (v.evalErase γ_e) := by
  induction v with
  | zero => exact hγ.1
  | succ _ ih => exact ih hγ.2

/-- Structural fuel-bounded course-of-values helper used to elaborate `SizedTm.fixNat`. -/
def evalFixNatErase {α : Type} (base : α) (next : Nat → Nat) (combine : α → Nat → α) :
    Nat → Nat → α
  | 0, _ => base
  | _ + 1, 0 => base
  | fuel + 1, n + 1 => combine (evalFixNatErase base next combine fuel (next n)) n

def evalFixNatSem {α : Type} (bound : Nat) (base : α)
    (next : { n : Nat // n ≤ bound } → { n : Nat // n ≤ bound })
    (combine : α → { n : Nat // n ≤ bound } → α) :
    (fuel : Nat) → { n : Nat // n ≤ bound } → α
  | 0, _ => base
  | _ + 1, ⟨0, _⟩ => base
  | fuel + 1, ⟨n + 1, hn⟩ =>
      let pred : { k : Nat // k ≤ bound } := ⟨n, Nat.le_of_succ_le hn⟩
      combine (evalFixNatSem bound base next combine fuel (next pred)) pred

theorem evalFixNat_rel {s : Nat} (ρ : Fin s → Nat) (A : SizedTy s) (bound : Nat)
    (base_s : A.sem ρ) (base_e : A.erase) (hbase : A.Rel ρ base_s base_e)
    (next_s : { n : Nat // n ≤ bound } → { n : Nat // n ≤ bound })
    (next_e : Nat → Nat)
    (hnext : ∀ x_s x_e, x_s.1 = x_e → (next_s x_s).1 = next_e x_e)
    (comb_s : A.sem ρ → { n : Nat // n ≤ bound } → A.sem ρ)
    (comb_e : A.erase → Nat → A.erase)
    (hcomb : ∀ a_s a_e x_s x_e, A.Rel ρ a_s a_e → x_s.1 = x_e →
      A.Rel ρ (comb_s a_s x_s) (comb_e a_e x_e)) :
    ∀ (fuel : Nat) (x_s : { n : Nat // n ≤ bound }) (x_e : Nat),
      x_s.1 = x_e →
      A.Rel ρ (evalFixNatSem bound base_s next_s comb_s fuel x_s)
        (evalFixNatErase base_e next_e comb_e fuel x_e)
  | 0, _, _, _ => hbase
  | _ + 1, ⟨0, _⟩, 0, _ => hbase
  | _ + 1, ⟨0, _⟩, _ + 1, h => by cases h
  | _ + 1, ⟨_ + 1, _⟩, 0, h => by cases h
  | fuel + 1, ⟨n + 1, hn⟩, m + 1, h => by
    injection h with hnm
    subst hnm
    simp only [evalFixNatSem, evalFixNatErase]
    have hrec := evalFixNat_rel ρ A bound base_s base_e hbase next_s next_e hnext comb_s comb_e
      hcomb fuel (next_s ⟨n, Nat.le_of_succ_le hn⟩) (next_e n) (hnext ⟨n, Nat.le_of_succ_le hn⟩ n rfl)
    exact hcomb _ _ ⟨n, Nat.le_of_succ_le hn⟩ n hrec rfl

/-- Intrinsically typed terms `Γ ⊢_sized t : A` of the core sized calculus, including:
- lambda abstraction, application, products, unit,
- size-preserving `zero` and `minus` on `nat sz`, and
- bounded-size course-of-values recursion `fixNat` over `nat sz` (allowing non-structural
  size-preserving step transitions `nextArg : SizedTm (.nat sz :: Γ) (.nat sz)` such as `minus`). -/
inductive SizedTm : {s : Nat} → SizedCtx s → SizedTy s → Type where
  | var {s : Nat} {Γ : SizedCtx s} {A : SizedTy s} :
      HasVar Γ A → SizedTm Γ A
  | unit {s : Nat} {Γ : SizedCtx s} :
      SizedTm Γ .unit
  | pair {s : Nat} {Γ : SizedCtx s} {A B : SizedTy s} :
      SizedTm Γ A → SizedTm Γ B → SizedTm Γ (.prod A B)
  | fst {s : Nat} {Γ : SizedCtx s} {A B : SizedTy s} :
      SizedTm Γ (.prod A B) → SizedTm Γ A
  | snd {s : Nat} {Γ : SizedCtx s} {A B : SizedTy s} :
      SizedTm Γ (.prod A B) → SizedTm Γ B
  | lam {s : Nat} {Γ : SizedCtx s} {A B : SizedTy s} :
      SizedTm (A :: Γ) B → SizedTm Γ (.arr A B)
  | app {s : Nat} {Γ : SizedCtx s} {A B : SizedTy s} :
      SizedTm Γ (.arr A B) → SizedTm Γ A → SizedTm Γ B
  | zero {s : Nat} {Γ : SizedCtx s} (sz : Fin s) :
      SizedTm Γ (.nat sz)
  | minus {s : Nat} {Γ : SizedCtx s} (sz₁ sz₂ : Fin s) :
      SizedTm Γ (.nat sz₁) → SizedTm Γ (.nat sz₂) → SizedTm Γ (.nat sz₁)
  | fixNat {s : Nat} {Γ : SizedCtx s} {A : SizedTy s} (sz : Fin s) :
      SizedTm Γ (.nat sz) →
      SizedTm Γ A →
      SizedTm (.nat sz :: Γ) (.nat sz) →
      SizedTm (A :: .nat sz :: Γ) A →
      SizedTm Γ A

/-- **Verified Elaboration Pass `E(t)` (`SizedTm.elaborate`)**:
Translates any size-checked derivation `Γ ⊢_sized t : A` into a standard, size-erased Lean 4 term
`Γ° → A°`. By construction, `t.elaborate` has type `Γ.erase → A.erase` in Lean 4's kernel,
immediately establishing **Milestone 1.2's typing theorem**
`Γ ⊢_sized t : A ⟹ Γ° ⊢_Lean E(t) : A°`! -/
def SizedTm.elaborate {s : Nat} {Γ : SizedCtx s} {A : SizedTy s} :
    SizedTm Γ A → (Γ.erase → A.erase)
  | .var v, γ => v.evalErase γ
  | .unit, _ => PUnit.unit
  | .pair t₁ t₂, γ => (t₁.elaborate γ, t₂.elaborate γ)
  | .fst t, γ => (t.elaborate γ).1
  | .snd t, γ => (t.elaborate γ).2
  | .lam body, γ => fun x => body.elaborate (x, γ)
  | .app f x, γ => (f.elaborate γ) (x.elaborate γ)
  | .zero _, _ => (0 : Nat)
  | .minus _ _ t₁ t₂, γ => (t₁.elaborate γ : Nat) - (t₂.elaborate γ : Nat)
  | .fixNat _ arg base next combine, γ =>
      let n : Nat := arg.elaborate γ
      evalFixNatErase (base.elaborate γ) (fun m => next.elaborate (m, γ))
        (fun acc m => combine.elaborate (acc, (m, γ))) n n

/-- Size-indexed semantic evaluation `⟦t⟧_ρ : ⟦Γ⟧_ρ → ⟦A⟧_ρ`, verifying that every size bound is
preserved at run time. -/
def SizedTm.evalSem {s : Nat} (ρ : Fin s → Nat) {Γ : SizedCtx s} {A : SizedTy s} :
    SizedTm Γ A → (Γ.sem ρ → A.sem ρ)
  | .var v, γ => v.evalSem γ
  | .unit, _ => PUnit.unit
  | .pair t₁ t₂, γ => (t₁.evalSem ρ γ, t₂.evalSem ρ γ)
  | .fst t, γ => (t.evalSem ρ γ).1
  | .snd t, γ => (t.evalSem ρ γ).2
  | .lam body, γ => fun x => body.evalSem ρ (x, γ)
  | .app f x, γ => (f.evalSem ρ γ) (x.evalSem ρ γ)
  | .zero _, _ => ⟨0, Nat.zero_le _⟩
  | .minus _ _ t₁ t₂, γ =>
      let v₁ := t₁.evalSem ρ γ
      let v₂ := t₂.evalSem ρ γ
      ⟨v₁.1 - v₂.1, Nat.le_trans (Nat.sub_le v₁.1 v₂.1) v₁.2⟩
  | .fixNat sz arg base next combine, γ =>
      let v := arg.evalSem ρ γ
      evalFixNatSem (ρ sz) (base.evalSem ρ γ) (fun m => next.evalSem ρ (m, γ))
        (fun acc m => combine.evalSem ρ (acc, (m, γ))) v.1 v

/-- **Milestone 1.2 Core Theorem (`elaborate_sound_and_coherent`)**:
Every size-checked term `t : SizedTm Γ A` elaborates to a well-typed Lean 4 term
`t.elaborate : Γ.erase → A.erase` that is logically related (`A.Rel ρ`) to its size-indexed
semantic evaluation `t.evalSem ρ` across all size valuations `ρ` and related contexts. -/
theorem elaborate_sound_and_coherent {s : Nat} (ρ : Fin s → Nat)
    {Γ : SizedCtx s} {A : SizedTy s} (t : SizedTm Γ A)
    {γ_s : Γ.sem ρ} {γ_e : Γ.erase} (hγ : SizedCtx.Rel ρ Γ γ_s γ_e) :
    A.Rel ρ (t.evalSem ρ γ_s) (t.elaborate γ_e) := by
  induction t with
  | var v => exact v.rel hγ
  | unit => trivial
  | pair _ _ ih₁ ih₂ => exact ⟨ih₁ hγ, ih₂ hγ⟩
  | fst _ ih => exact (ih hγ).1
  | snd _ ih => exact (ih hγ).2
  | lam _ ih =>
    intro x_s x_e hx
    exact ih ⟨hx, hγ⟩
  | app _ _ ihf ihx =>
    exact ihf hγ _ _ (ihx hγ)
  | zero _ => rfl
  | minus _ _ _ _ ih₁ ih₂ =>
    simp only [SizedTy.Rel, SizedTm.evalSem, SizedTm.elaborate]
    exact congrArg₂ HSub.hSub (ih₁ hγ) (ih₂ hγ)
  | fixNat sz arg base next combine ihArg ihBase ihNext ihComb =>
    have hArg : (arg.evalSem ρ γ_s).1 = arg.elaborate γ_e := ihArg hγ
    simp only [SizedTm.evalSem, SizedTm.elaborate]
    rw [← hArg]
    exact evalFixNat_rel ρ _ (ρ sz)
      (base.evalSem ρ γ_s) (base.elaborate γ_e) (ihBase hγ)
      (fun m => next.evalSem ρ (m, γ_s)) (fun m => next.elaborate (m, γ_e))
      (fun x_s x_e hx => ihNext ⟨hx, hγ⟩)
      (fun acc m => combine.evalSem ρ (acc, (m, γ_s)))
      (fun acc m => combine.elaborate (acc, (m, γ_e)))
      (fun a_s a_e x_s x_e ha hx => ihComb ⟨ha, ⟨hx, hγ⟩⟩)
      (arg.evalSem ρ γ_s).1 (arg.evalSem ρ γ_s) (arg.evalSem ρ γ_s).1 rfl

/-! ## Part 2: Dual Lowering (`WellFounded.fix` vs. Spine-Structural `brecOn`) & Kernel `rfl` Reduction -/

/-! ### 2A. Non-Structural Size-Preserving Recursion (`minus` & `div`, Nisht & Abel §2.6) -/

/-- Size-bounded natural numbers `SizedNat i = { n : Nat // n ≤ i }`. -/
abbrev SizedNat (i : Nat) := { n : Nat // n ≤ i }

/-- Size-preserving subtraction `sizedMinus : ∀ i, SizedNat i → Nat → SizedNat i`.
Crucially, the return type `SizedNat i` guarantees compositionally in the type signature that the
output is never larger than the first input's size bound `i`. -/
def sizedMinus (i : Nat) (x : SizedNat i) (y : Nat) : SizedNat i :=
  ⟨x.1 - y, Nat.le_trans (Nat.sub_le x.1 y) x.2⟩

/-- Step functional for `divWF`. -/
def divStep (i : Nat) (rec : ∀ j, j < i → SizedNat j → Nat → Nat) : SizedNat i → Nat → Nat :=
  match i with
  | 0 => fun _ _ => 0
  | j + 1 => fun x y =>
      match x with
      | ⟨0, _⟩ => 0
      | ⟨n + 1, hn⟩ =>
          1 + rec j (Nat.lt_succ_self j) (sizedMinus j ⟨n, Nat.le_of_succ_le_succ hn⟩ y) y

/-- **Lowering 1 (`WellFounded.fix` over the size index `i`)**:
Uses the compositional type of `sizedMinus` so the recursive call `divWF j (sizedMinus j x' y) y`
decreases strictly on the size parameter `j < j + 1` without inspecting `sizedMinus`'s body. -/
def divWF (i : Nat) : SizedNat i → Nat → Nat :=
  @WellFounded.fix Nat (fun k => SizedNat k → Nat → Nat) (· < ·) Nat.lt_wfRel.wf divStep i

/-- Unfolding equation for `divWF`. -/
theorem divWF_eq (i : Nat) (x : SizedNat i) (y : Nat) :
    divWF i x y = divStep i (fun j _ => divWF j) x y := by
  unfold divWF
  exact congrFun (congrFun (WellFounded.fix_eq Nat.lt_wfRel.wf divStep i) x) y

/-- **Lowering 2 (Spine-Structural Fuel / Course-of-Values Lowering Preserving `rfl`)**:
Compiles the size bound `i` directly into structural recursion on `Nat`, so the Lean 4 kernel
reduces concrete applications by `rfl` without unfolding `WellFounded.fix`! -/
def divStructural : (i : Nat) → SizedNat i → Nat → Nat
  | 0, _, _ => 0
  | _ + 1, ⟨0, _⟩, _ => 0
  | j + 1, ⟨n + 1, hn⟩, y =>
      1 + divStructural j (sizedMinus j ⟨n, Nat.le_of_succ_le_succ hn⟩ y) y

/-- Erased entry point `divErased x y` instantiating the tight size bound `i = x`. -/
def divErased (x y : Nat) : Nat :=
  divStructural x ⟨x, Nat.le_refl x⟩ y

/-- **Equivalence Theorem (`divStructural_eq_divWF`)**:
The spine-structural lowering (`divStructural`) and the `WellFounded.fix` lowering (`divWF`)
compute the exact same function on all inputs `i`, `x : SizedNat i`, and `y`. -/
theorem divStructural_eq_divWF :
    ∀ (i : Nat) (x : SizedNat i) (y : Nat),
      divStructural i x y = divWF i x y
  | 0, x, y => by
    rw [divWF_eq]
    rfl
  | j + 1, ⟨0, hn⟩, y => by
    rw [divWF_eq]
    rfl
  | j + 1, ⟨n + 1, hn⟩, y => by
    rw [divWF_eq]
    simp only [divStructural, divStep]
    congr 1
    exact divStructural_eq_divWF j (sizedMinus j ⟨n, Nat.le_of_succ_le_succ hn⟩ y) y

/-- **Definitional Reduction (`rfl`) Benchmark 1**:
Because `divErased` lowers bounded-size recursion into structural recursion, Lean 4's kernel
evaluates `divErased 10 2 = 4` (computing `⌈10 / (2 + 1)⌉ = 4`) **definitionally by `rfl`**! -/
theorem divErased_10_2_rfl : divErased 10 2 = 4 := rfl

theorem divErased_15_2_rfl : divErased 15 2 = 5 := rfl

/-! ### 2B. Compositional Higher-Order Rose Tree Traversal (`plan.md` §2.1 & §2.3) -/

/-- Standard unannotated rose tree in Lean 4 (`Rose° α`). -/
inductive Rose (α : Type) : Type where
  | node (val : α) (children : List (Rose α)) : Rose α
  deriving Repr

mutual

/-- Tree depth (height) of an unannotated `Rose α`. -/
def Rose.depth {α : Type} : Rose α → Nat
  | .node _ cs => 1 + Rose.depthList cs

def Rose.depthList {α : Type} : List (Rose α) → Nat
  | [] => 0
  | c :: cs => max c.depth (Rose.depthList cs)

end

/-- Size-indexed rose tree `SizedRose α i` (`Rose^[i] α` from `plan.md` §2.1):
An element of `SizedRose α i` is a rose tree of depth bounded by `i`. -/
abbrev SizedRose (α : Type) (i : Nat) := { t : Rose α // t.depth ≤ i }

/-- Zero-cost size erasure `(t : SizedRose α i).erase : Rose α`. -/
def SizedRose.erase {α : Type} {i : Nat} (t : SizedRose α i) : Rose α := t.1

/-- Canonical size reconstruction: every unannotated `t : Rose α` embeds into `SizedRose α t.depth`. -/
def Rose.toSized {α : Type} (t : Rose α) : SizedRose α t.depth := ⟨t, Nat.le_refl _⟩

theorem Rose.depth_mem_lt {α : Type} (v : α) (cs : List (Rose α)) :
    ∀ {c : Rose α}, c ∈ cs → c.depth < (Rose.node v cs).depth := by
  intro c hc
  simp only [Rose.depth]
  have hle : ∀ (xs : List (Rose α)), c ∈ xs → c.depth ≤ Rose.depthList xs := by
    intro xs hmem
    induction xs with
    | nil => cases hmem
    | cons _ rest ih =>
      simp only [Rose.depthList]
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hrest) (Nat.le_max_right _ _)
  have := hle cs hc
  omega

/-- Unpack the children of `t : SizedRose α i` into a list of size-bounded children
`List (Σ j : { j : Nat // j < i }, SizedRose α j.1)`. -/
def unpackSizedChildren {α : Type} {i : Nat} (v : α) (cs : List (Rose α))
    (h : (Rose.node v cs).depth ≤ i) :
    List (Σ j : { j : Nat // j < i }, SizedRose α j.1) :=
  unpackAux cs (fun c hc => Nat.lt_of_lt_of_le (Rose.depth_mem_lt v cs hc) h)
where
  unpackAux : (xs : List (Rose α)) → (∀ c ∈ xs, c.depth < i) →
      List (Σ j : { j : Nat // j < i }, SizedRose α j.1)
  | [], _ => []
  | c :: rest, hlt =>
      ⟨⟨c.depth, hlt c List.mem_cons_self⟩, ⟨c, Nat.le_refl _⟩⟩ ::
        unpackAux rest (fun _ hc' => hlt _ (List.mem_cons_of_mem c hc'))

/-- Pack a list of size-bounded children `List (Σ j : { j : Nat // j < i }, SizedRose β j.1)` back
into `SizedRose β i`. -/
def packSizedNode {β : Type} {i : Nat} (v : β)
    (cs : List (Σ j : { j : Nat // j < i }, SizedRose β j.1))
    (hi : 0 < i) : SizedRose β i :=
  ⟨Rose.node v (cs.map fun p => p.2.1), by
    simp only [Rose.depth]
    have hbound : ∀ (xs : List (Σ j : { j : Nat // j < i }, SizedRose β j.1)),
        Rose.depthList (xs.map fun p => p.2.1) < i := by
      intro xs
      induction xs with
      | nil => exact hi
      | cons p rest ih =>
        simp only [List.map, Rose.depthList]
        exact Nat.max_lt.mpr ⟨Nat.lt_of_le_of_lt p.2.2 p.1.2, ih⟩
    have := hbound cs
    omega⟩

/-- Custom higher-order child transformer across an abstraction boundary (`plan.md` §2.1):
Takes a size-bounded step callback `step : ∀ j < i, SizedRose α j → SizedRose β j` and applies it
across a list of sized children without inspecting `step`'s implementation. -/
def transformChildren {α β : Type} {i : Nat}
    (step : ∀ (j : Nat), j < i → SizedRose α j → SizedRose β j) :
    List (Σ j : { j : Nat // j < i }, SizedRose α j.1) →
    List (Σ j : { j : Nat // j < i }, SizedRose β j.1)
  | [] => []
  | ⟨⟨j, hj⟩, child⟩ :: rest =>
      ⟨⟨j, hj⟩, step j hj child⟩ :: transformChildren step rest

/-- **Higher-Order Sized Rose-Tree Traversal (`mapRoseSized`)**:
Passes the recursive call `(fun j _ child => mapRoseSized f j child)` directly as a first-class
higher-order argument to `transformChildren`. Termination is checked purely from the size bound
`j < i` in the type of `transformChildren`'s `step` parameter! -/
def mapRoseSized {α β : Type} (f : α → β) : (i : Nat) → SizedRose α i → SizedRose β i
  | i, ⟨.node v cs, h⟩ =>
      have hi : 0 < i := by
        simp only [Rose.depth] at h
        omega
      packSizedNode (f v)
        (transformChildren (fun j _ child => mapRoseSized f j child) (unpackSizedChildren v cs h))
        hi
termination_by i _ => i

/-- Spine-structural lowering of `mapRoseSized` on unannotated `Rose α` (`Rose.map`). -/
def Rose.map {α β : Type} (f : α → β) : Rose α → Rose β
  | .node v cs => .node (f v) (mapList cs)
where
  mapList : List (Rose α) → List (Rose β)
  | [] => []
  | c :: cs => c.map f :: mapList cs

/-- **Coherence of Higher-Order Sized Rose Traversal with Spine-Structural `Rose.map`**:
Erasing the output of the higher-order size-checked `mapRoseSized f i t` (which passes the
recursive call across `transformChildren`) produces the exact same `Rose β` as the spine-structural
`t.erase.map f`! -/
theorem mapRoseSized_erase_eq {α β : Type} (f : α → β) :
    ∀ (i : Nat) (t : SizedRose α i),
      (mapRoseSized f i t).erase = t.erase.map f
  | i, ⟨.node v cs, h⟩ => by
    rw [mapRoseSized]
    simp only [SizedRose.erase, packSizedNode, Rose.map, unpackSizedChildren]
    congr 1
    have hlt0 : ∀ c ∈ cs, c.depth < i :=
      fun c hc => Nat.lt_of_lt_of_le (Rose.depth_mem_lt v cs hc) h
    have haux :
        ∀ (xs : List (Rose α)) (hlt : ∀ c ∈ xs, c.depth < i)
          (ih_xs : ∀ c ∈ xs, (mapRoseSized f c.depth ⟨c, Nat.le_refl _⟩).erase = c.map f),
          List.map (fun p => p.2.1)
            (transformChildren (fun j _ child => mapRoseSized f j child)
              (unpackSizedChildren.unpackAux xs hlt)) =
          Rose.map.mapList f xs := by
      intro xs
      induction xs with
      | nil =>
        intro _ _
        rfl
      | cons c rest ih =>
        intro hlt ih_xs
        simp only [unpackSizedChildren.unpackAux, transformChildren, List.map, Rose.map.mapList]
        have hhead : (mapRoseSized f c.depth ⟨c, Nat.le_refl _⟩).erase = c.map f :=
          ih_xs c List.mem_cons_self
        rw [SizedRose.erase] at hhead
        rw [hhead, ih (fun _ hc' => hlt _ (List.mem_cons_of_mem c hc'))
          (fun c' hc' => ih_xs c' (List.mem_cons_of_mem c hc'))]
    exact haux cs hlt0 (fun c hc =>
      have : c.depth < i := hlt0 c hc
      mapRoseSized_erase_eq f c.depth ⟨c, Nat.le_refl _⟩)
termination_by i _ => i

/-- **Definitional Reduction (`rfl`) Benchmark 2 (Rose Tree Traversal)**:
Concrete nested `Rose Nat` mapped via the spine-structural lowering reduces definitionally
**by `rfl`** in Lean 4's kernel! -/
def sampleRose : Rose Nat :=
  .node 10 [.node 20 [.node 30 []], .node 40 []]

theorem mapRose_rfl_benchmark :
    sampleRose.map (· + 1) =
      Rose.node 11 [Rose.node 21 [Rose.node 31 []], Rose.node 41 []] := rfl

/-! ### 2C. General SCT Mutual-Block Lowering to `WellFounded.fix` via `NishtAbel2024V5` Theorem 1 -/

/-- Call states `(f, αs)` pairing a function identifier `f : FunName` with its ordinal size tuple. -/
abbrev SCTCallState := FunName × List Ordinal.{0}

/-- **General SCT-to-`WellFounded.fix` Elaborator (`elaborateSCTBlock`)**:
Given any invocation graph family `G : InvGraphFamily` satisfying Lee–Jones–Ben-Amram size-change
termination (`hSCT : SCTValid G`), `NishtAbel2024V5`'s **Theorem 1** (`callRel_wf ramseyPairs G hSCT`)
proves that `CallRel G : SCTCallState → SCTCallState → Prop` is well-founded
(`WellFounded (CallRel G)`).

Therefore, *any* mutually recursive family of functions `step` indexed by `s : SCTCallState` whose
recursive calls transition along `CallRel G s' s` elaborates directly to a total Lean 4 definition
via `WellFounded.fix`, with a verified unfolding theorem (`elaborateSCTBlock_eq`)! -/
noncomputable def elaborateSCTBlock
    {G : InvGraphFamily} (hSCT : SCTValid G)
    {R : SCTCallState → Type}
    (step : ∀ (s : SCTCallState), (∀ (s' : SCTCallState), CallRel G s' s → R s') → R s) :
    ∀ (s : SCTCallState), R s :=
  WellFounded.fix (callRel_wf ramseyPairs G hSCT) step

/-- **Verified Unfolding Theorem for `elaborateSCTBlock`**:
Every mutual block elaborated from an `SCTValid` size-change graph family `G` satisfies its exact
recursive specification for all call states `s : SCTCallState`. -/
theorem elaborateSCTBlock_eq
    {G : InvGraphFamily} (hSCT : SCTValid G)
    {R : SCTCallState → Type}
    (step : ∀ (s : SCTCallState), (∀ (s' : SCTCallState), CallRel G s' s → R s') → R s)
    (s : SCTCallState) :
    elaborateSCTBlock hSCT step s =
      step s (fun s' _hrel => elaborateSCTBlock hSCT step s') :=
  WellFounded.fix_eq (callRel_wf ramseyPairs G hSCT) step s

end SizedTypes.Milestone1_2

#print axioms SizedTypes.Milestone1_2.elaborate_sound_and_coherent
#print axioms SizedTypes.Milestone1_2.divStructural_eq_divWF
#print axioms SizedTypes.Milestone1_2.divErased_10_2_rfl
#print axioms SizedTypes.Milestone1_2.mapRoseSized_erase_eq
#print axioms SizedTypes.Milestone1_2.mapRose_rfl_benchmark
#print axioms SizedTypes.Milestone1_2.elaborateSCTBlock_eq
