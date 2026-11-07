import Solutions.V5.Final

/-!
# Stage 1: `MiniLean-Sized` — Executable Bidirectional Type & Termination Checker

This module implements **Stage 1 (`MiniLean-Sized`)** from `plan.md`: a self-contained,
executable bidirectional type and size-change termination checker in Lean 4 for
System `F_ω^c` / `F_ω^{cop,SCT}` (Nisht & Abel 2024), together with `0-sorry` soundness
theorems connecting every executable pass to the relational judgments and strong
normalization theorem (`theorem_15_proof`).

## Architecture of the Executable Pipeline

1. **Source Validation & Kind Checking (`unsizedB`, `inferKindB`, `checkKindB`, `ekindingB`)**:
   Verifies that input types are size-free (`Unsized`) and well-kinded (`Kinding` / `EKinding`),
   including variance-aware operator kinding and positive/mixed fixpoint functor checks.
2. **Polarized Signature Encoding (`encodeTyB`, `encodeDeclB`, `encodeBlockB`)**:
   Allocates fresh rigid size parameters (even names `2 * n`) for recursive input positions
   (`μ` at target polarity `−`, `ν` at `+`) and proves `Encode` and `EncodedDecl`.
3. **Pattern & Copattern Spine Inference (`inferPatB`, `inferSpineB`)**:
   Introduces fresh bounded rigid size variables (`j < a`) at constructor patterns and
   coinductive projections, and fresh type variables at polymorphic copatterns.
4. **Type Comparison with β-Reduction & Functor Variance (`compareTyB2`)**:
   Generates size subtyping constraints (`a ≤ b^↑`), reducing type-level β-redexes and
   separating positive functors (`mu_pos`, `nu_pos`) from mixed-variance functors
   (`mu_eqv`, `nu_eqv`).
5. **Bidirectional Term & Clause Inference (`inferTmB`, `checkTmB`, `checkClauseB`)**:
   Allocates fresh flexible size variables (odd names `2 * n + 1`), collects size constraints
   and call records, and feeds them to Algorithm 1 (`solve`) and the post-checks
   (`checkScope`, `checkCoherent`).
6. **Certified Size-Change Termination Checker (`checkSCTB`, `checkBlockB`)**:
   Computes the transitive closure of the block's invocation graphs, certifies closure under
   base graphs and composition, and checks that every idempotent self-loop `G = G ∘ G` has
   a strict `<` diagonal edge (`SCTValid`).
-/

namespace MiniLeanSized

open NishtAbel2024V5
open NishtAbel2024V2 (InvGraph InvGraphFamily InvGraphClosure SCTValid ConformsToGraph FunName EdgeRel)

/-! ## Part 1: Fresh Name Generation & List Helpers -/

/-- Maximum element of a list of natural numbers (`0` on `[]`). -/
def listMax : List Nat → Nat
  | [] => 0
  | x :: xs => max x (listMax xs)

theorem le_listMax {x : Nat} {L : List Nat} (h : x ∈ L) : x ≤ listMax L := by
  induction L with
  | nil => simp at h
  | cons y ys ih =>
    simp only [listMax]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- A fresh natural number strictly greater than all elements in `L`. -/
def freshVar (L : List Nat) : Nat := listMax L + 1

theorem freshVar_not_mem (L : List Nat) : freshVar L ∉ L := by
  intro h
  have := le_listMax h
  unfold freshVar at this
  omega

/-- A fresh even natural number (`RigidName`) strictly greater than all elements in `L`. -/
def freshEven (L : List Nat) : Nat := 2 * (listMax L + 1)

theorem freshEven_rigid (L : List Nat) : RigidName (freshEven L) := by
  unfold RigidName freshEven
  omega

theorem freshEven_not_mem (L : List Nat) : freshEven L ∉ L := by
  intro h
  have := le_listMax h
  unfold freshEven at this
  omega

/-- Maps counter `n` to an odd flexible name (`2 * n + 1`) when `isFlex = true`,
or an even rigid name (`2 * n`) when `isFlex = false`. -/
def mkName (isFlex : Bool) (n : Nat) : Nat :=
  if isFlex then 2 * n + 1 else 2 * n

/-- Predicate corresponding to `isFlex`. -/
def nameOk (isFlex : Bool) : Nat → Prop :=
  if isFlex then FlexName else RigidName

theorem mkName_ok (isFlex : Bool) (n : Nat) : nameOk isFlex (mkName isFlex n) := by
  cases isFlex <;> simp [nameOk, mkName, FlexName, RigidName]

theorem mkName_lt_iff (isFlex : Bool) {a b : Nat} :
    mkName isFlex a < mkName isFlex b ↔ a < b := by
  cases isFlex <;> simp [mkName]

theorem mkName_le_iff (isFlex : Bool) {a b : Nat} :
    mkName isFlex a ≤ mkName isFlex b ↔ a ≤ b := by
  cases isFlex <;> (dsimp [mkName]; omega)

/-- Computable duplicate-free check on `List Nat`. -/
def nodupB : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

theorem nodupB_sound : ∀ {L : List Nat}, nodupB L = true → L.Nodup
  | [], _ => .nil
  | _ :: _, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    exact List.nodup_cons.mpr ⟨h.1, nodupB_sound h.2⟩

/-! ## Part 2: Executable `Unsized` Checker -/

mutual

/-- Executable check that a type is size-free (`Unsized`). -/
def unsizedB : Ty → Bool
  | .unit => true
  | .prod A B => unsizedB A && unsizedB B
  | .arr A B => unsizedB A && unsizedB B
  | .var _ => true
  | .fvar _ => true
  | .lam _ F => unsizedB F
  | .app F G _ => unsizedB F && unsizedB G
  | .mu a S =>
    match a with
    | .inf 0 => unsizedListB S
    | _ => false
  | .nu a R =>
    match a with
    | .inf 0 => unsizedListB R
    | _ => false
  | .allT _ B => unsizedB B
  | .exT _ B => unsizedB B
  | .allS _ _ => false
  | .exS _ _ => false

/-- Executable check that a list of types is size-free (`UnsizedList`). -/
def unsizedListB : List Ty → Bool
  | [] => true
  | T :: S => unsizedB T && unsizedListB S

end

mutual

theorem unsizedB_sound : ∀ {A : Ty}, unsizedB A = true → Unsized A
  | .unit, _ => .unit
  | .prod _ _, h => by
    simp only [unsizedB, Bool.and_eq_true] at h
    exact .prod (unsizedB_sound h.1) (unsizedB_sound h.2)
  | .arr _ _, h => by
    simp only [unsizedB, Bool.and_eq_true] at h
    exact .arr (unsizedB_sound h.1) (unsizedB_sound h.2)
  | .var k, _ => .var k
  | .fvar X, _ => .fvar X
  | .lam _ _, h => .lam (unsizedB_sound h)
  | .app _ _ _, h => by
    simp only [unsizedB, Bool.and_eq_true] at h
    exact .app (unsizedB_sound h.1) (unsizedB_sound h.2)
  | .mu a S, h => by
    unfold unsizedB at h
    cases a with
    | inf m =>
      cases m with
      | zero => exact .mu (unsizedListB_sound h)
      | succ _ => simp at h
    | _ => simp at h
  | .nu a R, h => by
    unfold unsizedB at h
    cases a with
    | inf m =>
      cases m with
      | zero => exact .nu (unsizedListB_sound h)
      | succ _ => simp at h
    | _ => simp at h
  | .allT _ _, h => .allT (unsizedB_sound h)
  | .exT _ _, h => .exT (unsizedB_sound h)
  | .allS _ _, h => by simp [unsizedB] at h
  | .exS _ _, h => by simp [unsizedB] at h

theorem unsizedListB_sound : ∀ {S : List Ty}, unsizedListB S = true → UnsizedList S
  | [], _ => .nil
  | _ :: _, h => by
    simp only [unsizedListB, Bool.and_eq_true] at h
    exact .cons (unsizedB_sound h.1) (unsizedListB_sound h.2)

end

/-! ## Part 3: Executable Kind Checker (`inferKindB`, `checkKindB`, `ekindingB`) -/

/-- Executable polarity ordering `π₁ ≤ π₂`. -/
def polLeB : Pol → Pol → Bool
  | .mix, _ => true
  | .pos, .pos => true
  | .pos, .top => true
  | .neg, .neg => true
  | .neg, .top => true
  | .top, .top => true
  | _, _ => false

theorem polLeB_sound {π₁ π₂ : Pol} (h : polLeB π₁ π₂ = true) : Pol.le π₁ π₂ := by
  cases π₁ <;> cases π₂ <;> simp [polLeB, Pol.le] at h ⊢

/-- Executable usability check `π ≤ +`. -/
def polUsableB (π : Pol) : Bool := polLeB π .pos

theorem polUsableB_sound {π : Pol} (h : polUsableB π = true) : π.Usable :=
  polLeB_sound h

/-- Structurally recursive directional subkinding check:
`dir = false` checks `κ₁ ≤ κ₂`; `dir = true` checks `κ₂ ≤ κ₁`. -/
def subKindDirB : Bool → Kind → Kind → Bool
  | _, .star, .star => true
  | false, .arr π a₁ a₂, .arr π' b₁ b₂ =>
    polLeB π' π && subKindDirB true a₁ b₁ && subKindDirB false a₂ b₂
  | true, .arr π a₁ a₂, .arr π' b₁ b₂ =>
    polLeB π π' && subKindDirB false a₁ b₁ && subKindDirB true a₂ b₂
  | _, _, _ => false

/-- Executable subkinding check `κ₁ ≤ κ₂`. -/
def subKindB (κ₁ κ₂ : Kind) : Bool := subKindDirB false κ₁ κ₂

theorem subKindDirB_sound :
    ∀ (κ₁ κ₂ : Kind),
      (subKindDirB false κ₁ κ₂ = true → SubKind κ₁ κ₂) ∧
      (subKindDirB true κ₁ κ₂ = true → SubKind κ₂ κ₁)
  | .star, .star => ⟨fun _ => .star, fun _ => .star⟩
  | .star, .arr _ _ _ => ⟨fun h => by simp [subKindDirB] at h, fun h => by simp [subKindDirB] at h⟩
  | .arr _ _ _, .star => ⟨fun h => by simp [subKindDirB] at h, fun h => by simp [subKindDirB] at h⟩
  | .arr π a₁ a₂, .arr π' b₁ b₂ => by
    obtain ⟨ih₁f, ih₁t⟩ := subKindDirB_sound a₁ b₁
    obtain ⟨ih₂f, ih₂t⟩ := subKindDirB_sound a₂ b₂
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [subKindDirB, Bool.and_eq_true] at h
      exact .arr (polLeB_sound h.1.1) (ih₁t h.1.2) (ih₂f h.2)
    · simp only [subKindDirB, Bool.and_eq_true] at h
      exact .arr (polLeB_sound h.1.1) (ih₁f h.1.2) (ih₂t h.2)

theorem subKindB_sound {κ₁ κ₂ : Kind} (h : subKindB κ₁ κ₂ = true) : SubKind κ₁ κ₂ :=
  (subKindDirB_sound κ₁ κ₂).1 h

/-- Executable size well-formedness check at binder depth `m`. -/
def sizeWfAtB (Ψ : SizeCtx) (m : Nat) : Size → Bool
  | .inf _ => true
  | .var i _ => Ψ.dom.contains i
  | .bvar k _ => decide (k < m)
  | .meet a b => sizeWfAtB Ψ m a && sizeWfAtB Ψ m b

theorem sizeWfAtB_sound {Ψ : SizeCtx} {m : Nat} :
    ∀ {a : Size}, sizeWfAtB Ψ m a = true → SizeWfAt Ψ m a
  | .inf _, _ => trivial
  | .var i _, h => by simpa [sizeWfAtB, SizeWfAt] using h
  | .bvar k _, h => by simpa [sizeWfAtB, SizeWfAt] using h
  | .meet _ _, h => by
    simp only [sizeWfAtB, Bool.and_eq_true] at h
    exact ⟨sizeWfAtB_sound h.1, sizeWfAtB_sound h.2⟩

/-- Pointwise kinding of a list of constructor/destructor functors. -/
def KindingList (Ψ : SizeCtx) (Δ : KCtx) (Δb : BCtx) (m : Nat) : List Ty → Prop
  | [] => True
  | T :: S => Kinding Ψ Δ Δb m T .star ∧ KindingList Ψ Δ Δb m S

theorem KindingList.forall_mem {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} :
    ∀ {S : List Ty}, KindingList Ψ Δ Δb m S → ∀ T ∈ S, Kinding Ψ Δ Δb m T .star
  | [], _, _, hT => by simp at hT
  | _ :: _, ⟨h₁, h₂⟩, _, hT => by
    rcases List.mem_cons.mp hT with rfl | hT
    · exact h₁
    · exact h₂.forall_mem _ hT

mutual

/-- Structural kind synthesis for types. -/
def inferKindB (Ψ : SizeCtx) (Δ : KCtx) (Δb : BCtx) (m : Nat) : Ty → Option Kind
  | .unit => some .star
  | .prod A B =>
    if checkKindB Ψ Δ Δb m A .star && checkKindB Ψ Δ Δb m B .star then some .star else none
  | .arr A B =>
    if checkKindB Ψ (Δ.inv .neg) (Δb.inv .neg) m A .star && checkKindB Ψ Δ Δb m B .star then
      some .star
    else none
  | .var k =>
    match Δb[k]? with
    | some p => if polUsableB p.1 then some p.2 else none
    | none => none
  | .fvar X =>
    match Δ.lookup X with
    | some p => if polUsableB p.1 then some p.2 else none
    | none => none
  | .lam ι F =>
    let κ₁ := Kind.ofSKind ι
    match inferKindB Ψ Δ ((.pos, κ₁) :: Δb) m F with
    | some κ₂ => some (.arr .pos κ₁ κ₂)
    | none =>
      match inferKindB Ψ Δ ((.neg, κ₁) :: Δb) m F with
      | some κ₂ => some (.arr .neg κ₁ κ₂)
      | none =>
        match inferKindB Ψ Δ ((.mix, κ₁) :: Δb) m F with
        | some κ₂ => some (.arr .mix κ₁ κ₂)
        | none => none
  | .app F G ι =>
    match inferKindB Ψ Δ Δb m F with
    | some (.arr π κ₁ κ₂) =>
      if decide (κ₁.erase = ι) && checkKindB Ψ (Δ.inv π) (Δb.inv π) m G κ₁ then some κ₂ else none
    | _ => none
  | .mu a S =>
    if sizeWfAtB Ψ m a then
      if checkKindListB Ψ (Δ.inv .pos) ((.pos, .star) :: Δb.inv .pos) m S then some .star
      else if checkKindListB Ψ (Δ.inv .mix) ((.mix, .star) :: Δb.inv .mix) m S then some .star
      else none
    else none
  | .nu a R =>
    if sizeWfAtB Ψ m a then
      if checkKindListB Ψ (Δ.inv .pos) ((.pos, .star) :: Δb.inv .pos) m R then some .star
      else if checkKindListB Ψ (Δ.inv .mix) ((.mix, .star) :: Δb.inv .mix) m R then some .star
      else none
    else none
  | .allT κ B =>
    if checkKindB Ψ Δ ((.mix, κ) :: Δb) m B .star then some .star else none
  | .exT κ B =>
    if checkKindB Ψ Δ ((.mix, κ) :: Δb) m B .star then some .star else none
  | .allS a B =>
    if sizeWfAtB Ψ m a && checkKindB Ψ Δ Δb (m + 1) B .star then some .star else none
  | .exS a B =>
    if sizeWfAtB Ψ m a && checkKindB Ψ Δ Δb (m + 1) B .star then some .star else none

/-- Structural kind checking for types against a target kind `κ`. -/
def checkKindB (Ψ : SizeCtx) (Δ : KCtx) (Δb : BCtx) (m : Nat) : Ty → Kind → Bool
  | .unit, κ => subKindB .star κ
  | .prod A B, κ =>
    subKindB .star κ && checkKindB Ψ Δ Δb m A .star && checkKindB Ψ Δ Δb m B .star
  | .arr A B, κ =>
    subKindB .star κ &&
      checkKindB Ψ (Δ.inv .neg) (Δb.inv .neg) m A .star &&
      checkKindB Ψ Δ Δb m B .star
  | .var k, κ =>
    match Δb[k]? with
    | some p => polUsableB p.1 && subKindB p.2 κ
    | none => false
  | .fvar X, κ =>
    match Δ.lookup X with
    | some p => polUsableB p.1 && subKindB p.2 κ
    | none => false
  | .lam ι F, κ =>
    match κ with
    | .arr π κ₁ κ₂ => decide (κ₁.erase = ι) && checkKindB Ψ Δ ((π, κ₁) :: Δb) m F κ₂
    | .star => false
  | .app F G ι, κ =>
    match inferKindB Ψ Δ Δb m F with
    | some (.arr π κ₁ κ₂) =>
      decide (κ₁.erase = ι) && checkKindB Ψ (Δ.inv π) (Δb.inv π) m G κ₁ && subKindB κ₂ κ
    | _ => false
  | .mu a S, κ =>
    subKindB .star κ && sizeWfAtB Ψ m a &&
      (checkKindListB Ψ (Δ.inv .pos) ((.pos, .star) :: Δb.inv .pos) m S ||
       checkKindListB Ψ (Δ.inv .mix) ((.mix, .star) :: Δb.inv .mix) m S)
  | .nu a R, κ =>
    subKindB .star κ && sizeWfAtB Ψ m a &&
      (checkKindListB Ψ (Δ.inv .pos) ((.pos, .star) :: Δb.inv .pos) m R ||
       checkKindListB Ψ (Δ.inv .mix) ((.mix, .star) :: Δb.inv .mix) m R)
  | .allT κ₁ B, κ =>
    subKindB .star κ && checkKindB Ψ Δ ((.mix, κ₁) :: Δb) m B .star
  | .exT κ₁ B, κ =>
    subKindB .star κ && checkKindB Ψ Δ ((.mix, κ₁) :: Δb) m B .star
  | .allS a B, κ =>
    subKindB .star κ && sizeWfAtB Ψ m a && checkKindB Ψ Δ Δb (m + 1) B .star
  | .exS a B, κ =>
    subKindB .star κ && sizeWfAtB Ψ m a && checkKindB Ψ Δ Δb (m + 1) B .star

/-- Structural kind checking for a list of constructor/destructor functors. -/
def checkKindListB (Ψ : SizeCtx) (Δ : KCtx) (Δb : BCtx) (m : Nat) : List Ty → Bool
  | [] => true
  | T :: S => checkKindB Ψ Δ Δb m T .star && checkKindListB Ψ Δ Δb m S

end

theorem erase_ofSKind : ∀ (ι : SKind), (Kind.ofSKind ι).erase = ι
  | .star => rfl
  | .arr ι₁ ι₂ => by simp [Kind.ofSKind, erase_ofSKind ι₁, erase_ofSKind ι₂]

mutual

theorem inferKindB_sound (Ψ : SizeCtx) (Δ : KCtx) (Δb : BCtx) (m : Nat) :
    ∀ (A : Ty) {κ : Kind}, inferKindB Ψ Δ Δb m A = some κ → Kinding Ψ Δ Δb m A κ
  | .unit, _, h => by
    simp only [inferKindB, Option.some.injEq] at h
    subst h; exact .unit
  | .prod A B, _, h => by
    unfold inferKindB at h
    split at h
    · rename_i hboth
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true] at hboth
      exact .prod (checkKindB_sound Ψ Δ Δb m A hboth.1) (checkKindB_sound Ψ Δ Δb m B hboth.2)
    · simp at h
  | .arr A B, _, h => by
    unfold inferKindB at h
    split at h
    · rename_i hboth
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true] at hboth
      exact .arr (checkKindB_sound Ψ (Δ.inv .neg) (Δb.inv .neg) m A hboth.1)
        (checkKindB_sound Ψ Δ Δb m B hboth.2)
    · simp at h
  | .var k, _, h => by
    unfold inferKindB at h
    cases hlk : Δb[k]? with
    | none => simp [hlk] at h
    | some p =>
      rcases p with ⟨π, κ₀⟩
      simp only [hlk] at h
      split at h
      · rename_i hus
        simp only [Option.some.injEq] at h; subst h
        exact .var hlk (polUsableB_sound hus)
      · simp at h
  | .fvar X, _, h => by
    unfold inferKindB at h
    cases hlk : Δ.lookup X with
    | none => simp [hlk] at h
    | some p =>
      rcases p with ⟨π, κ₀⟩
      simp only [hlk] at h
      split at h
      · rename_i hus
        simp only [Option.some.injEq] at h; subst h
        exact .fvar hlk (polUsableB_sound hus)
      · simp at h
  | .lam ι F, _, h => by
    unfold inferKindB at h
    dsimp only at h
    split at h
    · rename_i κ₂ hF
      simp only [Option.some.injEq] at h; subst h
      exact .lam (erase_ofSKind ι) (inferKindB_sound Ψ Δ ((.pos, Kind.ofSKind ι) :: Δb) m F hF)
    · split at h
      · rename_i κ₂ hF
        simp only [Option.some.injEq] at h; subst h
        exact .lam (erase_ofSKind ι) (inferKindB_sound Ψ Δ ((.neg, Kind.ofSKind ι) :: Δb) m F hF)
      · split at h
        · rename_i κ₂ hF
          simp only [Option.some.injEq] at h; subst h
          exact .lam (erase_ofSKind ι) (inferKindB_sound Ψ Δ ((.mix, Kind.ofSKind ι) :: Δb) m F hF)
        · simp at h
  | .app F G ι, _, h => by
    unfold inferKindB at h
    split at h
    · rename_i π κ₁ κ₂ hF
      split at h
      · rename_i hG
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
        exact .app (inferKindB_sound Ψ Δ Δb m F hF)
          (checkKindB_sound Ψ (Δ.inv π) (Δb.inv π) m G hG.2) hG.1
      · simp at h
    · simp at h
  | .mu a S, _, h => by
    unfold inferKindB at h
    split at h
    · rename_i ha
      split at h
      · rename_i hpos
        simp only [Option.some.injEq] at h; subst h
        exact .mu (Or.inl rfl) (sizeWfAtB_sound ha)
          (checkKindListB_sound Ψ (Δ.inv .pos) ((.pos, .star) :: Δb.inv .pos) m S hpos).forall_mem
      · split at h
        · rename_i hmix
          simp only [Option.some.injEq] at h; subst h
          exact .mu (Or.inr rfl) (sizeWfAtB_sound ha)
            (checkKindListB_sound Ψ (Δ.inv .mix) ((.mix, .star) :: Δb.inv .mix) m S hmix).forall_mem
        · simp at h
    · simp at h
  | .nu a R, _, h => by
    unfold inferKindB at h
    split at h
    · rename_i ha
      split at h
      · rename_i hpos
        simp only [Option.some.injEq] at h; subst h
        exact .nu (Or.inl rfl) (sizeWfAtB_sound ha)
          (checkKindListB_sound Ψ (Δ.inv .pos) ((.pos, .star) :: Δb.inv .pos) m R hpos).forall_mem
      · split at h
        · rename_i hmix
          simp only [Option.some.injEq] at h; subst h
          exact .nu (Or.inr rfl) (sizeWfAtB_sound ha)
            (checkKindListB_sound Ψ (Δ.inv .mix) ((.mix, .star) :: Δb.inv .mix) m R hmix).forall_mem
        · simp at h
    · simp at h
  | .allT κ₁ B, _, h => by
    unfold inferKindB at h
    split at h
    · rename_i hB
      simp only [Option.some.injEq] at h; subst h
      exact .allT (checkKindB_sound Ψ Δ ((.mix, κ₁) :: Δb) m B hB)
    · simp at h
  | .exT κ₁ B, _, h => by
    unfold inferKindB at h
    split at h
    · rename_i hB
      simp only [Option.some.injEq] at h; subst h
      exact .exT (checkKindB_sound Ψ Δ ((.mix, κ₁) :: Δb) m B hB)
    · simp at h
  | .allS a B, _, h => by
    unfold inferKindB at h
    split at h
    · rename_i hB
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true] at hB
      exact .allS (sizeWfAtB_sound hB.1) (checkKindB_sound Ψ Δ Δb (m + 1) B hB.2)
    · simp at h
  | .exS a B, _, h => by
    unfold inferKindB at h
    split at h
    · rename_i hB
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true] at hB
      exact .exS (sizeWfAtB_sound hB.1) (checkKindB_sound Ψ Δ Δb (m + 1) B hB.2)
    · simp at h

theorem checkKindB_sound (Ψ : SizeCtx) (Δ : KCtx) (Δb : BCtx) (m : Nat) :
    ∀ (A : Ty) {κ : Kind}, checkKindB Ψ Δ Δb m A κ = true → Kinding Ψ Δ Δb m A κ
  | .unit, _, h => .sub .unit (subKindB_sound h)
  | .prod A B, _, h => by
    simp only [checkKindB, Bool.and_eq_true] at h
    exact .sub (.prod (checkKindB_sound Ψ Δ Δb m A h.1.2) (checkKindB_sound Ψ Δ Δb m B h.2))
      (subKindB_sound h.1.1)
  | .arr A B, _, h => by
    simp only [checkKindB, Bool.and_eq_true] at h
    exact .sub (.arr (checkKindB_sound Ψ (Δ.inv .neg) (Δb.inv .neg) m A h.1.2)
      (checkKindB_sound Ψ Δ Δb m B h.2)) (subKindB_sound h.1.1)
  | .var k, _, h => by
    unfold checkKindB at h
    cases hlk : Δb[k]? with
    | none => simp [hlk] at h
    | some p =>
      rcases p with ⟨π, κ₀⟩
      simp only [hlk, Bool.and_eq_true] at h
      exact .sub (.var hlk (polUsableB_sound h.1)) (subKindB_sound h.2)
  | .fvar X, _, h => by
    unfold checkKindB at h
    cases hlk : Δ.lookup X with
    | none => simp [hlk] at h
    | some p =>
      rcases p with ⟨π, κ₀⟩
      simp only [hlk, Bool.and_eq_true] at h
      exact .sub (.fvar hlk (polUsableB_sound h.1)) (subKindB_sound h.2)
  | .lam ι F, κ, h => by
    unfold checkKindB at h
    cases κ with
    | star => simp at h
    | arr π κ₁ κ₂ =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact .lam h.1 (checkKindB_sound Ψ Δ ((π, κ₁) :: Δb) m F h.2)
  | .app F G ι, _, h => by
    unfold checkKindB at h
    split at h
    · rename_i π κ₁ κ₂ hF
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact .sub (.app (inferKindB_sound Ψ Δ Δb m F hF)
        (checkKindB_sound Ψ (Δ.inv π) (Δb.inv π) m G h.1.2) h.1.1) (subKindB_sound h.2)
    · simp at h
  | .mu a S, _, h => by
    simp only [checkKindB, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h.2 with hpos | hmix
    · exact .sub (.mu (Or.inl rfl) (sizeWfAtB_sound h.1.2)
        (checkKindListB_sound Ψ (Δ.inv .pos) ((.pos, .star) :: Δb.inv .pos) m S hpos).forall_mem)
        (subKindB_sound h.1.1)
    · exact .sub (.mu (Or.inr rfl) (sizeWfAtB_sound h.1.2)
        (checkKindListB_sound Ψ (Δ.inv .mix) ((.mix, .star) :: Δb.inv .mix) m S hmix).forall_mem)
        (subKindB_sound h.1.1)
  | .nu a R, _, h => by
    simp only [checkKindB, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h.2 with hpos | hmix
    · exact .sub (.nu (Or.inl rfl) (sizeWfAtB_sound h.1.2)
        (checkKindListB_sound Ψ (Δ.inv .pos) ((.pos, .star) :: Δb.inv .pos) m R hpos).forall_mem)
        (subKindB_sound h.1.1)
    · exact .sub (.nu (Or.inr rfl) (sizeWfAtB_sound h.1.2)
        (checkKindListB_sound Ψ (Δ.inv .mix) ((.mix, .star) :: Δb.inv .mix) m R hmix).forall_mem)
        (subKindB_sound h.1.1)
  | .allT κ₁ B, _, h => by
    simp only [checkKindB, Bool.and_eq_true] at h
    exact .sub (.allT (checkKindB_sound Ψ Δ ((.mix, κ₁) :: Δb) m B h.2)) (subKindB_sound h.1)
  | .exT κ₁ B, _, h => by
    simp only [checkKindB, Bool.and_eq_true] at h
    exact .sub (.exT (checkKindB_sound Ψ Δ ((.mix, κ₁) :: Δb) m B h.2)) (subKindB_sound h.1)
  | .allS a B, _, h => by
    simp only [checkKindB, Bool.and_eq_true] at h
    exact .sub (.allS (sizeWfAtB_sound h.1.2) (checkKindB_sound Ψ Δ Δb (m + 1) B h.2))
      (subKindB_sound h.1.1)
  | .exS a B, _, h => by
    simp only [checkKindB, Bool.and_eq_true] at h
    exact .sub (.exS (sizeWfAtB_sound h.1.2) (checkKindB_sound Ψ Δ Δb (m + 1) B h.2))
      (subKindB_sound h.1.1)

theorem checkKindListB_sound (Ψ : SizeCtx) (Δ : KCtx) (Δb : BCtx) (m : Nat) :
    ∀ (S : List Ty), checkKindListB Ψ Δ Δb m S = true → KindingList Ψ Δ Δb m S
  | [], _ => trivial
  | T :: S, h => by
    simp only [checkKindListB, Bool.and_eq_true] at h
    exact ⟨checkKindB_sound Ψ Δ Δb m T h.1, checkKindListB_sound Ψ Δ Δb m S h.2⟩

end

/-- Executable size-erased kinding check (`EKinding Δ Δb A κ`). -/
def ekindingB (Δ : KCtx) (Δb : BCtx) (A : Ty) (κ : Kind) : Bool :=
  checkKindB [] Δ Δb 0 A.eraseSz κ

theorem ekindingB_sound {Δ : KCtx} {Δb : BCtx} {A : Ty} {κ : Kind}
    (h : ekindingB Δ Δb A κ = true) : EKinding Δ Δb A κ :=
  checkKindB_sound [] Δ Δb 0 A.eraseSz h

/-- Executable check that all functors in `S` are positive (`∀ T ∈ S, EKinding Δ [(.pos, .star)] T .star`). -/
def allPosFunctorsB (Δ : KCtx) : List Ty → Bool
  | [] => true
  | T :: S => ekindingB Δ [(.pos, .star)] T .star && allPosFunctorsB Δ S

theorem allPosFunctorsB_sound {Δ : KCtx} :
    ∀ {S : List Ty}, allPosFunctorsB Δ S = true → ∀ T ∈ S, EKinding Δ [(.pos, .star)] T .star
  | [], _, _, hT => by simp at hT
  | _ :: _, h, _, hT => by
    simp only [allPosFunctorsB, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hT with rfl | hT
    · exact ekindingB_sound h.1
    · exact allPosFunctorsB_sound h.2 _ hT

/-! ## Part 4: Executable Signature & Type-Argument Encoding (`encodeTyB`) -/

mutual

/-- Executable signature & type-argument encoder (`Encode`).
Allocates fresh names `mkName isFlex m` for `n ≤ m < n'`. -/
def encodeTyB (isFlex : Bool) (πs π : Pol) (Δ : KCtx) (Δb : BCtx) :
    Ty → Nat → Option (SizeCtx × Ty × Nat)
  | .unit, n => some ([], .unit, n)
  | .prod A B, n =>
    match encodeTyB isFlex πs π Δ Δb A n with
    | some (Ψ₁, A', n₁) =>
      match encodeTyB isFlex πs π Δ Δb B n₁ with
      | some (Ψ₂, B', n₂) => some (Ψ₁ ++ Ψ₂, .prod A' B', n₂)
      | none => none
    | none => none
  | .arr A B, n =>
    match encodeTyB isFlex πs π.negate Δ Δb A n with
    | some (Ψ₁, A', n₁) =>
      match encodeTyB isFlex πs π Δ Δb B n₁ with
      | some (Ψ₂, B', n₂) => some (Ψ₁ ++ Ψ₂, .arr A' B', n₂)
      | none => none
    | none => none
  | .var k, n => some ([], .var k, n)
  | .fvar X, n => some ([], .fvar X, n)
  | .lam ι F, n =>
    match encodeTyB isFlex πs π Δ ((.mix, Kind.ofSKind ι) :: Δb) F n with
    | some (Ψ, F', n') => some (Ψ, .lam ι F', n')
    | none => none
  | .app F G ι, n =>
    match inferKindB [] Δ Δb 0 F with
    | some (.arr π' _ _) =>
      match encodeTyB isFlex πs π Δ Δb F n with
      | some (Ψ₁, F', n₁) =>
        match encodeTyB isFlex πs (Pol.comp π' π) Δ Δb G n₁ with
        | some (Ψ₂, G', n₂) => some (Ψ₁ ++ Ψ₂, .app F' G' ι, n₂)
        | none => none
      | none => none
    | _ => none
  | .mu a S, n =>
    match a with
    | .inf 0 =>
      if decide (π = πs) then
        let i := mkName isFlex n
        match encodeTyListB isFlex πs π Δ ((.mix, .star) :: Δb) S (n + 1) with
        | some (Ψ, S', n') => some ((i, .inf 0) :: Ψ, .mu (.var i 0) S', n')
        | none => none
      else
        match encodeTyListB isFlex πs π Δ ((.mix, .star) :: Δb) S n with
        | some (Ψ, S', n') => some (Ψ, .mu (.inf 0) S', n')
        | none => none
    | _ => none
  | .nu a R, n =>
    match a with
    | .inf 0 =>
      if decide (π = πs.negate) then
        let i := mkName isFlex n
        match encodeTyListB isFlex πs π Δ ((.mix, .star) :: Δb) R (n + 1) with
        | some (Ψ, R', n') => some ((i, .inf 0) :: Ψ, .nu (.var i 0) R', n')
        | none => none
      else
        match encodeTyListB isFlex πs π Δ ((.mix, .star) :: Δb) R n with
        | some (Ψ, R', n') => some (Ψ, .nu (.inf 0) R', n')
        | none => none
    | _ => none
  | .allT κ B, n =>
    match encodeTyB isFlex πs π Δ ((.mix, κ) :: Δb) B n with
    | some (Ψ, B', n') => some (Ψ, .allT κ B', n')
    | none => none
  | .exT κ B, n =>
    match encodeTyB isFlex πs π Δ ((.mix, κ) :: Δb) B n with
    | some (Ψ, B', n') => some (Ψ, .exT κ B', n')
    | none => none
  | .allS _ _, _ => none
  | .exS _ _, _ => none

/-- Executable functor list encoder (`EncodeList`). -/
def encodeTyListB (isFlex : Bool) (πs π : Pol) (Δ : KCtx) (Δb : BCtx) :
    List Ty → Nat → Option (SizeCtx × List Ty × Nat)
  | [], n => some ([], [], n)
  | T :: S, n =>
    match encodeTyB isFlex πs π Δ Δb T n with
    | some (Ψ₁, T', n₁) =>
      match encodeTyListB isFlex πs π Δ Δb S n₁ with
      | some (Ψ₂, S', n₂) => some (Ψ₁ ++ Ψ₂, T' :: S', n₂)
      | none => none
    | none => none

end

/-- Range invariant for fresh size contexts generated by `encodeTyB`. -/
def DomInRange (isFlex : Bool) (n n' : Nat) (Ψ : SizeCtx) : Prop :=
  n ≤ n' ∧ ∀ x ∈ Ψ.dom, mkName isFlex n ≤ x ∧ x < mkName isFlex n'

theorem DomInRange.refl (isFlex : Bool) (n : Nat) : DomInRange isFlex n n [] :=
  ⟨Nat.le_refl n, fun _ hx => by simp [SizeCtx.dom] at hx⟩

theorem DomInRange.disjoint {isFlex : Bool} {n n₁ n₂ : Nat} {Ψ₁ Ψ₂ : SizeCtx}
    (h₁ : DomInRange isFlex n n₁ Ψ₁) (h₂ : DomInRange isFlex n₁ n₂ Ψ₂) :
    NamesDisjoint Ψ₁.dom Ψ₂.dom := by
  intro x hx₁ hx₂
  have := (h₁.2 x hx₁).2
  have := (h₂.2 x hx₂).1
  omega

theorem DomInRange.append {isFlex : Bool} {n n₁ n₂ : Nat} {Ψ₁ Ψ₂ : SizeCtx}
    (h₁ : DomInRange isFlex n n₁ Ψ₁) (h₂ : DomInRange isFlex n₁ n₂ Ψ₂) :
    DomInRange isFlex n n₂ (Ψ₁ ++ Ψ₂) := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun x hx => ?_⟩
  simp only [SizeCtx.dom, List.map_append, List.mem_append] at hx
  rcases hx with hx | hx
  · have ⟨hle, hlt⟩ := h₁.2 x hx
    have hn : mkName isFlex n₁ ≤ mkName isFlex n₂ := (mkName_le_iff isFlex).mpr h₂.1
    exact ⟨hle, Nat.lt_of_lt_of_le hlt hn⟩
  · have ⟨hle, hlt⟩ := h₂.2 x hx
    have hn : mkName isFlex n ≤ mkName isFlex n₁ := (mkName_le_iff isFlex).mpr h₁.1
    exact ⟨Nat.le_trans hn hle, hlt⟩

theorem DomInRange.not_mem_head {isFlex : Bool} {n n' : Nat} {Ψ : SizeCtx}
    (h : DomInRange isFlex (n + 1) n' Ψ) : mkName isFlex n ∉ Ψ.dom := by
  intro hx
  have hle := (h.2 _ hx).1
  have hlt : mkName isFlex n < mkName isFlex (n + 1) := (mkName_lt_iff isFlex).mpr (by omega)
  omega

theorem DomInRange.cons_head {isFlex : Bool} {n n' : Nat} {Ψ : SizeCtx} {a : Size}
    (h : DomInRange isFlex (n + 1) n' Ψ) :
    DomInRange isFlex n n' ((mkName isFlex n, a) :: Ψ) := by
  refine ⟨Nat.le_of_succ_le h.1, fun x hx => ?_⟩
  simp only [SizeCtx.dom, List.map_cons, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact ⟨Nat.le_refl _, (mkName_lt_iff isFlex).mpr h.1⟩
  · have ⟨hle, hlt⟩ := h.2 x hx
    have hn : mkName isFlex n ≤ mkName isFlex (n + 1) := (mkName_le_iff isFlex).mpr (by omega)
    exact ⟨Nat.le_trans hn hle, hlt⟩

mutual

theorem encodeTyB_sound (isFlex : Bool) (πs : Pol) :
    ∀ (π : Pol) (Δ : KCtx) (Δb : BCtx) (A : Ty) (n : Nat) {Ψ : SizeCtx} {A' : Ty} {n' : Nat},
      encodeTyB isFlex πs π Δ Δb A n = some (Ψ, A', n') →
      Encode πs (nameOk isFlex) π Δ Δb A Ψ A' ∧ DomInRange isFlex n n' Ψ
  | π, Δ, Δb, .unit, n, _, _, _, h => by
    simp only [encodeTyB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.unit, DomInRange.refl isFlex n⟩
  | π, Δ, Δb, .prod A B, n, _, _, _, h => by
    unfold encodeTyB at h
    split at h
    · rename_i Ψ₁ A' n₁ h₁
      split at h
      · rename_i Ψ₂ B' n₂ h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨he₁, hr₁⟩ := encodeTyB_sound isFlex πs π Δ Δb A n h₁
        obtain ⟨he₂, hr₂⟩ := encodeTyB_sound isFlex πs π Δ Δb B n₁ h₂
        exact ⟨.prod he₁ he₂ (hr₁.disjoint hr₂), hr₁.append hr₂⟩
      · simp at h
    · simp at h
  | π, Δ, Δb, .arr A B, n, _, _, _, h => by
    unfold encodeTyB at h
    split at h
    · rename_i Ψ₁ A' n₁ h₁
      split at h
      · rename_i Ψ₂ B' n₂ h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨he₁, hr₁⟩ := encodeTyB_sound isFlex πs π.negate Δ Δb A n h₁
        obtain ⟨he₂, hr₂⟩ := encodeTyB_sound isFlex πs π Δ Δb B n₁ h₂
        exact ⟨.arr he₁ he₂ (hr₁.disjoint hr₂), hr₁.append hr₂⟩
      · simp at h
    · simp at h
  | π, Δ, Δb, .var k, n, _, _, _, h => by
    simp only [encodeTyB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.var k, DomInRange.refl isFlex n⟩
  | π, Δ, Δb, .fvar X, n, _, _, _, h => by
    simp only [encodeTyB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.fvar X, DomInRange.refl isFlex n⟩
  | π, Δ, Δb, .lam ι F, n, _, _, _, h => by
    unfold encodeTyB at h
    split at h
    · rename_i Ψ F' n' hF
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨he, hr⟩ := encodeTyB_sound isFlex πs π Δ ((.mix, Kind.ofSKind ι) :: Δb) F n hF
      exact ⟨.lam he, hr⟩
    · simp at h
  | π, Δ, Δb, .app F G ι, n, _, _, _, h => by
    unfold encodeTyB at h
    split at h
    · rename_i π' κ₁ κ₂ hkF
      split at h
      · rename_i Ψ₁ F' n₁ h₁
        split at h
        · rename_i Ψ₂ G' n₂ h₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨he₁, hr₁⟩ := encodeTyB_sound isFlex πs π Δ Δb F n h₁
          obtain ⟨he₂, hr₂⟩ := encodeTyB_sound isFlex πs (Pol.comp π' π) Δ Δb G n₁ h₂
          exact ⟨.app (inferKindB_sound [] Δ Δb 0 F hkF) he₁ he₂ (hr₁.disjoint hr₂),
            hr₁.append hr₂⟩
        · simp at h
      · simp at h
    · simp at h
  | π, Δ, Δb, .mu a S, n, _, _, _, h => by
    unfold encodeTyB at h
    cases a with
    | inf m =>
      cases m with
      | zero =>
        simp only at h
        split at h
        · rename_i hpol
          simp only [decide_eq_true_eq] at hpol
          split at h
          · rename_i Ψ S' n' hS
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨he, hr⟩ := encodeTyListB_sound isFlex πs π Δ ((.mix, .star) :: Δb) S (n + 1) hS
            exact ⟨.mu_fresh hpol (mkName_ok isFlex n) hr.not_mem_head he, hr.cons_head⟩
          · simp at h
        · rename_i hpol
          simp only [decide_eq_true_eq] at hpol
          split at h
          · rename_i Ψ S' n' hS
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨he, hr⟩ := encodeTyListB_sound isFlex πs π Δ ((.mix, .star) :: Δb) S n hS
            exact ⟨.mu_inf hpol he, hr⟩
          · simp at h
      | succ _ => simp at h
    | _ => simp at h
  | π, Δ, Δb, .nu a R, n, _, _, _, h => by
    unfold encodeTyB at h
    cases a with
    | inf m =>
      cases m with
      | zero =>
        simp only at h
        split at h
        · rename_i hpol
          simp only [decide_eq_true_eq] at hpol
          split at h
          · rename_i Ψ R' n' hR
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨he, hr⟩ := encodeTyListB_sound isFlex πs π Δ ((.mix, .star) :: Δb) R (n + 1) hR
            exact ⟨.nu_fresh hpol (mkName_ok isFlex n) hr.not_mem_head he, hr.cons_head⟩
          · simp at h
        · rename_i hpol
          simp only [decide_eq_true_eq] at hpol
          split at h
          · rename_i Ψ R' n' hR
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨he, hr⟩ := encodeTyListB_sound isFlex πs π Δ ((.mix, .star) :: Δb) R n hR
            exact ⟨.nu_inf hpol he, hr⟩
          · simp at h
      | succ _ => simp at h
    | _ => simp at h
  | π, Δ, Δb, .allT κ B, n, _, _, _, h => by
    unfold encodeTyB at h
    split at h
    · rename_i Ψ B' n' hB
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨he, hr⟩ := encodeTyB_sound isFlex πs π Δ ((.mix, κ) :: Δb) B n hB
      exact ⟨.allT he, hr⟩
    · simp at h
  | π, Δ, Δb, .exT κ B, n, _, _, _, h => by
    unfold encodeTyB at h
    split at h
    · rename_i Ψ B' n' hB
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨he, hr⟩ := encodeTyB_sound isFlex πs π Δ ((.mix, κ) :: Δb) B n hB
      exact ⟨.exT he, hr⟩
    · simp at h
  | _, _, _, .allS _ _, _, _, _, _, h => by simp [encodeTyB] at h
  | _, _, _, .exS _ _, _, _, _, _, h => by simp [encodeTyB] at h

theorem encodeTyListB_sound (isFlex : Bool) (πs : Pol) :
    ∀ (π : Pol) (Δ : KCtx) (Δb : BCtx) (S : List Ty) (n : Nat) {Ψ : SizeCtx} {S' : List Ty}
      {n' : Nat},
      encodeTyListB isFlex πs π Δ Δb S n = some (Ψ, S', n') →
      EncodeList πs (nameOk isFlex) π Δ Δb S Ψ S' ∧ DomInRange isFlex n n' Ψ
  | π, Δ, Δb, [], n, _, _, _, h => by
    simp only [encodeTyListB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.nil, DomInRange.refl isFlex n⟩
  | π, Δ, Δb, T :: S, n, _, _, _, h => by
    unfold encodeTyListB at h
    split at h
    · rename_i Ψ₁ T' n₁ h₁
      split at h
      · rename_i Ψ₂ S' n₂ h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨he₁, hr₁⟩ := encodeTyB_sound isFlex πs π Δ Δb T n h₁
        obtain ⟨he₂, hr₂⟩ := encodeTyListB_sound isFlex πs π Δ Δb S n₁ h₂
        exact ⟨.cons he₁ he₂ (hr₁.disjoint hr₂), hr₁.append hr₂⟩
      · simp at h
    · simp at h

end

/-- Executable declaration encoder (`EncodedDecl d d'`). -/
def encodeDeclB (d : FunDecl) : Option FunDecl :=
  if decide (d.sizeParams = []) && unsizedB d.ty && ekindingB [] [] d.ty .star then
    match encodeTyB false .neg .pos [] [] d.ty 0 with
    | some (Ψ, ty', _) => some { name := d.name, sizeParams := Ψ, ty := ty', clauses := d.clauses }
    | none => none
  else none

theorem encodeDeclB_sound {d d' : FunDecl} (h : encodeDeclB d = some d') : EncodedDecl d d' := by
  unfold encodeDeclB at h
  split at h
  · rename_i hpre
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpre
    split at h
    · rename_i Ψ ty' n' henc
      simp only [Option.some.injEq] at h
      subst h
      have hE := (encodeTyB_sound false .neg .pos [] [] d.ty 0 henc).1
      simpa [EncodedDecl, nameOk] using
        ⟨hpre.1.1, unsizedB_sound hpre.1.2, ekindingB_sound hpre.2, hE⟩
    · simp at h
  · simp at h

/-- Executable block encoder (`ListRel EncodedDecl Ξ Ξannot`). -/
def encodeBlockB : List FunDecl → Option (List FunDecl)
  | [] => some []
  | d :: Ξ =>
    match encodeDeclB d, encodeBlockB Ξ with
    | some d', some Ξ' => some (d' :: Ξ')
    | _, _ => none

theorem encodeBlockB_sound :
    ∀ {Ξ Ξannot : List FunDecl}, encodeBlockB Ξ = some Ξannot → ListRel EncodedDecl Ξ Ξannot
  | [], _, h => by
    simp only [encodeBlockB, Option.some.injEq] at h
    subst h; exact .nil
  | d :: Ξ, _, h => by
    unfold encodeBlockB at h
    split at h
    · rename_i d' Ξ' hd hΞ
      simp only [Option.some.injEq] at h
      subst h
      exact .cons (encodeDeclB_sound hd) (encodeBlockB_sound hΞ)
    · simp at h

/-! ## Part 5: Executable Pattern & Copattern Spine Inference (`inferPatB`, `inferSpineB`) -/

/-- Executable pattern inference (`InferPat Ψ Θ p A Γ Ψ' Θ'`). -/
def inferPatB (Ψ : SizeCtx) (Θ : TyCtx) : Pat → Ty → Option (TermCtx × SizeCtx × TyCtx)
  | .var x, A => some ([(x, A)], [], [])
  | .unit, A =>
    match A with
    | .unit => some ([], [], [])
    | _ => none
  | .pair p q, A =>
    match A with
    | .prod A₁ A₂ =>
      match inferPatB Ψ Θ p A₁ with
      | some (Γ₁, Ψ₁, Θ₁) =>
        match inferPatB (Ψ ++ Ψ₁) (Θ ++ Θ₁) q A₂ with
        | some (Γ₂, Ψ₂, Θ₂) => some (Γ₁ ++ Γ₂, Ψ₁ ++ Ψ₂, Θ₁ ++ Θ₂)
        | none => none
      | none => none
    | _ => none
  | .cons c p, A =>
    match A with
    | .mu a S =>
      match S[c]? with
      | some Sc =>
        let j := freshEven Ψ.dom
        match inferPatB (Ψ ++ [(j, a)]) Θ p (Sc.substTy 0 (.mu (.var j 0) S)) with
        | some (Γ, Ψ', Θ') => some (Γ, (j, a) :: Ψ', Θ')
        | none => none
      | none => none
    | _ => none
  | .pack p, A =>
    match A with
    | .exT κ B =>
      let X := freshVar (Θ.map Prod.fst)
      match inferPatB Ψ (Θ ++ [(X, κ)]) p (B.substTy 0 (.fvar X)) with
      | some (Γ, Ψ', Θ') => some (Γ, Ψ', (X, κ) :: Θ')
      | none => none
    | _ => none

theorem inferPatB_sound :
    ∀ (p : Pat) (Ψ : SizeCtx) (Θ : TyCtx) (A : Ty) {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : TyCtx},
      inferPatB Ψ Θ p A = some (Γ, Ψ', Θ') → InferPat Ψ Θ p A Γ Ψ' Θ'
  | .var x, Ψ, Θ, A, _, _, _, h => by
    simp only [inferPatB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .var Ψ Θ x A
  | .unit, Ψ, Θ, A, _, _, _, h => by
    unfold inferPatB at h
    cases A <;> simp at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .unit Ψ Θ
  | .pair p q, Ψ, Θ, A, _, _, _, h => by
    unfold inferPatB at h
    cases A <;> try simp at h
    rename_i A₁ A₂
    split at h
    · rename_i Γ₁ Ψ₁ Θ₁ h₁
      split at h
      · rename_i Γ₂ Ψ₂ Θ₂ h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .pair (inferPatB_sound p Ψ Θ A₁ h₁) (inferPatB_sound q (Ψ ++ Ψ₁) (Θ ++ Θ₁) A₂ h₂)
      · simp at h
    · simp at h
  | .cons c p, Ψ, Θ, A, _, _, _, h => by
    unfold inferPatB at h
    cases A <;> try simp at h
    rename_i a S
    split at h
    · rename_i Sc hc
      split at h
      · rename_i Γ Ψ' Θ' hp
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .cons hc (freshEven_rigid Ψ.dom) (freshEven_not_mem Ψ.dom)
          (inferPatB_sound p (Ψ ++ [(freshEven Ψ.dom, a)]) Θ _ hp)
      · simp at h
    · simp at h
  | .pack p, Ψ, Θ, A, _, _, _, h => by
    unfold inferPatB at h
    cases A <;> try simp at h
    rename_i κ B
    split at h
    · rename_i Γ Ψ' Θ' hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .pack (freshVar_not_mem (Θ.map Prod.fst))
        (inferPatB_sound p Ψ (Θ ++ [(freshVar (Θ.map Prod.fst), κ)]) _ hp)
    · simp at h

/-- Executable copattern spine inference (`InferSpine Ψ Θ qs A Γ Ψ' Θ' C`). -/
def inferSpineB (Ψ : SizeCtx) (Θ : TyCtx) :
    List Copat → Ty → Option (TermCtx × SizeCtx × TyCtx × Ty)
  | [], A => some ([], [], [], A)
  | .pat p :: qs, A =>
    match A with
    | .arr A₁ B =>
      match inferPatB Ψ Θ p A₁ with
      | some (Γ₁, Ψ₁, Θ₁) =>
        match inferSpineB (Ψ ++ Ψ₁) (Θ ++ Θ₁) qs B with
        | some (Γ₂, Ψ₂, Θ₂, C) => some (Γ₁ ++ Γ₂, Ψ₁ ++ Ψ₂, Θ₁ ++ Θ₂, C)
        | none => none
      | none => none
    | _ => none
  | .proj d :: qs, A =>
    match A with
    | .nu a R =>
      match R[d]? with
      | some Rd =>
        let j := freshEven Ψ.dom
        match inferSpineB (Ψ ++ [(j, a)]) Θ qs (Rd.substTy 0 (.nu (.var j 0) R)) with
        | some (Γ, Ψ', Θ', C) => some (Γ, (j, a) :: Ψ', Θ', C)
        | none => none
      | none => none
    | _ => none
  | .inst :: qs, A =>
    match A with
    | .allT κ B =>
      let X := freshVar (Θ.map Prod.fst)
      match inferSpineB Ψ (Θ ++ [(X, κ)]) qs (B.substTy 0 (.fvar X)) with
      | some (Γ, Ψ', Θ', C) => some (Γ, Ψ', (X, κ) :: Θ', C)
      | none => none
    | _ => none

theorem inferSpineB_sound :
    ∀ (qs : List Copat) (Ψ : SizeCtx) (Θ : TyCtx) (A : Ty) {Γ : TermCtx} {Ψ' : SizeCtx}
      {Θ' : TyCtx} {C : Ty},
      inferSpineB Ψ Θ qs A = some (Γ, Ψ', Θ', C) → InferSpine Ψ Θ qs A Γ Ψ' Θ' C
  | [], Ψ, Θ, A, _, _, _, _, h => by
    simp only [inferSpineB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact .nil Ψ Θ A
  | .pat p :: qs, Ψ, Θ, A, _, _, _, _, h => by
    unfold inferSpineB at h
    cases A <;> try simp at h
    rename_i A₁ B
    split at h
    · rename_i Γ₁ Ψ₁ Θ₁ hp
      split at h
      · rename_i Γ₂ Ψ₂ Θ₂ C hqs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact .pat (inferPatB_sound p Ψ Θ A₁ hp) (inferSpineB_sound qs (Ψ ++ Ψ₁) (Θ ++ Θ₁) B hqs)
      · simp at h
    · simp at h
  | .proj d :: qs, Ψ, Θ, A, _, _, _, _, h => by
    unfold inferSpineB at h
    cases A <;> try simp at h
    rename_i a R
    split at h
    · rename_i Rd hd
      split at h
      · rename_i Γ Ψ' Θ' C hqs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact .proj hd (freshEven_rigid Ψ.dom) (freshEven_not_mem Ψ.dom)
          (inferSpineB_sound qs (Ψ ++ [(freshEven Ψ.dom, a)]) Θ _ hqs)
      · simp at h
    · simp at h
  | .inst :: qs, Ψ, Θ, A, _, _, _, _, h => by
    unfold inferSpineB at h
    cases A <;> try simp at h
    rename_i κ B
    split at h
    · rename_i Γ Ψ' Θ' C hqs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact .inst (freshVar_not_mem (Θ.map Prod.fst))
        (inferSpineB_sound qs Ψ (Θ ++ [(freshVar (Θ.map Prod.fst), κ)]) _ hqs)
    · simp at h

/-! ## Part 6: Executable Type Comparison (`compareTyB2`) -/

/-- Pointwise comparison helper for functor lists opened at `X`. -/
def compareListWith (cmp : Ty → Ty → Option (List SConstr)) (X : Nat) :
    List Ty → List Ty → Option (List SConstr)
  | [], [] => some []
  | T :: S, T' :: S' =>
    match cmp (T.substTy 0 (.fvar X)) (T'.substTy 0 (.fvar X)),
          compareListWith cmp X S S' with
    | some C₁, some C₂ => some (C₁ ++ C₂)
    | _, _ => none
  | _, _ => none

theorem compareListWith_sound {Ψ : SizeCtx} {Δ : KCtx} {X : Nat}
    {cmp : Ty → Ty → Option (List SConstr)}
    (hcmp : ∀ A B C, cmp A B = some C → Compare Ψ Δ A B .star C) :
    ∀ (S S' : List Ty) {C : List SConstr},
      compareListWith cmp X S S' = some C → CompareList Ψ Δ X S S' C
  | [], [], _, h => by
    simp only [compareListWith, Option.some.injEq] at h
    subst h; exact .nil
  | [], _ :: _, _, h => by simp [compareListWith] at h
  | _ :: _, [], _, h => by simp [compareListWith] at h
  | T :: S, T' :: S', _, h => by
    unfold compareListWith at h
    split at h
    · rename_i C₁ C₂ h₁ h₂
      simp only [Option.some.injEq] at h
      subst h
      exact .cons (hcmp _ _ C₁ h₁) (compareListWith_sound hcmp S S' h₂)
    · simp at h

/-- Detects a type-level β-redex `.app (.lam ι F) G ι`. -/
def betaRedex? : Ty → Option (SKind × Ty × Ty)
  | .app Op G ι' =>
    match Op with
    | .lam ι F => if decide (ι' = ι) then some (ι, F, G) else none
    | _ => none
  | _ => none

theorem betaRedex?_some {A : Ty} {ι : SKind} {F G : Ty}
    (h : betaRedex? A = some (ι, F, G)) : A = .app (.lam ι F) G ι := by
  cases A with
  | app Op Arg ι' =>
    cases Op with
    | lam ι₀ F₀ =>
      simp only [betaRedex?] at h
      split at h
      · rename_i heq
        simp only [decide_eq_true_eq] at heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        subst heq; rfl
      · simp at h
    | _ => simp [betaRedex?] at h
  | _ => simp [betaRedex?] at h

/-- Structural core of `compareTyB2` parameterized by the recursive comparison function `rec`. -/
def compareTyCoreB (rec : SizeCtx → KCtx → Ty → Ty → Kind → Option (List SConstr))
    (Ψ : SizeCtx) (Δ : KCtx) (A B : Ty) (κ : Kind) : Option (List SConstr) :=
  match A, B, κ with
  | .unit, .unit, .star => some []
  | .var k₁, .var k₂, κ =>
    if decide (k₁ = k₂) && ekindingB Δ [] (.var k₁) κ then some [] else none
  | .fvar X₁, .fvar X₂, κ =>
    if decide (X₁ = X₂) && ekindingB Δ [] (.fvar X₁) κ then some [] else none
  | .prod A₁ B₁, .prod A₂ B₂, .star =>
    match rec Ψ Δ A₁ A₂ .star, rec Ψ Δ B₁ B₂ .star with
    | some C₁, some C₂ => some (C₁ ++ C₂)
    | _, _ => none
  | .arr A₁ B₁, .arr A₂ B₂, .star =>
    match rec Ψ Δ A₂ A₁ .star, rec Ψ Δ B₁ B₂ .star with
    | some C₁, some C₂ => some (C₁ ++ C₂)
    | _, _ => none
  | .lam ι₁ F₁, .lam ι₂ F₂, .arr π κ₁ κ₂ =>
    if ekindingB Δ [] (.lam ι₁ F₁) (.arr π κ₁ κ₂) &&
       ekindingB Δ [] (.lam ι₂ F₂) (.arr π κ₁ κ₂) then
      let X := freshVar Δ.dom
      rec Ψ (Δ ++ [(X, π, κ₁)]) (F₁.substTy 0 (.fvar X)) (F₂.substTy 0 (.fvar X)) κ₂
    else none
  | .allT κ₁ B₁, .allT κ₂ B₂, .star =>
    if decide (κ₁ = κ₂) && ekindingB Δ [] (.allT κ₁ B₁) .star &&
       ekindingB Δ [] (.allT κ₁ B₂) .star then
      let X := freshVar Δ.dom
      rec Ψ (Δ ++ [(X, .mix, κ₁)]) (B₁.substTy 0 (.fvar X)) (B₂.substTy 0 (.fvar X)) .star
    else none
  | .exT κ₁ B₁, .exT κ₂ B₂, .star =>
    if decide (κ₁ = κ₂) && ekindingB Δ [] (.exT κ₁ B₁) .star &&
       ekindingB Δ [] (.exT κ₁ B₂) .star then
      let X := freshVar Δ.dom
      rec Ψ (Δ ++ [(X, .mix, κ₁)]) (B₁.substTy 0 (.fvar X)) (B₂.substTy 0 (.fvar X)) .star
    else none
  | .mu a S, .mu b S', .star =>
    if ekindingB Δ [] (.mu a S) .star && ekindingB Δ [] (.mu b S') .star then
      let X := freshVar Δ.dom
      let Δ' := Δ ++ [(X, .mix, .star)]
      let cmp := fun U V => rec Ψ Δ' U V .star
      if allPosFunctorsB Δ S' then
        match compareListWith cmp X S S' with
        | some C => some (⟨Ψ, a, b, false, true⟩ :: C)
        | none => none
      else
        match compareListWith cmp X S S', compareListWith cmp X S' S with
        | some C₁, some C₂ => some (⟨Ψ, a, b, false, true⟩ :: (C₁ ++ C₂))
        | _, _ => none
    else none
  | .nu a R, .nu b R', .star =>
    if ekindingB Δ [] (.nu a R) .star && ekindingB Δ [] (.nu b R') .star then
      let X := freshVar Δ.dom
      let Δ' := Δ ++ [(X, .mix, .star)]
      let cmp := fun U V => rec Ψ Δ' U V .star
      if allPosFunctorsB Δ R' then
        match compareListWith cmp X R R' with
        | some C => some (⟨Ψ, b, a, false, true⟩ :: C)
        | none => none
      else
        match compareListWith cmp X R R', compareListWith cmp X R' R with
        | some C₁, some C₂ => some (⟨Ψ, b, a, false, true⟩ :: (C₁ ++ C₂))
        | _, _ => none
    else none
  | _, _, _ => none

theorem compareTyCoreB_sound
    {rec : SizeCtx → KCtx → Ty → Ty → Kind → Option (List SConstr)}
    (hrec : ∀ Ψ Δ A B κ C, rec Ψ Δ A B κ = some C → Compare Ψ Δ A B κ C)
    (Ψ : SizeCtx) (Δ : KCtx) (A B : Ty) (κ : Kind) {C : List SConstr}
    (h : compareTyCoreB rec Ψ Δ A B κ = some C) : Compare Ψ Δ A B κ C := by
  unfold compareTyCoreB at h
  split at h
  · simp only [Option.some.injEq] at h; subst h
    exact .refl .unit
  · split at h
    · rename_i heq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at heq
      simp only [Option.some.injEq] at h; subst h
      rw [← heq.1]
      exact .refl (ekindingB_sound heq.2)
    · simp at h
  · split at h
    · rename_i heq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at heq
      simp only [Option.some.injEq] at h; subst h
      rw [← heq.1]
      exact .refl (ekindingB_sound heq.2)
    · simp at h
  · split at h
    · rename_i C₁ C₂ h₁ h₂
      simp only [Option.some.injEq] at h; subst h
      exact .prod (hrec _ _ _ _ _ _ h₁) (hrec _ _ _ _ _ _ h₂)
    · simp at h
  · split at h
    · rename_i C₁ C₂ h₁ h₂
      simp only [Option.some.injEq] at h; subst h
      exact .arr (hrec _ _ _ _ _ _ h₁) (hrec _ _ _ _ _ _ h₂)
    · simp at h
  · split at h
    · rename_i hk
      simp only [Bool.and_eq_true] at hk
      exact .lam (freshVar_not_mem Δ.dom) (hrec _ _ _ _ _ _ h)
        (ekindingB_sound hk.1) (ekindingB_sound hk.2)
    · simp at h
  · split at h
    · rename_i hk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      rcases hk with ⟨⟨rfl, hk₁⟩, hk₂⟩
      exact .allT (freshVar_not_mem Δ.dom) (hrec _ _ _ _ _ _ h)
        (ekindingB_sound hk₁) (ekindingB_sound hk₂)
    · simp at h
  · split at h
    · rename_i hk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      rcases hk with ⟨⟨rfl, hk₁⟩, hk₂⟩
      exact .exT (freshVar_not_mem Δ.dom) (hrec _ _ _ _ _ _ h)
        (ekindingB_sound hk₁) (ekindingB_sound hk₂)
    · simp at h
  · split at h
    · rename_i hk
      simp only [Bool.and_eq_true] at hk
      dsimp only at h
      split at h
      · rename_i hpos
        split at h
        · rename_i Cs hCs
          simp only [Option.some.injEq] at h; subst h
          exact .mu_pos (freshVar_not_mem Δ.dom)
            (compareListWith_sound (fun U V C₀ h₀ => hrec _ _ U V .star C₀ h₀) _ _ hCs)
            (allPosFunctorsB_sound hpos) (ekindingB_sound hk.1) (ekindingB_sound hk.2)
        · simp at h
      · split at h
        · rename_i C₁ C₂ h₁ h₂
          simp only [Option.some.injEq] at h; subst h
          exact .mu_eqv (freshVar_not_mem Δ.dom)
            (compareListWith_sound (fun U V C₀ h₀ => hrec _ _ U V .star C₀ h₀) _ _ h₁)
            (compareListWith_sound (fun U V C₀ h₀ => hrec _ _ U V .star C₀ h₀) _ _ h₂)
            (ekindingB_sound hk.1) (ekindingB_sound hk.2)
        · simp at h
    · simp at h
  · split at h
    · rename_i hk
      simp only [Bool.and_eq_true] at hk
      dsimp only at h
      split at h
      · rename_i hpos
        split at h
        · rename_i Cs hCs
          simp only [Option.some.injEq] at h; subst h
          exact .nu_pos (freshVar_not_mem Δ.dom)
            (compareListWith_sound (fun U V C₀ h₀ => hrec _ _ U V .star C₀ h₀) _ _ hCs)
            (allPosFunctorsB_sound hpos) (ekindingB_sound hk.1) (ekindingB_sound hk.2)
        · simp at h
      · split at h
        · rename_i C₁ C₂ h₁ h₂
          simp only [Option.some.injEq] at h; subst h
          exact .nu_eqv (freshVar_not_mem Δ.dom)
            (compareListWith_sound (fun U V C₀ h₀ => hrec _ _ U V .star C₀ h₀) _ _ h₁)
            (compareListWith_sound (fun U V C₀ h₀ => hrec _ _ U V .star C₀ h₀) _ _ h₂)
            (ekindingB_sound hk.1) (ekindingB_sound hk.2)
        · simp at h
    · simp at h
  · simp at h

/-- Fuel-bounded executable type comparison (`Compare Ψ Δ A B κ C`) with β-reduction. -/
def compareTyB2 : Nat → SizeCtx → KCtx → Ty → Ty → Kind → Option (List SConstr)
  | 0, _, _, _, _, _ => none
  | fuel + 1, Ψ, Δ, A, B, κ =>
    match betaRedex? A with
    | some (ι, F, G) =>
      if ekindingB Δ [] (.app (.lam ι F) G ι) κ then
        compareTyB2 fuel Ψ Δ (F.substTy 0 G) B κ
      else none
    | none =>
      match betaRedex? B with
      | some (ι, F, G) =>
        if ekindingB Δ [] (.app (.lam ι F) G ι) κ then
          compareTyB2 fuel Ψ Δ A (F.substTy 0 G) κ
        else none
      | none =>
        compareTyCoreB (compareTyB2 fuel) Ψ Δ A B κ

theorem compareTyB2_sound :
    ∀ (fuel : Nat) (Ψ : SizeCtx) (Δ : KCtx) (A B : Ty) (κ : Kind) (C : List SConstr),
      compareTyB2 fuel Ψ Δ A B κ = some C → Compare Ψ Δ A B κ C
  | 0, _, _, _, _, _, _, h => by simp [compareTyB2] at h
  | fuel + 1, Ψ, Δ, A, B, κ, C, h => by
    unfold compareTyB2 at h
    cases hβA : betaRedex? A with
    | some p =>
      rcases p with ⟨ι, F, G⟩
      simp only [hβA] at h
      split at h
      · rename_i hk
        rw [betaRedex?_some hβA]
        exact .beta_l (ekindingB_sound hk) (compareTyB2_sound fuel Ψ Δ _ B κ C h)
      · simp at h
    | none =>
      simp only [hβA] at h
      cases hβB : betaRedex? B with
      | some p =>
        rcases p with ⟨ι, F, G⟩
        simp only [hβB] at h
        split at h
        · rename_i hk
          rw [betaRedex?_some hβB]
          exact .beta_r (ekindingB_sound hk) (compareTyB2_sound fuel Ψ Δ A _ κ C h)
        · simp at h
      | none =>
        simp only [hβB] at h
        exact compareTyCoreB_sound (compareTyB2_sound fuel) Ψ Δ A B κ h

/-! ## Part 7: Executable Bidirectional Term & Clause Inference (`inferTmB`, `checkTmB`, `checkClauseB`) -/

/-- Default type argument of kind `κ` in type context `Θ`: chooses the first in-scope
type variable `(X, κ) ∈ Θ`, falling back to `.unit`. -/
def defaultTypeArg (Θ : TyCtx) (κ : Kind) : Ty :=
  match Θ.find? (fun p => decide (p.2 = κ)) with
  | some (X, _) => .fvar X
  | none => .unit

/-- Generates `m` fresh odd flexible variable names starting from counter `n`. -/
def mkFlexArgs (n m : Nat) : List Nat :=
  (List.range m).map (fun idx => 2 * (n + idx) + 1)

theorem mkFlexArgs_length (n m : Nat) : (mkFlexArgs n m).length = m := by
  simp [mkFlexArgs]

theorem mkFlexArgs_flex (n m : Nat) : ∀ k ∈ mkFlexArgs n m, FlexName k := by
  intro k hk
  simp only [mkFlexArgs, List.mem_map] at hk
  obtain ⟨idx, _, rfl⟩ := hk
  unfold FlexName
  omega

/-- Clause checking combinator parameterized by a term checker `chk`. -/
def checkClauseWith
    (chk : SizeCtx → TyCtx → TermCtx → Ty → Tm → Nat →
      Option (List FlexVar × List SConstr × List Nat × List CallRec × Nat))
    (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (cl : Clause) (n : Nat) :
    Option (List FlexVar × List SConstr × List Nat × List CallRec × Nat) :=
  match cl with
  | .mk qs t =>
    match inferSpineB Ψ Θ qs A with
    | some (Γ', Ψ', Θ', C) => chk (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) C t n
    | none => none

/-- Clause-list checking combinator parameterized by a term checker `chk`. -/
def checkClausesWith
    (chk : SizeCtx → TyCtx → TermCtx → Ty → Tm → Nat →
      Option (List FlexVar × List SConstr × List Nat × List CallRec × Nat))
    (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) :
    List Clause → Nat → Option (List FlexVar × List SConstr × List Nat × List CallRec × Nat)
  | [], n => some ([], [], [], [], n)
  | cl :: D, n =>
    match checkClauseWith chk Ψ Θ Γ A cl n with
    | some (Φ₁, C₁, T₁, K₁, n₁) =>
      match checkClausesWith chk Ψ Θ Γ A D n₁ with
      | some (Φ₂, C₂, T₂, K₂, n₂) => some (Φ₁ ++ Φ₂, C₁ ++ C₂, T₁ ++ T₂, K₁ ++ K₂, n₂)
      | none => none
    | none => none

theorem checkClauseWith_sound {Ω : InfEnv}
    {chk : SizeCtx → TyCtx → TermCtx → Ty → Tm → Nat →
      Option (List FlexVar × List SConstr × List Nat × List CallRec × Nat)}
    (hchk : ∀ Ψ Θ Γ A t Φ C T K n n',
      chk Ψ Θ Γ A t n = some (Φ, C, T, K, n') → CheckTm Ω Ψ Θ Γ A t Φ C T K)
    {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {A : Ty} {cl : Clause}
    {Φ : List FlexVar} {C : List SConstr} {T : List Nat} {K : List CallRec} {n n' : Nat}
    (h : checkClauseWith chk Ψ Θ Γ A cl n = some (Φ, C, T, K, n')) :
    CheckClause Ω Ψ Θ Γ A cl Φ C T K := by
  cases cl with
  | mk qs t =>
    simp only [checkClauseWith] at h
    split at h
    · rename_i Γ' Ψ' Θ' C₀ hsp
      exact .mk (inferSpineB_sound qs Ψ Θ A hsp) (hchk _ _ _ _ _ _ _ _ _ _ _ h)
    · simp at h

theorem checkClausesWith_sound {Ω : InfEnv}
    {chk : SizeCtx → TyCtx → TermCtx → Ty → Tm → Nat →
      Option (List FlexVar × List SConstr × List Nat × List CallRec × Nat)}
    (hchk : ∀ Ψ Θ Γ A t Φ C T K n n',
      chk Ψ Θ Γ A t n = some (Φ, C, T, K, n') → CheckTm Ω Ψ Θ Γ A t Φ C T K)
    {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {A : Ty} :
    ∀ (D : List Clause) {Φ : List FlexVar} {C : List SConstr} {T : List Nat}
      {K : List CallRec} {n n' : Nat},
      checkClausesWith chk Ψ Θ Γ A D n = some (Φ, C, T, K, n') →
      CheckClauses Ω Ψ Θ Γ A D Φ C T K
  | [], _, _, _, _, _, _, h => by
    simp only [checkClausesWith, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact .nil
  | cl :: D, _, _, _, _, _, _, h => by
    unfold checkClausesWith at h
    split at h
    · rename_i Φ₁ C₁ T₁ K₁ n₁ h₁
      split at h
      · rename_i Φ₂ C₂ T₂ K₂ n₂ h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        exact .cons (checkClauseWith_sound hchk h₁) (checkClausesWith_sound hchk D h₂)
      · simp at h
    · simp at h

mutual

/-- Fuel-bounded executable bidirectional term inference (`InferTm Ω Ψ Θ Γ r A Φ C T K`). -/
def inferTmB :
    Nat → InfEnv → SizeCtx → TyCtx → TermCtx → Tm → Nat →
      Option (Ty × List FlexVar × List SConstr × List Nat × List CallRec × Nat)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, Ω, Ψ, Θ, Γ, r, n =>
    match r with
    | .var x =>
      match Γ.lookup x with
      | some A => some (A, [], [], [], [], n)
      | none => none
    | .fn f =>
      match Ω.block.find? (fun d => decide (d.name = f)) with
      | some g =>
        let m := g.sizeParams.length
        let as := mkFlexArgs n m
        let szs := as.map fun k => Size.var k 0
        some (g.ty.substSize (g.sizeParams.dom.zip szs),
          callFlex Ψ g as, callBounds Ψ g szs, [], [⟨Ψ, g.name, szs⟩], n + m)
      | none =>
        match Ω.sig.find? (fun d => decide (d.name = f)) with
        | some g =>
          let m := g.sizeParams.length
          let as := mkFlexArgs n m
          let szs := as.map fun k => Size.var k 0
          some (g.ty.substSize (g.sizeParams.dom.zip szs),
            callFlex Ψ g as, callBounds Ψ g szs, [], [], n + m)
        | none => none
    | .app r₀ (.term s) =>
      match inferTmB fuel Ω Ψ Θ Γ r₀ n with
      | some (.arr A B, Φ₁, C₁, T₁, K₁, n₁) =>
        match checkTmB fuel Ω Ψ Θ Γ A s n₁ with
        | some (Φ₂, C₂, T₂, K₂, n₂) =>
          some (B, Φ₁ ++ Φ₂, C₁ ++ C₂, T₁ ++ T₂, K₁ ++ K₂, n₂)
        | none => none
      | _ => none
    | .app r₀ (.proj d) =>
      match inferTmB fuel Ω Ψ Θ Γ r₀ n with
      | some (.nu a R, Φ, C, T, K, n₁) =>
        match R[d]? with
        | some Rd =>
          let j := 2 * n₁ + 1
          some (Rd.substTy 0 (.nu (.var j 0) R),
            ⟨j, .neg, Ψ⟩ :: Φ,
            ⟨Ψ, .var j 0, a, true, true⟩ :: C,
            (if Rd.hasBVar 0 then [] else [j]) ++ T,
            K, n₁ + 1)
        | none => none
      | _ => none
    | .app r₀ .inst =>
      match inferTmB fuel Ω Ψ Θ Γ r₀ n with
      | some (.allT κ B, Φ, C, T, K, n₁) =>
        let G := defaultTypeArg Θ κ
        if unsizedB G && ekindingB Θ.toK [] G κ then
          match encodeTyB true .mix .mix Θ.toK [] G n₁ with
          | some (ΨG, G', n₂) =>
            some (B.substTy 0 G', encFlex Ψ ΨG ++ Φ, C, T, K, n₂)
          | none => none
        else none
      | _ => none
    | _ => none

/-- Fuel-bounded executable bidirectional term checking (`CheckTm Ω Ψ Θ Γ B t Φ C T K`). -/
def checkTmB :
    Nat → InfEnv → SizeCtx → TyCtx → TermCtx → Ty → Tm → Nat →
      Option (List FlexVar × List SConstr × List Nat × List CallRec × Nat)
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, Ω, Ψ, Θ, Γ, B, t, n =>
    match t with
    | .unit =>
      match B with
      | .unit => some ([], [], [], [], n)
      | _ => none
    | .pair t₁ t₂ =>
      match B with
      | .prod A₁ A₂ =>
        match checkTmB fuel Ω Ψ Θ Γ A₁ t₁ n with
        | some (Φ₁, C₁, T₁, K₁, n₁) =>
          match checkTmB fuel Ω Ψ Θ Γ A₂ t₂ n₁ with
          | some (Φ₂, C₂, T₂, K₂, n₂) =>
            some (Φ₁ ++ Φ₂, C₁ ++ C₂, T₁ ++ T₂, K₁ ++ K₂, n₂)
          | none => none
        | none => none
      | _ => none
    | .cons c t₀ =>
      match B with
      | .mu a S =>
        match S[c]? with
        | some Sc =>
          let j := 2 * n + 1
          match checkTmB fuel Ω Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t₀ (n + 1) with
          | some (Φ, C, T, K, n') =>
            some (⟨j, .pos, Ψ⟩ :: Φ,
              ⟨Ψ, .var j 0, a, true, true⟩ :: C,
              (if Sc.hasBVar 0 then [] else [j]) ++ T,
              K, n')
          | none => none
        | none => none
      | _ => none
    | .pack t₀ =>
      match B with
      | .exT κ B₀ =>
        let G := defaultTypeArg Θ κ
        if unsizedB G && ekindingB Θ.toK [] G κ then
          match encodeTyB true .mix .mix Θ.toK [] G n with
          | some (ΨG, G', n₁) =>
            match checkTmB fuel Ω Ψ Θ Γ (B₀.substTy 0 G') t₀ n₁ with
            | some (Φ, C, T, K, n₂) => some (encFlex Ψ ΨG ++ Φ, C, T, K, n₂)
            | none => none
          | none => none
        else none
      | _ => none
    | .lam D =>
      checkClausesWith (checkTmB fuel Ω) Ψ Θ Γ B D n
    | _ =>
      match inferTmB fuel Ω Ψ Θ Γ t n with
      | some (A, Φ, C₁, T, K, n₁) =>
        match compareTyB2 fuel Ψ Θ.toK A B .star with
        | some C₂ => some (Φ, C₁ ++ C₂, T, K, n₁)
        | none => none
      | none => none

end

theorem infer_check_sound (Ω : InfEnv) :
    ∀ (fuel : Nat),
      (∀ (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (r : Tm) (A : Ty)
         (Φ : List FlexVar) (C : List SConstr) (T : List Nat) (K : List CallRec) (n n' : Nat),
        inferTmB fuel Ω Ψ Θ Γ r n = some (A, Φ, C, T, K, n') →
        InferTm Ω Ψ Θ Γ r A Φ C T K) ∧
      (∀ (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (B : Ty) (t : Tm)
         (Φ : List FlexVar) (C : List SConstr) (T : List Nat) (K : List CallRec) (n n' : Nat),
        checkTmB fuel Ω Ψ Θ Γ B t n = some (Φ, C, T, K, n') →
        CheckTm Ω Ψ Θ Γ B t Φ C T K)
  | 0 => ⟨fun _ _ _ _ _ _ _ _ _ _ _ h => by simp [inferTmB] at h,
          fun _ _ _ _ _ _ _ _ _ _ _ h => by simp [checkTmB] at h⟩
  | fuel + 1 => by
    obtain ⟨ihInf, ihChk⟩ := infer_check_sound Ω fuel
    refine ⟨?_, ?_⟩
    · intro Ψ Θ Γ r A Φ C T K n n' h
      unfold inferTmB at h
      split at h
      · rename_i x
        cases hlk : Γ.lookup x with
        | none => simp [hlk] at h
        | some A₀ =>
          simp only [hlk, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
          exact .var hlk
      · rename_i f
        cases hblk : Ω.block.find? (fun d => decide (d.name = f)) with
        | some g =>
          simp only [hblk, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
          have hg : g ∈ Ω.block := List.mem_of_find?_eq_some hblk
          have hname : g.name = f := by simpa using List.find?_some hblk
          rw [← hname]
          exact .local hg (mkFlexArgs_length n g.sizeParams.length)
            (mkFlexArgs_flex n g.sizeParams.length)
        | none =>
          simp only [hblk] at h
          cases hsig : Ω.sig.find? (fun d => decide (d.name = f)) with
          | some g =>
            simp only [hsig, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
            have hg : g ∈ Ω.sig := List.mem_of_find?_eq_some hsig
            have hname : g.name = f := by simpa using List.find?_some hsig
            rw [← hname]
            exact .global hg (mkFlexArgs_length n g.sizeParams.length)
              (mkFlexArgs_flex n g.sizeParams.length)
          | none => simp [hsig] at h
      · rename_i r₀ s
        split at h
        · rename_i A₀ B₀ Φ₁ C₁ T₁ K₁ n₁ hr
          split at h
          · rename_i Φ₂ C₂ T₂ K₂ n₂ hs
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
            exact .app (ihInf _ _ _ _ _ _ _ _ _ _ _ hr) (ihChk _ _ _ _ _ _ _ _ _ _ _ hs)
          · simp at h
        · simp at h
      · rename_i r₀ d
        split at h
        · rename_i a R Φ₀ C₀ T₀ K₀ n₁ hr
          split at h
          · rename_i Rd hd
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
            have hj : FlexName (2 * n₁ + 1) := by unfold FlexName; omega
            exact .proj (ihInf _ _ _ _ _ _ _ _ _ _ _ hr) hd hj
          · simp at h
        · simp at h
      · rename_i r₀
        split at h
        · rename_i κ B₀ Φ₀ C₀ T₀ K₀ n₁ hr
          dsimp only at h
          split at h
          · rename_i hG
            simp only [Bool.and_eq_true] at hG
            split at h
            · rename_i ΨG G' n₂ henc
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
              have hE := (encodeTyB_sound true .mix .mix Θ.toK [] (defaultTypeArg Θ κ) n₁ henc).1
              simpa [nameOk] using InferTm.inst (ihInf _ _ _ _ _ _ _ _ _ _ _ hr)
                (unsizedB_sound hG.1) (ekindingB_sound hG.2) hE
            · simp at h
          · simp at h
        · simp at h
      · simp at h
    · intro Ψ Θ Γ B t Φ C T K n n' h
      unfold checkTmB at h
      split at h
      · cases B <;> simp at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        exact .unit
      · rename_i t₁ t₂
        split at h
        · rename_i A₁ A₂
          split at h
          · rename_i Φ₁ C₁ T₁ K₁ n₁ h₁
            split at h
            · rename_i Φ₂ C₂ T₂ K₂ n₂ h₂
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
              exact .pair (ihChk _ _ _ _ _ _ _ _ _ _ _ h₁) (ihChk _ _ _ _ _ _ _ _ _ _ _ h₂)
            · simp at h
          · simp at h
        · simp at h
      · rename_i c t₀
        split at h
        · rename_i a S
          split at h
          · rename_i Sc hc
            dsimp only at h
            split at h
            · rename_i Φ₀ C₀ T₀ K₀ n₁ ht₀
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
              have hj : FlexName (2 * n + 1) := by unfold FlexName; omega
              exact .cons hc hj (ihChk _ _ _ _ _ _ _ _ _ _ _ ht₀)
            · simp at h
          · simp at h
        · simp at h
      · rename_i t₀
        split at h
        · rename_i κ B₀
          dsimp only at h
          split at h
          · rename_i hG
            simp only [Bool.and_eq_true] at hG
            split at h
            · rename_i ΨG G' n₁ henc
              split at h
              · rename_i Φ₀ C₀ T₀ K₀ n₂ ht₀
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                have hE := (encodeTyB_sound true .mix .mix Θ.toK [] (defaultTypeArg Θ κ) n henc).1
                simpa [nameOk] using CheckTm.pack (unsizedB_sound hG.1) (ekindingB_sound hG.2)
                  hE (ihChk _ _ _ _ _ _ _ _ _ _ _ ht₀)
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      · rename_i D
        exact .lam (checkClausesWith_sound ihChk D h)
      · split at h
        · rename_i A Φ₀ C₁ T₀ K₀ n₁ hr
          split at h
          · rename_i C₂ hcmp
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
            exact .sub (ihInf _ _ _ _ _ _ _ _ _ _ _ hr) (compareTyB2_sound fuel Ψ Θ.toK A B .star C₂ hcmp)
          · simp at h
        · simp at h

/-- Executable clause checker (`CheckClause Ω Ψ Θ Γ A cl Φ C T K`). -/
def checkClauseB (fuel : Nat) (Ω : InfEnv) (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx)
    (A : Ty) (cl : Clause) (n : Nat) :
    Option (List FlexVar × List SConstr × List Nat × List CallRec × Nat) :=
  checkClauseWith (checkTmB fuel Ω) Ψ Θ Γ A cl n

theorem checkClauseB_sound {fuel : Nat} {Ω : InfEnv} {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx}
    {A : Ty} {cl : Clause} {Φ : List FlexVar} {C : List SConstr} {T : List Nat}
    {K : List CallRec} {n n' : Nat}
    (h : checkClauseB fuel Ω Ψ Θ Γ A cl n = some (Φ, C, T, K, n')) :
    CheckClause Ω Ψ Θ Γ A cl Φ C T K :=
  checkClauseWith_sound (infer_check_sound Ω fuel).2 h

/-! ## Part 8: Certified Size-Change Termination Checker (`checkSCTB`) & Full Pipeline (`checkBlockB`) -/

/-- Deduplicates a list of directed invocation-graph edges. -/
def dedupEdges : List (FunName × FunName × InvGraph) → List (FunName × FunName × InvGraph)
  | [] => []
  | e :: es =>
    let es' := dedupEdges es
    if es'.contains e then es' else e :: es'

/-- Initial normalized base edges `(f, g, G.normalize)` for `f, g ∈ dom`. -/
def initEdges (dom : List FunName) (𝒢 : InvGraphFamily) :
    List (FunName × FunName × InvGraph) :=
  dom.flatMap fun f =>
    dom.flatMap fun g =>
      (𝒢.graphs f g).map fun G => (f, g, G.normalize)

/-- Strict successor helper that forces its argument to WHNF before wrapping in `Nat.succ`. -/
def succForced : Nat → Nat
  | 0 => 1
  | k + 1 => k + 2

theorem succForced_eq : ∀ n, succForced n = n + 1
  | 0 => rfl
  | _ + 1 => rfl

/-- Forces a `Nat` to a thunk-free numeral during kernel `whnf` reduction. -/
def forceNat : Nat → Nat
  | 0 => 0
  | n + 1 => succForced (forceNat n)

theorem forceNat_eq : ∀ n, forceNat n = n
  | 0 => rfl
  | n + 1 => by simp [forceNat, succForced_eq, forceNat_eq n]

/-- Evaluates `n` to a thunk-free numeral before passing it to `k`. -/
def withNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  match forceNat n with
  | 0 => k 0
  | m + 1 => k (m + 1)

@[simp] theorem withNat_eq {α : Type} (n : Nat) (k : Nat → α) : withNat n k = k n := by
  unfold withNat; rw [forceNat_eq]; cases n <;> rfl

/-- Evaluates `b` to WHNF (`true` or `false`) before passing it to `k`. -/
def withBool {α : Type} (b : Bool) (k : Bool → α) : α :=
  match b with
  | true => k true
  | false => k false

@[simp] theorem withBool_eq {α : Type} (b : Bool) (k : Bool → α) : withBool b k = k b := by
  cases b <;> rfl

/-- Evaluates `π` to WHNF before passing it to `k`. -/
def withPol {α : Type} (π : Pol) (k : Pol → α) : α :=
  match π with
  | .pos => k .pos
  | .neg => k .neg
  | .mix => k .mix
  | .top => k .top

@[simp] theorem withPol_eq {α : Type} (π : Pol) (k : Pol → α) : withPol π k = k π := by
  cases π <;> rfl

/-- Evaluates the head constructor of `s : Size` before passing it to `k`. -/
def withSizeCore {α : Type} (s : Size) (k : Size → α) : α :=
  match s with
  | .inf n => k (.inf n)
  | .var i n => k (.var i n)
  | .bvar i n => k (.bvar i n)
  | .meet a b => k (.meet a b)

@[simp] theorem withSizeCore_eq {α : Type} (s : Size) (k : Size → α) :
    withSizeCore s k = k s := by
  cases s <;> rfl

/-- Forces a `Size` expression to a thunk-free constructor tree during kernel `whnf` reduction. -/
def forceSize : Size → Size
  | .inf n => withNat n fun n' => .inf n'
  | .var i n => withNat i fun i' => withNat n fun n' => .var i' n'
  | .bvar i n => withNat i fun i' => withNat n fun n' => .bvar i' n'
  | .meet a b =>
    withSizeCore (forceSize a) fun a' =>
      withSizeCore (forceSize b) fun b' =>
        .meet a' b'

@[simp] theorem forceSize_eq : ∀ s, forceSize s = s
  | .inf _ => by simp [forceSize]
  | .var _ _ => by simp [forceSize]
  | .bvar _ _ => by simp [forceSize]
  | .meet a b => by simp [forceSize, forceSize_eq a, forceSize_eq b]

/-- Evaluates `s : Size` to a thunk-free constructor tree before passing it to `k`. -/
def withSize {α : Type} (s : Size) (k : Size → α) : α :=
  withSizeCore (forceSize s) k

@[simp] theorem withSize_eq {α : Type} (s : Size) (k : Size → α) : withSize s k = k s := by
  simp [withSize]

/-- Evaluates the outer list cell of `xs` before passing it to `k`. -/
def withListCore {α β : Type} (xs : List α) (k : List α → β) : β :=
  match xs with
  | [] => k []
  | h :: t => k (h :: t)

@[simp] theorem withListCore_eq {α β : Type} (xs : List α) (k : List α → β) :
    withListCore xs k = k xs := by
  cases xs <;> rfl

/-- Forces a list spine and all elements using `withElem`. -/
def forceListWith {α : Type} (withElem : α → (α → List α) → List α) : List α → List α
  | [] => []
  | h :: t =>
    withElem h fun h' =>
      withListCore (forceListWith withElem t) fun t' =>
        h' :: t'

theorem forceListWith_eq {α : Type} (withElem : α → (α → List α) → List α)
    (helem : ∀ x f, withElem x f = f x) : ∀ xs, forceListWith withElem xs = xs
  | [] => rfl
  | h :: t => by simp [forceListWith, helem, forceListWith_eq withElem helem t]

/-- Evaluates `xs : List α` to a thunk-free list before passing it to `k`. -/
def withList {α β : Type} (withElem : α → (α → List α) → List α)
    (xs : List α) (k : List α → β) : β :=
  withListCore (forceListWith withElem xs) k

theorem withList_eq {α β : Type} (withElem : α → (α → List α) → List α)
    (helem : ∀ x f, withElem x f = f x) (xs : List α) (k : List α → β) :
    withList withElem xs k = k xs := by
  simp [withList, forceListWith_eq withElem helem]

def withSizeBind {α : Type} (p : Nat × Size) (k : (Nat × Size) → α) : α :=
  withNat p.1 fun x => withSize p.2 fun s => k (x, s)

@[simp] theorem withSizeBind_eq {α : Type} (p : Nat × Size) (k : (Nat × Size) → α) :
    withSizeBind p k = k p := by
  cases p; simp [withSizeBind]

def withSizeCtx {α : Type} (Ψ : List (Nat × Size)) (k : List (Nat × Size) → α) : α :=
  withList withSizeBind Ψ k

@[simp] theorem withSizeCtx_eq {α : Type} (Ψ : List (Nat × Size)) (k : List (Nat × Size) → α) :
    withSizeCtx Ψ k = k Ψ :=
  withList_eq withSizeBind (fun x f => withSizeBind_eq x f) Ψ k

def withFlexVar {α : Type} (v : FlexVar) (k : FlexVar → α) : α :=
  withNat v.name fun nm =>
    withPol v.pol fun pol =>
      withSizeCtx v.scope fun sc =>
        k ⟨nm, pol, sc⟩

@[simp] theorem withFlexVar_eq {α : Type} (v : FlexVar) (k : FlexVar → α) :
    withFlexVar v k = k v := by
  cases v; simp [withFlexVar]

def withSConstr {α : Type} (c : SConstr) (k : SConstr → α) : α :=
  withSizeCtx c.ctx fun ctx =>
    withSize c.lhs fun l =>
      withSize c.rhs fun r =>
        withBool c.strict fun st =>
          withBool c.up fun up =>
            k ⟨ctx, l, r, st, up⟩

@[simp] theorem withSConstr_eq {α : Type} (c : SConstr) (k : SConstr → α) :
    withSConstr c k = k c := by
  cases c; simp [withSConstr]

def withCallRec {α : Type} (cr : CallRec) (k : CallRec → α) : α :=
  withSizeCtx cr.ctx fun ctx =>
    withNat cr.callee fun g =>
      withList withSize cr.args fun as =>
        k ⟨ctx, g, as⟩

@[simp] theorem withCallRec_eq {α : Type} (cr : CallRec) (k : CallRec → α) :
    withCallRec cr k = k cr := by
  cases cr
  simp [withCallRec, withList_eq withSize (fun x f => withSize_eq x f)]

def withClauseRun {α : Type} (r : ClauseRun) (k : ClauseRun → α) : α :=
  withList withFlexVar r.flex fun Φ =>
    withList withSConstr r.constraints fun C =>
      withList withNat r.nonrecVars fun T =>
        withList withCallRec r.calls fun K =>
          k ⟨Φ, C, T, K⟩

@[simp] theorem withClauseRun_eq {α : Type} (r : ClauseRun) (k : ClauseRun → α) :
    withClauseRun r k = k r := by
  cases r
  simp [withClauseRun,
    withList_eq withFlexVar (fun x f => withFlexVar_eq x f),
    withList_eq withSConstr (fun x f => withSConstr_eq x f),
    withList_eq withNat (fun x f => withNat_eq x f),
    withList_eq withCallRec (fun x f => withCallRec_eq x f)]

def withEdgeKind {α : Type} (ek : NishtAbel2024V2.EdgeRel)
    (k : NishtAbel2024V2.EdgeRel → α) : α :=
  match ek with
  | .lt => k .lt
  | .le => k .le

@[simp] theorem withEdgeKind_eq {α : Type} (ek : NishtAbel2024V2.EdgeRel)
    (k : NishtAbel2024V2.EdgeRel → α) :
    withEdgeKind ek k = k ek := by
  cases ek <;> rfl

def withGraphEdge {α : Type} (e : Nat × Nat × NishtAbel2024V2.EdgeRel)
    (k : (Nat × Nat × NishtAbel2024V2.EdgeRel) → α) : α :=
  withNat e.1 fun i =>
    withNat e.2.1 fun j =>
      withEdgeKind e.2.2 fun ek =>
        k (i, j, ek)

@[simp] theorem withGraphEdge_eq {α : Type} (e : Nat × Nat × NishtAbel2024V2.EdgeRel)
    (k : (Nat × Nat × NishtAbel2024V2.EdgeRel) → α) :
    withGraphEdge e k = k e := by
  rcases e with ⟨i, j, ek⟩; simp [withGraphEdge]

def withInvGraph {α : Type} (G : InvGraph) (k : InvGraph → α) : α :=
  withNat G.leftArity fun la =>
    withNat G.rightArity fun ra =>
      withList withGraphEdge G.edges fun es =>
        k ⟨la, ra, es⟩

@[simp] theorem withInvGraph_eq {α : Type} (G : InvGraph) (k : InvGraph → α) :
    withInvGraph G k = k G := by
  cases G
  simp [withInvGraph, withList_eq withGraphEdge (fun x f => withGraphEdge_eq x f)]

def withClosureEdge {α : Type} (e : FunName × FunName × InvGraph)
    (k : (FunName × FunName × InvGraph) → α) : α :=
  withNat e.1 fun f =>
    withNat e.2.1 fun g =>
      withInvGraph e.2.2 fun G =>
        k (f, g, G)

@[simp] theorem withClosureEdge_eq {α : Type} (e : FunName × FunName × InvGraph)
    (k : (FunName × FunName × InvGraph) → α) :
    withClosureEdge e k = k e := by
  rcases e with ⟨f, g, G⟩; simp [withClosureEdge]

@[simp] theorem withClosureEdgeList_eq {α : Type}
    (es : List (FunName × FunName × InvGraph))
    (k : List (FunName × FunName × InvGraph) → α) :
    withList withClosureEdge es k = k es :=
  withList_eq withClosureEdge (fun x f => withClosureEdge_eq x f) es k

/-- One round of transitive composition closure on invocation graphs. -/
def stepClosure (edges : List (FunName × FunName × InvGraph)) :
    List (FunName × FunName × InvGraph) :=
  let comps := edges.flatMap fun e₁ =>
    edges.filterMap fun e₂ =>
      if decide (e₁.1 = e₂.2.1) then
        some (e₂.1, e₁.2.1, e₁.2.2.comp e₂.2.2)
      else none
  dedupEdges (edges ++ comps)

/-- Iterates `stepClosure` for `steps` rounds, forcing intermediate edge lists to normal form. -/
def computeClosureAux : Nat → List (FunName × FunName × InvGraph) →
    List (FunName × FunName × InvGraph)
  | 0, edges => edges
  | steps + 1, edges =>
    withList withClosureEdge (stepClosure edges) fun edges' =>
      computeClosureAux steps edges'

/-- Computes the transitive closure of `𝒢` over `dom` using `steps` rounds. -/
def computeClosure (steps : Nat) (dom : List FunName) (𝒢 : InvGraphFamily) :
    List (FunName × FunName × InvGraph) :=
  withList withClosureEdge (dedupEdges (initEdges dom 𝒢)) fun init =>
    computeClosureAux steps init

/-- Certifies that all normalized base graphs on `dom` belong to `closed`. -/
def baseClosedB (dom : List FunName) (𝒢 : InvGraphFamily)
    (closed : List (FunName × FunName × InvGraph)) : Bool :=
  dom.all fun f =>
    dom.all fun g =>
      (𝒢.graphs f g).all fun G =>
        decide ((f, g, G.normalize) ∈ closed)

/-- Certifies that `closed` is closed under graph composition. -/
def compClosedB (closed : List (FunName × FunName × InvGraph)) : Bool :=
  closed.all fun e₁ =>
    closed.all fun e₂ =>
      if decide (e₁.1 = e₂.2.1) then
        decide ((e₂.1, e₁.2.1, e₁.2.2.comp e₂.2.2) ∈ closed)
      else true

/-- Certifies that every idempotent self-loop in `closed` has a strict `<` diagonal edge. -/
def selfLoopStrictB (closed : List (FunName × FunName × InvGraph)) : Bool :=
  closed.all fun e =>
    if decide (e.1 = e.2.1 ∧ e.2.2.comp e.2.2 = e.2.2) then
      (List.range e.2.2.leftArity).any fun k =>
        decide (e.2.2.edgeAt k k = some .lt)
    else true

/-- Certifies well-formed arities and normalization for all base graphs on `dom`. -/
def arityWfOnDomB (dom : List FunName) (𝒢 : InvGraphFamily) : Bool :=
  dom.all fun f =>
    dom.all fun g =>
      (𝒢.graphs f g).all fun G =>
        decide (G.leftArity = 𝒢.arity g ∧ G.rightArity = 𝒢.arity f ∧ G = G.normalize)

/-- Executable certified Size-Change Termination decision procedure (`SCTValid 𝒢`). -/
def checkSCTB (steps : Nat) (dom : List FunName) (𝒢 : InvGraphFamily) : Bool :=
  withList withClosureEdge (computeClosure steps dom 𝒢) fun closed =>
    arityWfOnDomB dom 𝒢 &&
      baseClosedB dom 𝒢 closed &&
      compClosedB closed &&
      selfLoopStrictB closed

theorem closure_mem_of_certified {dom : List FunName} {𝒢 : InvGraphFamily}
    {closed : List (FunName × FunName × InvGraph)}
    (hdom : ∀ f g, 𝒢.graphs f g ≠ [] → f ∈ dom ∧ g ∈ dom)
    (hbase : baseClosedB dom 𝒢 closed = true)
    (hcomp : compClosedB closed = true)
    {f g : FunName} {G : InvGraph} (hc : InvGraphClosure 𝒢 f g G) :
    (f, g, G) ∈ closed := by
  induction hc with
  | @base f g G hG =>
    have hne : 𝒢.graphs f g ≠ [] := List.ne_nil_of_mem hG
    obtain ⟨hf, hg⟩ := hdom f g hne
    have h₁ := List.all_eq_true.mp hbase f hf
    have h₂ := List.all_eq_true.mp h₁ g hg
    have h₃ := List.all_eq_true.mp h₂ G hG
    exact of_decide_eq_true h₃
  | @comp f h g G₁ G₂ _ _ ih₁ ih₂ =>
    have h₁ := List.all_eq_true.mp hcomp (h, g, G₁) ih₁
    have h₂ := List.all_eq_true.mp h₁ (f, h, G₂) ih₂
    simp only [decide_true, ↓reduceIte, decide_eq_true_eq] at h₂
    exact h₂

/-- Soundness of the certified executable SCT checker (`checkSCTB`). -/
theorem checkSCTB_sound {steps : Nat} {dom : List FunName} {𝒢 : InvGraphFamily}
    (hdom : ∀ f g, 𝒢.graphs f g ≠ [] → f ∈ dom ∧ g ∈ dom)
    (h : checkSCTB steps dom 𝒢 = true) : SCTValid 𝒢 := by
  unfold checkSCTB at h
  simp only [withClosureEdgeList_eq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨harity, hbase⟩, hcomp⟩, hloop⟩ := h
  refine ⟨⟨⟨dom, hdom⟩, ?_⟩, ?_⟩
  · intro f g G hG
    have hne : 𝒢.graphs f g ≠ [] := List.ne_nil_of_mem hG
    obtain ⟨hf, hg⟩ := hdom f g hne
    have h₁ := List.all_eq_true.mp harity f hf
    have h₂ := List.all_eq_true.mp h₁ g hg
    have h₃ := List.all_eq_true.mp h₂ G hG
    exact of_decide_eq_true h₃
  · intro f G hc hid
    have hmem := closure_mem_of_certified hdom hbase hcomp hc
    have hl := List.all_eq_true.mp hloop (f, f, G) hmem
    have hcond : decide ((f, f, G).1 = (f, f, G).2.1 ∧ (f, f, G).2.2.comp (f, f, G).2.2 = (f, f, G).2.2) = true :=
      decide_eq_true ⟨rfl, hid⟩
    rw [if_pos hcond] at hl
    obtain ⟨k, hk, he⟩ := List.any_eq_true.mp hl
    exact ⟨k, List.mem_range.mp hk, of_decide_eq_true he⟩

/-- Runs clause inference on a single clause of an annotated declaration `d`,
forcing the resulting `ClauseRun` to a thunk-free normal form. -/
def inferClauseRunB (fuel : Nat) (Ω : InfEnv) (d : FunDecl) (cl : Clause) : Option ClauseRun :=
  match checkClauseB (fuel + 8) Ω d.sizeParams [] [] d.ty cl 0 with
  | some (Φ, C, T, K, _) => withClauseRun ⟨Φ, C, T, K⟩ some
  | none => none

/-- Checks that `cl` is accepted by Algorithm 2 (`ClauseAccepted`) and all calls stay in `dom`. -/
def checkClauseAcceptedB (fuel : Nat) (Ω : InfEnv) (dom : List FunName)
    (d : FunDecl) (cl : Clause) : Bool :=
  match inferClauseRunB fuel Ω d cl with
  | some r =>
    withSizeCtx (r.solution fuel) fun φ =>
      checkScope φ r.flex &&
        checkCoherent fuel φ r.constraints &&
        r.calls.all (fun k => dom.contains k.callee)
  | none => false

/-- Total `runs` function on `FunName → Clause → ClauseRun` extracted from `inferClauseRunB`. -/
def runsOf (fuel : Nat) (Ω : InfEnv) (Ξannot : List FunDecl)
    (f : FunName) (cl : Clause) : ClauseRun :=
  match Ξannot.find? (fun d => decide (d.name = f)) with
  | some d => (inferClauseRunB fuel Ω d cl).getD ⟨[], [], [], []⟩
  | none => ⟨[], [], [], []⟩

theorem find?_name_eq_self {Ξ : List FunDecl} (hnd : (Ξ.map FunDecl.name).Nodup)
    {d : FunDecl} (hd : d ∈ Ξ) :
    Ξ.find? (fun d' => decide (d'.name = d.name)) = some d := by
  cases hf : Ξ.find? (fun d' => decide (d'.name = d.name)) with
  | none =>
    have := List.find?_eq_none.mp hf d hd
    simp at this
  | some d' =>
    have hd' : d' ∈ Ξ := List.mem_of_find?_eq_some hf
    have hname : d'.name = d.name := by simpa using List.find?_some hf
    rw [List.inj_on_of_nodup_map hnd hd' hd hname]

theorem checkClauseAcceptedB_sound {fuel : Nat} {Ω : InfEnv} {Ξannot : List FunDecl}
    (hnd : (Ξannot.map FunDecl.name).Nodup)
    {d : FunDecl} (hd : d ∈ Ξannot) {cl : Clause}
    (h : checkClauseAcceptedB fuel Ω (Ξannot.map FunDecl.name) d cl = true) :
    ClauseAccepted fuel Ω d cl (runsOf fuel Ω Ξannot d.name cl) ∧
      ∀ k ∈ (runsOf fuel Ω Ξannot d.name cl).calls, k.callee ∈ Ξannot.map FunDecl.name := by
  unfold checkClauseAcceptedB at h
  cases hrun : inferClauseRunB fuel Ω d cl with
  | none => simp [hrun] at h
  | some r =>
    simp only [hrun, withSizeCtx_eq, Bool.and_eq_true] at h
    have hruns : runsOf fuel Ω Ξannot d.name cl = r := by
      simp [runsOf, find?_name_eq_self hnd hd, hrun]
    rw [hruns]
    unfold inferClauseRunB at hrun
    split at hrun
    · rename_i Φ C T K n' hchk
      simp only [withClauseRun_eq, Option.some.injEq] at hrun
      subst hrun
      refine ⟨⟨checkClauseB_sound hchk, h.1.1, h.1.2⟩, ?_⟩
      intro k hk
      simpa using List.all_eq_true.mp h.2 k hk
    · simp at hrun

theorem blockGraphs_dom {fuel : Nat} {Ξannot : List FunDecl}
    {runs : FunName → Clause → ClauseRun}
    (hcalls : ∀ d ∈ Ξannot, ∀ cl ∈ d.clauses,
      ∀ k ∈ (runs d.name cl).calls, k.callee ∈ Ξannot.map FunDecl.name)
    (f g : FunName) (hne : (blockGraphs fuel Ξannot runs).graphs f g ≠ []) :
    f ∈ Ξannot.map FunDecl.name ∧ g ∈ Ξannot.map FunDecl.name := by
  obtain ⟨G, hG⟩ := List.exists_mem_of_ne_nil _ hne
  simp only [blockGraphs, List.mem_flatMap] at hG
  obtain ⟨d, hd, hG⟩ := hG
  split at hG
  · rename_i hdf
    subst hdf
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter, beq_iff_eq] at hG
    obtain ⟨cl, hcl, k, ⟨hk, rfl⟩, _⟩ := hG
    exact ⟨List.mem_map_of_mem hd, hcalls d hd cl hcl k hk⟩
  · simp at hG

/-- Master executable bidirectional type & termination checker (`MiniLean-Sized`, Algorithm 2).
Takes a fuel bound `fuel`, global signature `sig`, and unannotated mutual block `Ξ`. -/
def checkBlockB (fuel : Nat) (sig Ξ : List FunDecl) : Bool :=
  match encodeBlockB Ξ with
  | some Ξannot =>
    let dom := Ξannot.map FunDecl.name
    let Ω : InfEnv := ⟨sig, Ξannot⟩
    let runs := runsOf fuel Ω Ξannot
    nodupB dom &&
      (Ξannot.all fun d => d.clauses.all (checkClauseAcceptedB fuel Ω dom d)) &&
      checkSCTB (dom.length + 1) dom (blockGraphs fuel Ξannot runs)
  | none => false

/-- **Master Soundness Theorem of `MiniLean-Sized` (`checkBlockB_sound`)**:
If `checkBlockB fuel sig Ξ = true`, then `encodeBlockB Ξ` produces an annotated block
`Ξannot` accepted by Algorithm 2 (`Algorithm2Accepts sig Ξ Ξannot`), well-typed in
System `F_ω^{cop,SCT}` (`BlockTy sig Ξannot` when `DeclsWf sig`), and strongly normalizing /
productive (`SemValid W Ξannot` by Theorem 15). -/
theorem checkBlockB_sound {fuel : Nat} {sig Ξ : List FunDecl}
    (h : checkBlockB fuel sig Ξ = true) :
    ∃ Ξannot,
      encodeBlockB Ξ = some Ξannot ∧
      Algorithm2Accepts sig Ξ Ξannot ∧
      (DeclsWf sig → BlockTy sig Ξannot) ∧
      (∀ W : List FunDecl,
        DeclsWf sig →
        (∀ d ∈ sig ++ Ξannot, d ∈ W) →
        (W.map FunDecl.name).Nodup →
        (∀ d ∈ W, (Tm.lam d.clauses).Closed) →
        SemValid W sig →
        SemValid W Ξannot) := by
  unfold checkBlockB at h
  cases henc : encodeBlockB Ξ with
  | none => simp [henc] at h
  | some Ξannot =>
    simp only [henc, Bool.and_eq_true] at h
    obtain ⟨⟨hndB, hcls⟩, hsct⟩ := h
    have hnd : (Ξannot.map FunDecl.name).Nodup := nodupB_sound hndB
    let Ω : InfEnv := ⟨sig, Ξannot⟩
    let runs := runsOf fuel Ω Ξannot
    have hboth : ∀ d ∈ Ξannot, ∀ cl ∈ d.clauses,
        ClauseAccepted fuel Ω d cl (runs d.name cl) ∧
        ∀ k ∈ (runs d.name cl).calls, k.callee ∈ Ξannot.map FunDecl.name := by
      intro d hd cl hcl
      have hd' := List.all_eq_true.mp hcls d hd
      have hcl' := List.all_eq_true.mp hd' cl hcl
      exact checkClauseAcceptedB_sound hnd hd hcl'
    have hacc : Algorithm2Accepts sig Ξ Ξannot := by
      refine ⟨encodeBlockB_sound henc, hnd, fuel, runs, ?_, ?_⟩
      · intro d hd cl hcl
        exact (hboth d hd cl hcl).1
      · exact checkSCTB_sound (blockGraphs_dom fun d hd cl hcl => (hboth d hd cl hcl).2) hsct
    refine ⟨Ξannot, rfl, hacc, fun hsigwf => algorithm2_typing hsigwf hacc, ?_⟩
    intro W hsigwf hW hnames hclosed hsig
    exact (theorem_15_proof ramseyPairs W sig Ξ Ξannot hsigwf hacc hW hnames hclosed hsig).2

/-! ## Part 9: Mandatory Executable Regression Suite (Positive & Negative Benchmarks) -/

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-- Unsized natural numbers `Nat = μ^∞ [1, X]`. -/
abbrev natU : Ty := .mu (.inf 0) [.unit, .var 0]

/-- Unsized streams of natural numbers `Stream = ν^∞ [Nat, X]`. -/
abbrev streamU : Ty := .nu (.inf 0) [natU, .var 0]

/-- Unsized polymorphic lists `List X = μ^∞ [1, var 1 × var 0]` (where `var 1` is `X`). -/
abbrev listBodyU : Ty := .mu (.inf 0) [.unit, .prod (.var 1) (.var 0)]

/-- Unsized polymorphic binary-branching rose trees `Rose X = μ^∞ [var 1, var 1 × (var 0 × var 0)]`. -/
abbrev roseBodyU : Ty := .mu (.inf 0) [.var 1, .prod (.var 1) (.prod (.var 0) (.var 0))]

/-- Unsized mixed-variance bush `Bush = μ^∞ [1, (X → 1) × X]`. -/
abbrev bushU : Ty := .mu (.inf 0) [.unit, .prod (.arr (.var 0) .unit) (.var 0)]

/-- Identity type operator `IdOp = λ(X : *). X`. -/
abbrev idOpU : Ty := .lam .star (.var 0)

/-! ### Positive Benchmark P1: Structural Inductive Recursion (`copy : Nat → Nat`) -/

def copySrc : FunDecl where
  name := 0
  sizeParams := []
  ty := .arr natU natU
  clauses :=
    [.mk [.pat (.cons 0 (.var 10))] (.cons 0 (.var 10)),
     .mk [.pat (.cons 1 (.var 11))] (.cons 1 (.app (.fn 0) (.term (.var 11))))]

/-- Kernel `rfl` check: `MiniLean-Sized` accepts `copySrc`. -/
theorem test_P1_copy_accepted : checkBlockB 10 [] [copySrc] = true := rfl

/-! ### Positive Benchmark P2: Productive Stream Combinators via Copatterns (`zeros` & `blink`) -/

def zerosSrc : FunDecl where
  name := 1
  sizeParams := []
  ty := streamU
  clauses :=
    [.mk [.proj 0] (.cons 0 .unit),
     .mk [.proj 1] (.fn 1)]

/-- `blink` alternates `0` and `1` using nested copattern projections `.head`, `.tail.head`, `.tail.tail`. -/
def blinkSrc : FunDecl where
  name := 2
  sizeParams := []
  ty := streamU
  clauses :=
    [.mk [.proj 0] (.cons 0 .unit),
     .mk [.proj 1, .proj 0] (.cons 1 (.cons 0 .unit)),
     .mk [.proj 1, .proj 1] (.fn 2)]

/-- Kernel `rfl` check: `MiniLean-Sized` accepts productive stream definitions `zerosSrc` and `blinkSrc`. -/
theorem test_P2_streams_accepted : checkBlockB 10 [] [zerosSrc, blinkSrc] = true := rfl

/-! ### Positive Benchmark P3: Polymorphic List Length (`len : ∀(X : *). List X → Nat`) -/

def lenSrc : FunDecl where
  name := 3
  sizeParams := []
  ty := .allT .star (.arr listBodyU natU)
  clauses :=
    [.mk [.inst, .pat (.cons 0 (.var 10))] (.cons 0 .unit),
     .mk [.inst, .pat (.cons 1 (.pair (.var 11) (.var 12)))]
       (.cons 1 (.app (.app (.fn 3) .inst) (.term (.var 12))))]

/-- Kernel `rfl` check: `MiniLean-Sized` accepts polymorphic `lenSrc`. -/
theorem test_P3_len_accepted : checkBlockB 10 [] [lenSrc] = true := rfl

/-! ### Positive Benchmark P4: Mutual Recursion (`even` & `odd : Nat → Nat`) -/

def evenSrc : FunDecl where
  name := 4
  sizeParams := []
  ty := .arr natU natU
  clauses :=
    [.mk [.pat (.cons 0 (.var 10))] (.cons 1 (.cons 0 .unit)),
     .mk [.pat (.cons 1 (.var 11))] (.app (.fn 5) (.term (.var 11)))]

def oddSrc : FunDecl where
  name := 5
  sizeParams := []
  ty := .arr natU natU
  clauses :=
    [.mk [.pat (.cons 0 (.var 10))] (.cons 0 .unit),
     .mk [.pat (.cons 1 (.var 11))] (.app (.fn 4) (.term (.var 11)))]

/-- Kernel `rfl` check: `MiniLean-Sized` accepts the mutually recursive `[evenSrc, oddSrc]` block. -/
theorem test_P4_evenOdd_accepted : checkBlockB 4 [] [evenSrc, oddSrc] = true := rfl

/-! ### Positive Benchmark P5: Higher-Order Polymorphic Rose-Tree Traversal (`mapRose` & `mapChildren`)
Exercises polymorphism (`∀ X : *`), higher-order function arguments (`(X → X)`), mutual recursion,
and heterogeneous size arities (`mapRose` has 1 size parameter, `mapChildren` has 2 size parameters). -/

def mapRoseSrc : FunDecl where
  name := 6
  sizeParams := []
  ty := .allT .star (.arr (.arr (.var 0) (.var 0)) (.arr roseBodyU roseBodyU))
  clauses :=
    [.mk [.inst, .pat (.var 20), .pat (.cons 0 (.var 21))]
       (.cons 0 (.app (.var 20) (.term (.var 21)))),
     .mk [.inst, .pat (.var 20), .pat (.cons 1 (.pair (.var 21) (.var 22)))]
       (.cons 1 (.pair (.app (.var 20) (.term (.var 21)))
         (.app (.app (.app (.fn 7) .inst) (.term (.var 20))) (.term (.var 22)))))]

def mapChildrenSrc : FunDecl where
  name := 7
  sizeParams := []
  ty := .allT .star (.arr (.arr (.var 0) (.var 0))
    (.arr (.prod roseBodyU roseBodyU) (.prod roseBodyU roseBodyU)))
  clauses :=
    [.mk [.inst, .pat (.var 20), .pat (.pair (.var 21) (.var 22))]
       (.pair (.app (.app (.app (.fn 6) .inst) (.term (.var 20))) (.term (.var 21)))
              (.app (.app (.app (.fn 6) .inst) (.term (.var 20))) (.term (.var 22))))]

/-- Kernel `rfl` check: `MiniLean-Sized` accepts the higher-order mutual rose-tree traversal
`[mapRoseSrc, mapChildrenSrc]`. -/
theorem test_P5_mapRose_accepted :
    checkBlockB 4 [] [mapRoseSrc, mapChildrenSrc] = true := rfl

/-! ### Positive Benchmark P6: Mixed-Variance Functor + Type-Level β-Redex (`evalBush`) -/

def evalBushValidSrc : FunDecl where
  name := 8
  sizeParams := []
  ty := .arr bushU (.app idOpU bushU .star)
  clauses :=
    [.mk [.pat (.cons 1 (.pair (.var 11) (.var 12)))] (.app (.fn 8) (.term (.var 12)))]

/-- Kernel `rfl` check: `MiniLean-Sized` accepts `evalBushValidSrc` (mixed-variance functor + β-redex). -/
theorem test_P6_evalBush_accepted : checkBlockB 10 [] [evalBushValidSrc] = true := rfl

/-! ### End-to-End Declarative Typing & Strong Normalization Proofs from `rfl` -/

/-- Applying `checkBlockB_sound` to `test_P1_copy_accepted` (`rfl`) immediately yields an
annotated declaration block that is well-typed in System `F_ω^{cop,SCT}` (`BlockTy`). -/
theorem copy_blockTy :
    ∃ Ξannot, encodeBlockB [copySrc] = some Ξannot ∧ BlockTy [] Ξannot := by
  obtain ⟨Ξannot, henc, _, hbt, _⟩ := checkBlockB_sound test_P1_copy_accepted
  exact ⟨Ξannot, henc, hbt (fun _ h => by simp at h)⟩

/-- Applying `checkBlockB_sound` to `test_P5_mapRose_accepted` (`rfl`) immediately yields
`BlockTy` for the higher-order polymorphic rose-tree traversal block. -/
theorem mapRose_blockTy :
    ∃ Ξannot, encodeBlockB [mapRoseSrc, mapChildrenSrc] = some Ξannot ∧ BlockTy [] Ξannot := by
  obtain ⟨Ξannot, henc, _, hbt, _⟩ := checkBlockB_sound test_P5_mapRose_accepted
  exact ⟨Ξannot, henc, hbt (fun _ h => by simp at h)⟩

/-! ### Negative Benchmark N1: Static Rejection of Agda #3026 (`loop3026`)
`loop3026` attempts to recurse on the unguarded input, which would require `i < i` or `∞ < ∞`.
`MiniLean-Sized` statically rejects it (`= false := rfl`). -/

def agda3026LoopSrc : FunDecl where
  name := 90
  sizeParams := []
  ty := .arr natU natU
  clauses :=
    [.mk [.pat (.var 10)] (.app (.fn 90) (.term (.var 10)))]

/-- Kernel `rfl` check: `MiniLean-Sized` statically rejects Agda #3026 self-instantiation. -/
theorem test_N1_agda3026_rejected : checkBlockB 10 [] [agda3026LoopSrc] = false := rfl

/-! ### Negative Benchmark N2: Static Rejection of Non-Productive Stream (`badStream .tail = badStream .tail`)
Eliminating `.proj 1` at the recursive call site requires a larger coinductive size than the
target projection provides (`j < i` vs `i ≤ j`), so `MiniLean-Sized` rejects it (`= false := rfl`). -/

def nonProductiveStreamSrc : FunDecl where
  name := 91
  sizeParams := []
  ty := streamU
  clauses :=
    [.mk [.proj 0] (.cons 0 .unit),
     .mk [.proj 1] (.app (.fn 91) (.proj 1))]

/-- Kernel `rfl` check: `MiniLean-Sized` statically rejects non-productive stream recursion. -/
theorem test_N2_nonProductiveStream_rejected :
    checkBlockB 10 [] [nonProductiveStreamSrc] = false := rfl

/-! ### Negative Benchmark N3: Static Rejection of Agda #7178 Negative Fixpoint (`MuNeg = μ [X → 1]`)
Attempting to recurse without size decrease on `MuNeg = μ [X → 1]` is statically rejected (`= false := rfl`). -/

def agda7178BadLoopSrc : FunDecl where
  name := 92
  sizeParams := []
  ty := .arr (.mu (.inf 0) [.arr (.var 0) .unit]) .unit
  clauses :=
    [.mk [.pat (.cons 0 (.var 10))] (.app (.fn 92) (.term (.cons 0 (.var 10))))]

/-- Kernel `rfl` check: `MiniLean-Sized` statically rejects Agda #7178 negative fixpoint loop. -/
theorem test_N3_agda7178_negFix_rejected :
    checkBlockB 10 [] [agda7178BadLoopSrc] = false := rfl

/-! ### Negative Benchmark N4: Static Rejection of Non-Terminating Mutual Cycle (`badEven`/`badOdd`)
`badEven` peels a constructor, but `badOdd` calls `badEven` on its unpeeled argument wrapped in
`.cons 1`, creating an idempotent self-loop without strict decrease. -/

def badEvenSrc : FunDecl where
  name := 93
  sizeParams := []
  ty := .arr natU natU
  clauses :=
    [.mk [.pat (.cons 1 (.var 11))] (.app (.fn 94) (.term (.var 11)))]

def badOddSrc : FunDecl where
  name := 94
  sizeParams := []
  ty := .arr natU natU
  clauses :=
    [.mk [.pat (.var 11)] (.app (.fn 93) (.term (.cons 1 (.var 11))))]

/-- Kernel `rfl` check: `MiniLean-Sized` statically rejects the non-terminating mutual block. -/
theorem test_N4_badMutual_rejected :
    checkBlockB 10 [] [badEvenSrc, badOddSrc] = false := rfl

end MiniLeanSized
