import Solutions.V5.Stable

/-! # V5: semantic domains of kinds, goodness and order -/

namespace NishtAbel2024V5

/-! ## Kind-polymorphic values -/

@[simp] theorem PSem.ofSem_self (ι : SKind) (X : Sem ι) : PSem.ofSem ι X ι = X := by
  simp [PSem.ofSem]

theorem PSem.ofSem_ne {ι ι' : SKind} (X : Sem ι) (h : ι ≠ ι') :
    PSem.ofSem ι X ι' = Sem.dflt ι' := by
  simp [PSem.ofSem, h]

@[simp] theorem Sem.ofStar_star (S : Set Tm) : Sem.ofStar S .star = S := rfl

@[simp] theorem Sem.ofFun_arr (f : (ι₁ ι₂ : SKind) → Sem ι₁ → Sem ι₂) (ι₁ ι₂ : SKind) :
    Sem.ofFun f (.arr ι₁ ι₂) = f ι₁ ι₂ := rfl

@[simp] theorem Env.cons_zero (X : PSem) (η : Env) : Env.cons X η 0 = X := rfl

@[simp] theorem Env.cons_succ (X : PSem) (η : Env) (n : Nat) : Env.cons X η (n + 1) = η n := rfl

/-! ## Polarities -/

/-- `PolRel W π κ X Y`: `X` and `Y` are related along the variance `π` at kind `κ`. -/
def PolRel (W : World) (π : Pol) (κ : Kind) {ι : SKind} (X Y : Sem ι) : Prop :=
  polRelOf (SemLe W κ) π X Y

theorem polRelOf_mono {α : Type} {le : α → α → Prop} {π π' : Pol} (h : Pol.le π' π) {X Y : α}
    (hr : polRelOf le π' X Y) : polRelOf le π X Y := by
  cases π' <;> cases π <;> simp_all [Pol.le, polRelOf]

theorem Pol.le_refl (π : Pol) : Pol.le π π := by cases π <;> simp [Pol.le]

theorem Pol.le_trans {π₁ π₂ π₃ : Pol} (h₁ : Pol.le π₁ π₂) (h₂ : Pol.le π₂ π₃) : Pol.le π₁ π₃ := by
  cases π₁ <;> cases π₂ <;> cases π₃ <;> simp_all [Pol.le]

/-! ## Equations for goodness and order -/

theorem good_star {W : World} {A : Set Tm} : Good W .star (ι := .star) A ↔ Cand W A := Iff.rfl

theorem semLe_star {W : World} {A B : Set Tm} : SemLe W .star (ι := .star) A B ↔ A ⊆ B :=
  Iff.rfl

theorem good_arr {W : World} {π : Pol} {κ₁ κ₂ : Kind} {ι₁ ι₂ : SKind} {F : Sem (.arr ι₁ ι₂)} :
    Good W (.arr π κ₁ κ₂) F ↔
      (∀ X, Good W κ₁ X → Good W κ₂ (F X)) ∧
      ∀ X Y, Good W κ₁ X → Good W κ₁ Y → PolRel W π κ₁ X Y → SemLe W κ₂ (F X) (F Y) :=
  Iff.rfl

theorem semLe_arr {W : World} {π : Pol} {κ₁ κ₂ : Kind} {ι₁ ι₂ : SKind}
    {F G : Sem (.arr ι₁ ι₂)} :
    SemLe W (.arr π κ₁ κ₂) F G ↔
      ∀ X Y, Good W κ₁ X → Good W κ₁ Y → PolRel W π κ₁ X Y → SemLe W κ₂ (F X) (G Y) :=
  Iff.rfl

theorem good_star_arr {W : World} {ι₁ ι₂ : SKind} {F : Sem (.arr ι₁ ι₂)} :
    ¬ Good W .star F := fun h => h

theorem good_arr_star {W : World} {π : Pol} {κ₁ κ₂ : Kind} {A : Sem .star} :
    ¬ Good W (.arr π κ₁ κ₂) A := fun h => h

/-! ## Reflexivity and transitivity -/

theorem Good.refl {W : World} : ∀ {κ : Kind} {ι : SKind} {X : Sem ι}, Good W κ X → SemLe W κ X X
  | .star, .star, _, _ => subset_refl _
  | .arr _ _ _, .arr _ _, _, h => h.2
  | .arr _ _ _, .star, _, h => absurd h good_arr_star
  | .star, .arr _ _, _, h => absurd h good_star_arr

theorem PolRel.refl {W : World} (π : Pol) {κ : Kind} {ι : SKind} {X : Sem ι}
    (h : Good W κ X) : PolRel W π κ X X := by
  have := Good.refl h
  cases π <;> simp [PolRel, polRelOf, this]

theorem SemLe.trans {W : World} :
    ∀ {κ : Kind} {ι : SKind} {X Y Z : Sem ι}, Good W κ X → Good W κ Y → Good W κ Z →
      SemLe W κ X Y → SemLe W κ Y Z → SemLe W κ X Z
  | .star, .star, _, _, _, _, _, _, h₁, h₂ => Set.Subset.trans h₁ h₂
  | .arr π κ₁ κ₂, .arr ι₁ ι₂, F, G, H, hF, hG, hH, h₁, h₂ => by
    intro X Y hX hY hXY
    exact SemLe.trans (hF.1 X hX) (hG.1 X hX) (hH.1 Y hY)
      (h₁ X X hX hX (PolRel.refl π hX)) (h₂ X Y hX hY hXY)
  | .arr _ _ _, .star, _, _, _, h, _, _, _, _ => absurd h good_arr_star
  | .star, .arr _ _, _, _, _, h, _, _, _, _ => absurd h good_star_arr

/-- Antisymmetry at kind `*`. -/
theorem semLe_star_antisymm {W : World} {A B : Set Tm} (h₁ : SemLe W .star (ι := .star) A B)
    (h₂ : SemLe W .star (ι := .star) B A) : A = B :=
  Set.Subset.antisymm h₁ h₂

/-! ## Subkinding -/

theorem SubKind.erase_eq {κ κ' : Kind} (h : SubKind κ κ') : κ.erase = κ'.erase := by
  induction h with
  | star => rfl
  | arr _ _ _ ih₁ ih₂ => simp [Kind.erase, ih₁, ih₂]

theorem SubKind.refl : ∀ κ : Kind, SubKind κ κ
  | .star => .star
  | .arr π κ₁ κ₂ => .arr (Pol.le_refl π) (SubKind.refl κ₁) (SubKind.refl κ₂)

/-- Goodness and order are transported along subkinding. -/
theorem SubKind.sem {W : World} {κ κ' : Kind} (h : SubKind κ κ') :
    ∀ {ι : SKind}, (∀ X : Sem ι, Good W κ X → Good W κ' X) ∧
      (∀ X Y : Sem ι, Good W κ X → Good W κ Y → SemLe W κ X Y → SemLe W κ' X Y) := by
  induction h with
  | star =>
    intro ι
    exact ⟨fun _ h => h, fun _ _ _ _ h => h⟩
  | @arr π π' κ₁ κ₁' κ₂ κ₂' hπ _ _ ih₁ ih₂ =>
    intro ι
    cases ι with
    | star => exact ⟨fun _ h => absurd h good_arr_star, fun _ _ h => absurd h good_arr_star⟩
    | arr ι₁ ι₂ =>
      have hrel : ∀ X Y : Sem ι₁, Good W κ₁' X → Good W κ₁' Y → PolRel W π' κ₁' X Y →
          PolRel W π κ₁ X Y := by
        intro X Y hX hY hXY
        apply polRelOf_mono hπ
        cases π' <;> simp only [PolRel, polRelOf] at hXY ⊢
        · exact ⟨ih₁.2 X Y hX hY hXY.1, ih₁.2 Y X hY hX hXY.2⟩
        · exact ih₁.2 X Y hX hY hXY
        · exact ih₁.2 Y X hY hX hXY
      refine ⟨fun F hF => ⟨fun X hX => ih₂.1 _ (hF.1 X (ih₁.1 X hX)), ?_⟩, ?_⟩
      · intro X Y hX hY hXY
        exact ih₂.2 _ _ (hF.1 X (ih₁.1 X hX)) (hF.1 Y (ih₁.1 Y hY))
          (hF.2 X Y (ih₁.1 X hX) (ih₁.1 Y hY) (hrel X Y hX hY hXY))
      · intro F G hF hG hFG X Y hX hY hXY
        exact ih₂.2 _ _ (hF.1 X (ih₁.1 X hX)) (hG.1 Y (ih₁.1 Y hY))
          (hFG X Y (ih₁.1 X hX) (ih₁.1 Y hY) (hrel X Y hX hY hXY))

theorem Good.sub {W : World} {κ κ' : Kind} (h : SubKind κ κ') {ι : SKind} {X : Sem ι}
    (hX : Good W κ X) : Good W κ' X :=
  (SubKind.sem h).1 X hX

theorem SemLe.sub {W : World} {κ κ' : Kind} (h : SubKind κ κ') {ι : SKind} {X Y : Sem ι}
    (hX : Good W κ X) (hY : Good W κ Y) (hXY : SemLe W κ X Y) : SemLe W κ' X Y :=
  (SubKind.sem h).2 X Y hX hY hXY

/-! ## Variance-directed relations -/

theorem PolRel.symm_mix {W : World} {κ : Kind} {ι : SKind} {X Y : Sem ι}
    (h : PolRel W .mix κ X Y) : PolRel W .mix κ Y X := ⟨h.2, h.1⟩

theorem PolRel.top {W : World} {κ : Kind} {ι : SKind} (X Y : Sem ι) : PolRel W .top κ X Y :=
  trivial

theorem PolRel.of_mix {W : World} (π : Pol) {κ : Kind} {ι : SKind} {X Y : Sem ι}
    (h : PolRel W .mix κ X Y) : PolRel W π κ X Y :=
  polRelOf_mono (π' := .mix) trivial h

end NishtAbel2024V5
