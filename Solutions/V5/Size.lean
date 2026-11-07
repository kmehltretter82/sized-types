import Solutions.V5.Kind

/-! # V5: sizes — increments, bound normalization, soundness of size judgments (Theorem 2) -/

namespace NishtAbel2024V5

open Order

theorem add_nat_lt_add_nat {α β : Ordinal.{0}} (h : α < β) (n : Nat) : α + n < β + n := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, ← add_assoc, ← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
    exact Order.succ_lt_succ ih

theorem add_nat_le_add_nat {α β : Ordinal.{0}} (h : α ≤ β) (n : Nat) : α + n ≤ β + n :=
  add_le_add h le_rfl

theorem min_add_nat (α β : Ordinal.{0}) (n : Nat) : min α β + n = min (α + n) (β + n) := by
  rcases le_total α β with h | h
  · rw [min_eq_left h, min_eq_left (add_nat_le_add_nat h n)]
  · rw [min_eq_right h, min_eq_right (add_nat_le_add_nat h n)]

theorem lt_add_one_iff_le' {α β : Ordinal.{0}} : α < β + 1 ↔ α ≤ β := by
  rw [← Order.succ_eq_add_one, Order.lt_succ_iff]

theorem omega_le_add_nat (n : Nat) : Omega ≤ Omega + n := le_self_add

theorem SizeCtx.mem_dom {Ψ : SizeCtx} {i : Nat} {a : Size} (h : (i, a) ∈ Ψ) : i ∈ Ψ.dom :=
  List.mem_map.mpr ⟨(i, a), h, rfl⟩

@[simp] theorem SizeCtx.dom_append (Ψ Ψ' : SizeCtx) : (Ψ ++ Ψ').dom = Ψ.dom ++ Ψ'.dom := by
  simp [SizeCtx.dom]

@[simp] theorem SizeCtx.dom_cons (p : Nat × Size) (Ψ : SizeCtx) :
    SizeCtx.dom (p :: Ψ) = p.1 :: Ψ.dom := rfl

@[simp] theorem SizeCtx.dom_nil : SizeCtx.dom [] = [] := rfl

/-! ## Increments -/

theorem sizeVal_shift (ρ : SizeVal) (ζ : SzEnv) :
    ∀ (a : Size) (n : Nat), sizeVal ρ ζ (a.shift n) = sizeVal ρ ζ a + n
  | .inf m, n => by simp [Size.shift, sizeVal, Nat.cast_add, add_assoc]
  | .var i m, n => by simp [Size.shift, sizeVal, Nat.cast_add, add_assoc]
  | .bvar k m, n => by simp [Size.shift, sizeVal, Nat.cast_add, add_assoc]
  | .meet a b, n => by
    simp only [Size.shift, sizeVal]
    rw [sizeVal_shift ρ ζ a n, sizeVal_shift ρ ζ b n, min_add_nat]

theorem Size.shift_zero : ∀ a : Size, a.shift 0 = a
  | .inf _ => rfl
  | .var _ _ => rfl
  | .bvar _ _ => rfl
  | .meet a b => by simp [Size.shift, Size.shift_zero a, Size.shift_zero b]

theorem Size.shift_shift : ∀ (a : Size) (m n : Nat), (a.shift m).shift n = a.shift (m + n)
  | .inf _, m, n => by simp [Size.shift, Nat.add_assoc]
  | .var _ _, m, n => by simp [Size.shift, Nat.add_assoc]
  | .bvar _ _, m, n => by simp [Size.shift, Nat.add_assoc]
  | .meet a b, m, n => by simp [Size.shift, Size.shift_shift a, Size.shift_shift b]

theorem SizeWfAt.shift {Ψ : SizeCtx} {m : Nat} :
    ∀ {a : Size} (n : Nat), SizeWfAt Ψ m a → SizeWfAt Ψ m (a.shift n)
  | .inf _, _, _ => trivial
  | .var _ _, _, h => h
  | .bvar _ _, _, h => h
  | .meet _ _, n, h => ⟨SizeWfAt.shift n h.1, SizeWfAt.shift n h.2⟩

theorem SizeWfAt.of_shift {Ψ : SizeCtx} {m : Nat} :
    ∀ {a : Size} {n : Nat}, SizeWfAt Ψ m (a.shift n) → SizeWfAt Ψ m a
  | .inf _, _, _ => trivial
  | .var _ _, _, h => h
  | .bvar _ _, _, h => h
  | .meet _ _, _, h => ⟨SizeWfAt.of_shift h.1, SizeWfAt.of_shift h.2⟩

/-! ## Bound normalization -/

theorem omega_le_sizeVal_up (ρ : SizeVal) (ζ : SzEnv) :
    ∀ a : Size, Omega ≤ sizeVal ρ ζ a → Omega ≤ sizeVal ρ ζ a.up
  | .inf _, _ => by simp only [Size.up, sizeVal]; exact omega_le_add_nat 1
  | .var _ _, h => h
  | .bvar _ _, h => h
  | .meet a b, h => by
    simp only [Size.up, sizeVal, le_min_iff] at h ⊢
    exact ⟨omega_le_sizeVal_up ρ ζ a h.1, omega_le_sizeVal_up ρ ζ b h.2⟩

theorem sizeVal_up_of_lt (ρ : SizeVal) (ζ : SzEnv) :
    ∀ a : Size, sizeVal ρ ζ a < Omega → sizeVal ρ ζ a.up = sizeVal ρ ζ a
  | .inf n, h => by
    simp only [sizeVal] at h
    exact absurd h (not_lt.mpr (omega_le_add_nat n))
  | .var _ _, _ => rfl
  | .bvar _ _, _ => rfl
  | .meet a b, h => by
    simp only [Size.up, sizeVal] at h ⊢
    rcases le_total (sizeVal ρ ζ a) (sizeVal ρ ζ b) with hab | hab
    · rw [min_eq_left hab] at h ⊢
      rw [sizeVal_up_of_lt ρ ζ a h]
      by_cases hb : sizeVal ρ ζ b < Omega
      · rw [sizeVal_up_of_lt ρ ζ b hb, min_eq_left hab]
      · have := omega_le_sizeVal_up ρ ζ b (not_lt.mp hb)
        exact min_eq_left (h.le.trans this)
    · rw [min_eq_right hab] at h ⊢
      rw [sizeVal_up_of_lt ρ ζ b h]
      by_cases ha : sizeVal ρ ζ a < Omega
      · rw [sizeVal_up_of_lt ρ ζ a ha, min_eq_right hab]
      · have := omega_le_sizeVal_up ρ ζ a (not_lt.mp ha)
        exact min_eq_right (h.le.trans this)

/-- An ordinal below `⟦a^↑⟧` is below `⟦a⟧`, unless `⟦a⟧ ≥ Ω`. -/
theorem lt_up_cases (ρ : SizeVal) (ζ : SzEnv) (a : Size) {β : Ordinal.{0}}
    (h : β < sizeVal ρ ζ a.up) : β < sizeVal ρ ζ a ∨ Omega ≤ sizeVal ρ ζ a := by
  by_cases ha : sizeVal ρ ζ a < Omega
  · rw [sizeVal_up_of_lt ρ ζ a ha] at h
    exact Or.inl h
  · exact Or.inr (not_lt.mp ha)

/-- Comparison of bound normalizations. -/
theorem le_of_up_le (ρ : SizeVal) (ζ : SzEnv) (a b : Size)
    (h : sizeVal ρ ζ a.up ≤ sizeVal ρ ζ b.up) :
    sizeVal ρ ζ a ≤ sizeVal ρ ζ b ∨ (Omega ≤ sizeVal ρ ζ a ∧ Omega ≤ sizeVal ρ ζ b) := by
  by_cases ha : sizeVal ρ ζ a < Omega
  · left
    rw [sizeVal_up_of_lt ρ ζ a ha] at h
    by_cases hb : sizeVal ρ ζ b < Omega
    · rwa [sizeVal_up_of_lt ρ ζ b hb] at h
    · exact ha.le.trans (not_lt.mp hb)
  · right
    refine ⟨not_lt.mp ha, ?_⟩
    by_contra hb
    have hb' := not_le.mp hb
    have hu := omega_le_sizeVal_up ρ ζ a (not_lt.mp ha)
    rw [sizeVal_up_of_lt ρ ζ b hb'] at h
    exact absurd (hu.trans h) (not_le.mpr hb')

/-- Comparison with a bound normalization. -/
theorem le_of_le_up (ρ : SizeVal) (ζ : SzEnv) (a b : Size)
    (h : sizeVal ρ ζ a ≤ sizeVal ρ ζ b.up) :
    sizeVal ρ ζ a ≤ sizeVal ρ ζ b ∨ (Omega ≤ sizeVal ρ ζ a ∧ Omega ≤ sizeVal ρ ζ b) := by
  by_cases hb : sizeVal ρ ζ b < Omega
  · left; rwa [sizeVal_up_of_lt ρ ζ b hb] at h
  · by_cases ha : sizeVal ρ ζ a < Omega
    · left; exact ha.le.trans (not_lt.mp hb)
    · right; exact ⟨not_lt.mp ha, not_lt.mp hb⟩

/-! ## Well-formedness of compared sizes -/

theorem SizeLt.wf {Ψ : SizeCtx} {a b : Size} (h : SizeLt Ψ a b) : SizeWf Ψ a ∧ SizeWf Ψ b := by
  induction h with
  | inf_inf _ => exact ⟨trivial, trivial⟩
  | var_var hi _ => exact ⟨hi, hi⟩
  | bound hm _ ih => exact ⟨SizeCtx.mem_dom hm, SizeWfAt.of_shift ih.2⟩
  | var_inf hm _ _ => exact ⟨SizeCtx.mem_dom hm, trivial⟩
  | meet_l _ hb ih => exact ⟨⟨ih.1, hb⟩, ih.2⟩
  | meet_r _ ha ih => exact ⟨⟨ha, ih.1⟩, ih.2⟩
  | lt_meet _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₁.2, ih₂.2⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩

/-! ## Theorem 2: soundness of size judgments -/

/-- `ρ ≤ ρ'` on the variables of `Ψ`. -/
def ValLe (Ψ : SizeCtx) (ρ ρ' : SizeVal) : Prop := ∀ i ∈ Ψ.dom, ρ i ≤ ρ' i

theorem ValLe.refl (Ψ : SizeCtx) (ρ : SizeVal) : ValLe Ψ ρ ρ := fun _ _ => le_rfl

/-- Theorem 2.1: well-formed sizes are monotone in the valuation. -/
theorem sizeWf_sound {Ψ : SizeCtx} {ρ ρ' : SizeVal} (hle : ValLe Ψ ρ ρ') (ζ : SzEnv) :
    ∀ {a : Size}, SizeWf Ψ a → sizeVal ρ ζ a ≤ sizeVal ρ' ζ a
  | .inf _, _ => le_rfl
  | .var i n, h => add_nat_le_add_nat (hle i h) n
  | .bvar _ _, h => absurd h (Nat.not_lt_zero _)
  | .meet _ _, h => min_le_min (sizeWf_sound hle ζ h.1) (sizeWf_sound hle ζ h.2)

/-- Theorem 2.3: strict size comparison is sound for ordered valid valuations. -/
theorem sizeLt_sound2 {Ψ : SizeCtx} {a b : Size} (h : SizeLt Ψ a b) :
    ∀ {ρ ρ' : SizeVal}, ValidVal Ψ ρ → ValidVal Ψ ρ' → ValLe Ψ ρ ρ' →
      sizeVal ρ SzEnv.zero a < sizeVal ρ' SzEnv.zero b := by
  induction h with
  | inf_inf hnm =>
    intro ρ ρ' _ _ _
    simp only [sizeVal]
    exact (add_lt_add_iff_left _).mpr (by exact_mod_cast hnm)
  | var_var hi hnm =>
    intro ρ ρ' _ _ hle
    simp only [sizeVal]
    exact lt_of_le_of_lt (add_nat_le_add_nat (hle _ hi) _)
      ((add_lt_add_iff_left _).mpr (by exact_mod_cast hnm))
  | @bound i n a b hm _ ih =>
    intro ρ ρ' hv hv' hle
    have h1 := ih hv hv' hle
    rw [sizeVal_shift, sizeVal_shift] at h1
    have h2 : sizeVal ρ SzEnv.zero a + n ≤ sizeVal ρ' SzEnv.zero b :=
      lt_add_one_iff_le'.mp (by simpa using h1)
    have h3 : ρ i + n < sizeVal ρ SzEnv.zero a + n := add_nat_lt_add_nat (hv _ hm) n
    exact lt_of_lt_of_le h3 h2
  | @var_inf i n m a hm _ ih =>
    intro ρ ρ' hv hv' hle
    have h1 := ih hv hv (ValLe.refl _ _)
    simp only [sizeVal] at h1 ⊢
    have h2 : sizeVal ρ SzEnv.zero a ≤ Omega := by
      have : sizeVal ρ SzEnv.zero a < Omega + 1 := by exact_mod_cast h1
      exact lt_add_one_iff_le'.mp this
    have h3 : ρ i < Omega := lt_of_lt_of_le (hv _ hm) h2
    exact lt_of_lt_of_le (add_nat_lt_omega h3 n) (omega_le_add_nat m)
  | meet_l _ _ ih =>
    intro ρ ρ' hv hv' hle
    exact lt_of_le_of_lt (min_le_left _ _) (ih hv hv' hle)
  | meet_r _ _ ih =>
    intro ρ ρ' hv hv' hle
    exact lt_of_le_of_lt (min_le_right _ _) (ih hv hv' hle)
  | lt_meet _ _ ih₁ ih₂ =>
    intro ρ ρ' hv hv' hle
    exact lt_min (ih₁ hv hv' hle) (ih₂ hv hv' hle)
  | trans _ _ ih₁ ih₂ =>
    intro ρ ρ' hv hv' hle
    exact lt_trans (ih₁ hv hv' hle) (ih₂ hv' hv' (ValLe.refl _ _))

/-- Theorem 2.2: non-strict size comparison is sound for ordered valid valuations. -/
theorem sizeLe_sound2 {Ψ : SizeCtx} {a b : Size} (h : SizeLe Ψ a b) {ρ ρ' : SizeVal}
    (hv : ValidVal Ψ ρ) (hv' : ValidVal Ψ ρ') (hle : ValLe Ψ ρ ρ') :
    sizeVal ρ SzEnv.zero a ≤ sizeVal ρ' SzEnv.zero b := by
  have := sizeLt_sound2 h hv hv' hle
  rw [sizeVal_shift] at this
  exact lt_add_one_iff_le'.mp (by exact_mod_cast this)

theorem sizeLt_sound {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {a b : Size}
    (h : SizeLt Ψ a b) : sizeVal ρ SzEnv.zero a < sizeVal ρ SzEnv.zero b :=
  sizeLt_sound2 h hv hv (ValLe.refl _ _)

theorem sizeLe_sound {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {a b : Size}
    (h : SizeLe Ψ a b) : sizeVal ρ SzEnv.zero a ≤ sizeVal ρ SzEnv.zero b :=
  sizeLe_sound2 h hv hv (ValLe.refl _ _)

/-! ## Size environments -/

def SzEnv.insert (k : Nat) (β : Ordinal.{0}) (ζ : SzEnv) : SzEnv := fun x =>
  if x < k then ζ x else if x = k then β else ζ (x - 1)

theorem SzEnv.insert_succ_cons (k : Nat) (β γ : Ordinal.{0}) (ζ : SzEnv) :
    SzEnv.insert (k + 1) β (SzEnv.cons γ ζ) = SzEnv.cons γ (SzEnv.insert k β ζ) := by
  funext x
  cases x with
  | zero => simp [SzEnv.insert, SzEnv.cons]
  | succ y =>
    simp only [SzEnv.insert, SzEnv.cons]
    by_cases h1 : y < k
    · simp [h1]
    · by_cases h2 : y = k
      · subst h2; simp
      · have h3 : ¬ y + 1 < k + 1 := by omega
        have h4 : y + 1 ≠ k + 1 := by omega
        simp only [h1, h2, h3, h4, if_false]
        cases y with
        | zero => omega
        | succ z => rfl

theorem SzEnv.insert_zero (β : Ordinal.{0}) (ζ : SzEnv) :
    SzEnv.insert 0 β ζ = SzEnv.cons β ζ := by
  funext x
  cases x with
  | zero => simp [SzEnv.insert, SzEnv.cons]
  | succ y => simp [SzEnv.insert, SzEnv.cons]

/-! ## Agreement -/

theorem sizeVal_agree {Ψ : SizeCtx} {m : Nat} {ρ ρ' : SizeVal} {ζ ζ' : SzEnv}
    (hρ : ∀ i ∈ Ψ.dom, ρ i = ρ' i) (hζ : ∀ x < m, ζ x = ζ' x) :
    ∀ {a : Size}, SizeWfAt Ψ m a → sizeVal ρ ζ a = sizeVal ρ' ζ' a
  | .inf _, _ => rfl
  | .var i n, ha => by simp only [sizeVal, hρ i ha]
  | .bvar k n, ha => by simp only [sizeVal, hζ k ha]
  | .meet _ _, ha => by
    simp only [sizeVal, sizeVal_agree hρ hζ ha.1, sizeVal_agree hρ hζ ha.2]

theorem SzEnv.cons_agree {ζ ζ' : SzEnv} {m : Nat} (h : ∀ x < m, ζ x = ζ' x) (β : Ordinal.{0}) :
    ∀ x < m + 1, SzEnv.cons β ζ x = SzEnv.cons β ζ' x
  | 0, _ => rfl
  | x + 1, hx => h x (by omega)

/-- Locally closed sizes do not depend on the bound-size environment. -/
theorem sizeVal_closed {Ψ : SizeCtx} {a : Size} (ha : SizeWf Ψ a) (ρ : SizeVal) (ζ ζ' : SzEnv) :
    sizeVal ρ ζ a = sizeVal ρ ζ' a :=
  sizeVal_agree (fun _ _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _)) ha

/-! ## Locally closed sizes and substitution -/

/-- A size without bound size variables. -/
def Size.LC : Size → Prop
  | .inf _ => True
  | .var _ _ => True
  | .bvar _ _ => False
  | .meet a b => a.LC ∧ b.LC

theorem Size.LC.of_wf {Ψ : SizeCtx} : ∀ {a : Size}, SizeWf Ψ a → a.LC
  | .inf _, _ => trivial
  | .var _ _, _ => trivial
  | .bvar _ _, h => absurd h (Nat.not_lt_zero _)
  | .meet _ _, h => ⟨Size.LC.of_wf h.1, Size.LC.of_wf h.2⟩

theorem sizeVal_lc (ρ : SizeVal) (ζ ζ' : SzEnv) : ∀ {a : Size}, a.LC → sizeVal ρ ζ a = sizeVal ρ ζ' a
  | .inf _, _ => rfl
  | .var _ _, _ => rfl
  | .bvar _ _, h => absurd h id
  | .meet _ _, h => by simp only [sizeVal, sizeVal_lc ρ ζ ζ' h.1, sizeVal_lc ρ ζ ζ' h.2]

theorem Size.LC.shift : ∀ {a : Size} (n : Nat), a.LC → (a.shift n).LC
  | .inf _, _, _ => trivial
  | .var _ _, _, _ => trivial
  | .bvar _ _, _, h => h
  | .meet _ _, n, h => ⟨Size.LC.shift n h.1, Size.LC.shift n h.2⟩

/-- Substitutions of locally closed sizes. -/
def LCSubst (σ : List (Nat × Size)) : Prop := ∀ i b, σ.lookup i = some b → b.LC

/-- The valuation induced by a size substitution. -/
noncomputable def substVal (ρ : SizeVal) (σ : List (Nat × Size)) : SizeVal := fun i =>
  match σ.lookup i with
  | some b => sizeVal ρ SzEnv.zero b
  | none => ρ i

theorem sizeVal_subst {σ : List (Nat × Size)} (hσ : LCSubst σ) (ρ : SizeVal) (ζ : SzEnv) :
    ∀ a : Size, sizeVal ρ ζ (a.subst σ) = sizeVal (substVal ρ σ) ζ a
  | .inf _ => rfl
  | .bvar _ _ => rfl
  | .var i n => by
    simp only [Size.subst, sizeVal, substVal]
    cases h : σ.lookup i with
    | none => rfl
    | some b =>
      simp only
      rw [sizeVal_shift, sizeVal_lc ρ ζ SzEnv.zero (hσ i b h)]
  | .meet a b => by
    simp only [Size.subst, sizeVal, sizeVal_subst hσ ρ ζ a, sizeVal_subst hσ ρ ζ b]

/-! ## Opening bound size variables -/

theorem sizeVal_openAt (ρ : SizeVal) (ζ : SzEnv) (k : Nat) {b : Size} (hb : b.LC) :
    ∀ a : Size, sizeVal ρ ζ (a.openAt k b) = sizeVal ρ (SzEnv.insert k (sizeVal ρ ζ b) ζ) a
  | .inf _ => rfl
  | .var _ _ => rfl
  | .bvar k' n => by
    by_cases h1 : k' = k
    · subst h1
      simp [Size.openAt, sizeVal, SzEnv.insert, sizeVal_shift]
    · by_cases h2 : k < k'
      · have h3 : ¬ k' < k := by omega
        simp [Size.openAt, h1, h2, h3, sizeVal, SzEnv.insert]
      · have h3 : k' < k := by omega
        simp [Size.openAt, h1, h2, h3, sizeVal, SzEnv.insert]
  | .meet a₁ a₂ => by
    simp only [Size.openAt, sizeVal, sizeVal_openAt ρ ζ k hb a₁, sizeVal_openAt ρ ζ k hb a₂]

end NishtAbel2024V5
