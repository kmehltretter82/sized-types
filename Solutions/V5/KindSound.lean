import Solutions.V5.Interp

/-! # V5: soundness of kinding

Every well-kinded type denotes a good semantic value of its kind, and the interpretation respects
the polarities of the variables: for environments related along the declared polarities, the
interpretations are ordered. -/

namespace NishtAbel2024V5

/-! ## Stages for candidate-preserving functors -/

theorem muSet_cand {W : World} (hW : WorldClosed W) (F : Nat → Set Tm → Set Tm) (α : Ordinal.{0}) :
    Cand W (MuSet W F α) := by
  rw [MuSet_eq]; exact introSet_cand hW _

theorem muSet_mono_cand {W : World} (hW : WorldClosed W) {F F' : Nat → Set Tm → Set Tm}
    (h : ∀ c 𝒳 𝒴, Cand W 𝒳 → Cand W 𝒴 → 𝒳 ⊆ 𝒴 → F c 𝒳 ⊆ F' c 𝒴) (α : Ordinal.{0}) :
    MuSet W F α ⊆ MuSet W F' α := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [MuSet_eq, MuSet_eq]
    exact introSet_mono fun _ ⟨c, t, β, hβ, hv, ht⟩ =>
      ⟨c, t, β, hβ, hv, h c _ _ (muSet_cand hW F β) (muSet_cand hW F' β) (ih β hβ) ht⟩

theorem muSet_congr_cand {W : World} (hW : WorldClosed W) {F F' : Nat → Set Tm → Set Tm}
    (h : ∀ c 𝒳, Cand W 𝒳 → F c 𝒳 = F' c 𝒳) (α : Ordinal.{0}) :
    MuSet W F α = MuSet W F' α := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [MuSet_eq, MuSet_eq]
    congr 1
    funext v
    apply propext
    constructor
    · rintro ⟨c, t, β, hβ, hv, ht⟩
      refine ⟨c, t, β, hβ, hv, ?_⟩
      have e := h c _ (muSet_cand hW F β)
      rw [← ih β hβ, ← e]
      exact ht
    · rintro ⟨c, t, β, hβ, hv, ht⟩
      refine ⟨c, t, β, hβ, hv, ?_⟩
      have e := h c _ (muSet_cand hW F β)
      rw [e, ih β hβ]
      exact ht

theorem nuSet_mono_cand {W : World} (hW : WorldClosed W) {n : Nat}
    {G G' : Nat → Set Tm → Set Tm} (hG : ∀ d < n, ∀ 𝒳, Cand W 𝒳 → Cand W (G d 𝒳))
    (hG' : ∀ d < n, ∀ 𝒳, Cand W 𝒳 → Cand W (G' d 𝒳))
    (h : ∀ d < n, ∀ 𝒳 𝒴, Cand W 𝒳 → Cand W 𝒴 → 𝒳 ⊆ 𝒴 → G d 𝒳 ⊆ G' d 𝒴)
    (α : Ordinal.{0}) : NuSet W n G α ⊆ NuSet W n G' α := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [NuSet_eq, NuSet_eq]
    exact fun _ ht => ⟨ht.1, fun β hβ d hd =>
      h d hd _ _ (nuSet_cand hW n hG β) (nuSet_cand hW n hG' β) (ih β hβ) (ht.2 β hβ d hd)⟩

theorem nuSet_congr_cand {W : World} (hW : WorldClosed W) {n : Nat}
    {G G' : Nat → Set Tm → Set Tm} (hG : ∀ d < n, ∀ 𝒳, Cand W 𝒳 → Cand W (G d 𝒳))
    (h : ∀ d < n, ∀ 𝒳, Cand W 𝒳 → G d 𝒳 = G' d 𝒳) (α : Ordinal.{0}) :
    NuSet W n G α = NuSet W n G' α := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [NuSet_eq, NuSet_eq]
    ext t
    constructor
    · intro ht
      refine ⟨ht.1, fun β hβ d hd => ?_⟩
      rw [← ih β hβ, ← h d hd _ (nuSet_cand hW n hG β)]
      exact ht.2 β hβ d hd
    · intro ht
      refine ⟨ht.1, fun β hβ d hd => ?_⟩
      rw [h d hd _ (nuSet_cand hW n hG β), ih β hβ]
      exact ht.2 β hβ d hd

/-! ## Equations of the interpretation at kind `*` -/

theorem interp_unit_star (W : World) (ρ : SizeVal) (θ : TEnv) (ζ : SzEnv) (η : Env) :
    interp W ρ θ .unit .star ζ η = UnitSet W := rfl

theorem interp_prod_star (W : World) (ρ : SizeVal) (θ : TEnv) (A B : Ty) (ζ : SzEnv) (η : Env) :
    interp W ρ θ (.prod A B) .star ζ η =
      ProdSet W (interp W ρ θ A .star ζ η) (interp W ρ θ B .star ζ η) := rfl

theorem interp_arr_star (W : World) (ρ : SizeVal) (θ : TEnv) (A B : Ty) (ζ : SzEnv) (η : Env) :
    interp W ρ θ (.arr A B) .star ζ η =
      ArrSet W (interp W ρ θ A .star ζ η) (interp W ρ θ B .star ζ η) := rfl

theorem interp_mu_star (W : World) (ρ : SizeVal) (θ : TEnv) (a : Size) (S : List Ty)
    (ζ : SzEnv) (η : Env) :
    interp W ρ θ (.mu a S) .star ζ η =
      MuSet W (fun c 𝒳 => interpAt W ρ θ S c ζ (Env.cons (PSem.ofSem .star 𝒳) η))
        (sizeVal ρ ζ a) := rfl

theorem interp_nu_star (W : World) (ρ : SizeVal) (θ : TEnv) (a : Size) (R : List Ty)
    (ζ : SzEnv) (η : Env) :
    interp W ρ θ (.nu a R) .star ζ η =
      NuSet W R.length (fun d 𝒳 => interpAt W ρ θ R d ζ (Env.cons (PSem.ofSem .star 𝒳) η))
        (sizeVal ρ ζ a) := rfl

theorem interp_allT_star (W : World) (ρ : SizeVal) (θ : TEnv) (κ : Kind) (B : Ty) (ζ : SzEnv)
    (η : Env) :
    interp W ρ θ (.allT κ B) .star ζ η =
      AllTSet W κ (fun X => interp W ρ θ B .star ζ (Env.cons (PSem.ofSem κ.erase X) η)) := rfl

theorem interp_exT_star (W : World) (ρ : SizeVal) (θ : TEnv) (κ : Kind) (B : Ty) (ζ : SzEnv)
    (η : Env) :
    interp W ρ θ (.exT κ B) .star ζ η =
      ExTSet W κ (fun X => interp W ρ θ B .star ζ (Env.cons (PSem.ofSem κ.erase X) η)) := rfl

theorem interp_allS_star (W : World) (ρ : SizeVal) (θ : TEnv) (a : Size) (B : Ty) (ζ : SzEnv)
    (η : Env) :
    interp W ρ θ (.allS a B) .star ζ η =
      AllSSet W (sizeVal ρ ζ a) (fun β => interp W ρ θ B .star (SzEnv.cons β ζ) η) := rfl

theorem interp_exS_star (W : World) (ρ : SizeVal) (θ : TEnv) (a : Size) (B : Ty) (ζ : SzEnv)
    (η : Env) :
    interp W ρ θ (.exS a B) .star ζ η =
      ExSSet W (sizeVal ρ ζ a) (fun β => interp W ρ θ B .star (SzEnv.cons β ζ) η) := rfl

theorem interp_lam_arr (W : World) (ρ : SizeVal) (θ : TEnv) (ι : SKind) (F : Ty)
    (ι₁ ι₂ : SKind) (ζ : SzEnv) (η : Env) :
    interp W ρ θ (.lam ι F) (.arr ι₁ ι₂) ζ η =
      fun X => interp W ρ θ F ι₂ ζ (Env.cons (PSem.ofSem ι₁ X) η) := rfl

theorem interp_app (W : World) (ρ : SizeVal) (θ : TEnv) (F G : Ty) (ι₁ ι : SKind) (ζ : SzEnv)
    (η : Env) :
    interp W ρ θ (.app F G ι₁) ι ζ η =
      interp W ρ θ F (.arr ι₁ ι) ζ η (interp W ρ θ G ι₁ ζ η) := rfl

@[simp] theorem Kind.erase_star : Kind.star.erase = SKind.star := rfl

@[simp] theorem Kind.erase_arr (π : Pol) (κ₁ κ₂ : Kind) :
    (Kind.arr π κ₁ κ₂).erase = SKind.arr κ₁.erase κ₂.erase := rfl

/-! ## Related environments -/

/-- Free type variables: good at their kinds, and related along their polarities. -/
def TRel (W : World) (Δ : KCtx) (θ θ' : TEnv) : Prop :=
  ∀ X π κ, Δ.lookup X = some (π, κ) →
    Good W κ (θ X κ.erase) ∧ Good W κ (θ' X κ.erase) ∧ PolRel W π κ (θ X κ.erase) (θ' X κ.erase)

/-- Bound type variables: good at their kinds, and related along their polarities. -/
def BRel (W : World) (Δb : BCtx) (η η' : Env) : Prop :=
  ∀ k π κ, Δb[k]? = some (π, κ) →
    Good W κ (η k κ.erase) ∧ Good W κ (η' k κ.erase) ∧ PolRel W π κ (η k κ.erase) (η' k κ.erase)

theorem KCtx.lookup_inv (π : Pol) :
    ∀ (Δ : KCtx) (X : Nat), (Δ.inv π).lookup X = (Δ.lookup X).map fun e => (Pol.inv π e.1, e.2)
  | [], _ => rfl
  | (Y, π', κ) :: Δ, X => by
    have ih := KCtx.lookup_inv π Δ X
    simp only [KCtx.inv] at ih ⊢
    simp only [List.map, List.lookup]
    by_cases h : X = Y
    · subst h; simp
    · have hb : (X == Y) = false := by simpa using h
      rw [hb]
      exact ih

theorem BCtx.getElem?_inv (π : Pol) (Δb : BCtx) (k : Nat) :
    (Δb.inv π)[k]? = (Δb[k]?).map fun e => (Pol.inv π e.1, e.2) := by
  simp [BCtx.inv]

/-- How `π⁻¹` acts on related pairs. -/
theorem polRel_inv {W : World} {π π' : Pol} {κ : Kind} {ι : SKind} {X Y : Sem ι}
    (hX : Good W κ X) (hY : Good W κ Y) (h : PolRel W π' κ X Y) :
    (π = .pos → PolRel W (Pol.inv π π') κ X Y) ∧
    (π = .neg → PolRel W (Pol.inv π π') κ Y X) ∧
    (π = .mix → PolRel W (Pol.inv π π') κ X Y ∧ PolRel W (Pol.inv π π') κ Y X) ∧
    (π = .top → PolRel W (Pol.inv π π') κ X X) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl; exact h
  · rintro rfl
    cases π' <;> simp_all [Pol.inv, Pol.negate, PolRel, polRelOf]
  · rintro rfl
    cases π' <;> simp_all [Pol.inv, PolRel, polRelOf]
  · rintro rfl
    exact PolRel.refl _ hX

theorem TRel.left {W : World} {Δ : KCtx} {θ θ' : TEnv} (h : TRel W Δ θ θ') : TRel W Δ θ θ :=
  fun X π κ hX => ⟨(h X π κ hX).1, (h X π κ hX).1, PolRel.refl π (h X π κ hX).1⟩

theorem TRel.right {W : World} {Δ : KCtx} {θ θ' : TEnv} (h : TRel W Δ θ θ') : TRel W Δ θ' θ' :=
  fun X π κ hX => ⟨(h X π κ hX).2.1, (h X π κ hX).2.1, PolRel.refl π (h X π κ hX).2.1⟩

theorem BRel.left {W : World} {Δb : BCtx} {η η' : Env} (h : BRel W Δb η η') : BRel W Δb η η :=
  fun k π κ hk => ⟨(h k π κ hk).1, (h k π κ hk).1, PolRel.refl π (h k π κ hk).1⟩

theorem BRel.right {W : World} {Δb : BCtx} {η η' : Env} (h : BRel W Δb η η') :
    BRel W Δb η' η' :=
  fun k π κ hk => ⟨(h k π κ hk).2.1, (h k π κ hk).2.1, PolRel.refl π (h k π κ hk).2.1⟩

theorem TRel.inv_pos {W : World} {Δ : KCtx} {θ θ' : TEnv} (h : TRel W Δ θ θ') :
    TRel W (Δ.inv .pos) θ θ' := by
  intro X π κ hX
  rw [KCtx.lookup_inv] at hX
  obtain ⟨⟨π', κ'⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := h X π' κ' hX'
  exact ⟨h1, h2, (polRel_inv (π := .pos) h1 h2 h3).1 rfl⟩

theorem TRel.inv_neg {W : World} {Δ : KCtx} {θ θ' : TEnv} (h : TRel W Δ θ θ') :
    TRel W (Δ.inv .neg) θ' θ := by
  intro X π κ hX
  rw [KCtx.lookup_inv] at hX
  obtain ⟨⟨π', κ'⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := h X π' κ' hX'
  exact ⟨h2, h1, (polRel_inv (π := .neg) h1 h2 h3).2.1 rfl⟩

theorem TRel.inv_mix {W : World} {Δ : KCtx} {θ θ' : TEnv} (h : TRel W Δ θ θ') :
    TRel W (Δ.inv .mix) θ θ' ∧ TRel W (Δ.inv .mix) θ' θ := by
  constructor <;>
  · intro X π κ hX
    rw [KCtx.lookup_inv] at hX
    obtain ⟨⟨π', κ'⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨h1, h2, h3⟩ := h X π' κ' hX'
    have := (polRel_inv (π := .mix) h1 h2 h3).2.2.1 rfl
    first
    | exact ⟨h1, h2, this.1⟩
    | exact ⟨h2, h1, this.2⟩

theorem TRel.inv_refl {W : World} {Δ : KCtx} {θ : TEnv} (h : TRel W Δ θ θ) (π : Pol) :
    TRel W (Δ.inv π) θ θ := by
  intro X π' κ hX
  rw [KCtx.lookup_inv] at hX
  obtain ⟨⟨π'', κ'⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, _, _⟩ := h X π'' κ' hX'
  exact ⟨h1, h1, PolRel.refl _ h1⟩

theorem BRel.inv_pos {W : World} {Δb : BCtx} {η η' : Env} (h : BRel W Δb η η') :
    BRel W (Δb.inv .pos) η η' := by
  intro k π κ hk
  rw [BCtx.getElem?_inv] at hk
  obtain ⟨⟨π', κ'⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := h k π' κ' hk'
  exact ⟨h1, h2, (polRel_inv (π := .pos) h1 h2 h3).1 rfl⟩

theorem BRel.inv_neg {W : World} {Δb : BCtx} {η η' : Env} (h : BRel W Δb η η') :
    BRel W (Δb.inv .neg) η' η := by
  intro k π κ hk
  rw [BCtx.getElem?_inv] at hk
  obtain ⟨⟨π', κ'⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := h k π' κ' hk'
  exact ⟨h2, h1, (polRel_inv (π := .neg) h1 h2 h3).2.1 rfl⟩

theorem BRel.inv_mix {W : World} {Δb : BCtx} {η η' : Env} (h : BRel W Δb η η') :
    BRel W (Δb.inv .mix) η η' ∧ BRel W (Δb.inv .mix) η' η := by
  constructor <;>
  · intro k π κ hk
    rw [BCtx.getElem?_inv] at hk
    obtain ⟨⟨π', κ'⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨h1, h2, h3⟩ := h k π' κ' hk'
    have := (polRel_inv (π := .mix) h1 h2 h3).2.2.1 rfl
    first
    | exact ⟨h1, h2, this.1⟩
    | exact ⟨h2, h1, this.2⟩

theorem BRel.inv_refl {W : World} {Δb : BCtx} {η : Env} (h : BRel W Δb η η) (π : Pol) :
    BRel W (Δb.inv π) η η := by
  intro k π' κ hk
  rw [BCtx.getElem?_inv] at hk
  obtain ⟨⟨π'', κ'⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, _, _⟩ := h k π'' κ' hk'
  exact ⟨h1, h1, PolRel.refl _ h1⟩

theorem BRel.cons {W : World} {Δb : BCtx} {η η' : Env} (h : BRel W Δb η η') {π : Pol}
    {κ : Kind} {X Y : Sem κ.erase} (hX : Good W κ X) (hY : Good W κ Y) (hXY : PolRel W π κ X Y) :
    BRel W ((π, κ) :: Δb) (Env.cons (PSem.ofSem κ.erase X) η)
      (Env.cons (PSem.ofSem κ.erase Y) η') := by
  intro k π' κ' hk
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    simpa using ⟨hX, hY, hXY⟩
  | succ k => exact h k π' κ' (by simpa using hk)

/-! ## Soundness of kinding -/

/-- A usable polarity relates its arguments by the order. -/
theorem PolRel.le_of_usable {W : World} {π : Pol} (hπ : π.Usable) {κ : Kind} {ι : SKind}
    {X Y : Sem ι} (h : PolRel W π κ X Y) : SemLe W κ X Y := by
  cases π <;> simp_all [Pol.Usable, Pol.le, PolRel, polRelOf]

/-- The semantic statement of kinding: goodness of both interpretations and their order. -/
def KSound (W : World) (κ : Kind) {ι : SKind} (X Y : Sem ι) : Prop :=
  Good W κ X ∧ Good W κ Y ∧ SemLe W κ X Y

theorem kinding_sound {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx}
    {m : Nat} {A : Ty} {κ : Kind} (h : Kinding Ψ Δ Δb m A κ) :
    ∀ (ρ : SizeVal) (θ θ' : TEnv) (ζ : SzEnv) (η η' : Env), TRel W Δ θ θ' → BRel W Δb η η' →
      KSound W κ (interp W ρ θ A κ.erase ζ η) (interp W ρ θ' A κ.erase ζ η') := by
  induction h with
  | unit =>
    intro ρ θ θ' ζ η η' _ _
    exact ⟨introSet_cand hW _, introSet_cand hW _, subset_refl _⟩
  | prod _ _ ihA ihB =>
    intro ρ θ θ' ζ η η' hθ hη
    have hA := ihA ρ θ θ' ζ η η' hθ hη
    have hB := ihB ρ θ θ' ζ η η' hθ hη
    exact ⟨introSet_cand hW _, introSet_cand hW _, prodSet_mono hA.2.2 hB.2.2⟩
  | arr _ _ ihA ihB =>
    intro ρ θ θ' ζ η η' hθ hη
    have hA := ihA ρ θ' θ ζ η' η hθ.inv_neg hη.inv_neg
    have hB := ihB ρ θ θ' ζ η η' hθ hη
    exact ⟨arrSet_cand hW hA.2.1 hB.1, arrSet_cand hW hA.1 hB.2.1, arrSet_mono hA.2.2 hB.2.2⟩
  | var hk hπ =>
    intro ρ θ θ' ζ η η' _ hη
    obtain ⟨h1, h2, h3⟩ := hη _ _ _ hk
    exact ⟨h1, h2, PolRel.le_of_usable hπ h3⟩
  | fvar hX hπ =>
    intro ρ θ θ' ζ η η' hθ _
    obtain ⟨h1, h2, h3⟩ := hθ _ _ _ hX
    exact ⟨h1, h2, PolRel.le_of_usable hπ h3⟩
  | @lam Δ Δb m ι F π κ₁ κ₂ hι _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    subst hι
    refine ⟨⟨fun X hX => ?_, fun X Y hX hY hXY => ?_⟩, ⟨fun X hX => ?_, fun X Y hX hY hXY => ?_⟩,
      fun X Y hX hY hXY => ?_⟩
    · exact (ih ρ θ θ ζ _ _ hθ.left (hη.left.cons hX hX (PolRel.refl π hX))).1
    · exact (ih ρ θ θ ζ _ _ hθ.left (hη.left.cons hX hY hXY)).2.2
    · exact (ih ρ θ' θ' ζ _ _ hθ.right (hη.right.cons hX hX (PolRel.refl π hX))).1
    · exact (ih ρ θ' θ' ζ _ _ hθ.right (hη.right.cons hX hY hXY)).2.2
    · exact (ih ρ θ θ' ζ _ _ hθ (hη.cons hX hY hXY)).2.2
  | @app Δ Δb m F G ι π κ₁ κ₂ _ _ hι ihF ihG =>
    intro ρ θ θ' ζ η η' hθ hη
    subst hι
    have hF := ihF ρ θ θ' ζ η η' hθ hη
    have hGl := ihG ρ θ θ ζ η η (hθ.left.inv_refl π) (hη.left.inv_refl π)
    have hGr := ihG ρ θ' θ' ζ η' η' (hθ.right.inv_refl π) (hη.right.inv_refl π)
    have hrel : PolRel W π κ₁ (interp W ρ θ G κ₁.erase ζ η) (interp W ρ θ' G κ₁.erase ζ η') := by
      cases π with
      | pos => exact (ihG ρ θ θ' ζ η η' hθ.inv_pos hη.inv_pos).2.2
      | neg => exact (ihG ρ θ' θ ζ η' η hθ.inv_neg hη.inv_neg).2.2
      | mix =>
        exact ⟨(ihG ρ θ θ' ζ η η' hθ.inv_mix.1 hη.inv_mix.1).2.2,
          (ihG ρ θ' θ ζ η' η hθ.inv_mix.2 hη.inv_mix.2).2.2⟩
      | top => trivial
    exact ⟨hF.1.1 _ hGl.1, hF.2.1.1 _ hGr.1, hF.2.2 _ _ hGl.1 hGr.1 hrel⟩
  | @mu Δ Δb m a S π hπ _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star, interp_mu_star]
    refine ⟨muSet_cand hW _ _, muSet_cand hW _ _, ?_⟩
    rcases hπ with rfl | rfl
    · apply muSet_mono_cand hW
      intro c 𝒳 𝒴 h𝒳 h𝒴 hsub
      by_cases hc : c < S.length
      · rw [interpAt_eq W ρ θ S c _ _ hc, interpAt_eq W ρ θ' S c _ _ hc]
        exact (ih _ (List.getElem_mem hc) ρ θ θ' ζ _ _ hθ.inv_pos
          (hη.inv_pos.cons (κ := .star) h𝒳 h𝒴 hsub)).2.2
      · rw [interpAt_out W ρ θ S c _ _ (by omega)]
        exact Set.empty_subset _
    · apply subset_of_eq
      apply muSet_congr_cand hW
      intro c 𝒳 h𝒳
      by_cases hc : c < S.length
      · rw [interpAt_eq W ρ θ S c _ _ hc, interpAt_eq W ρ θ' S c _ _ hc]
        have hrel : PolRel W .mix .star (ι := .star) 𝒳 𝒳 := PolRel.refl _ (W := W) h𝒳
        exact Set.Subset.antisymm
          (ih _ (List.getElem_mem hc) ρ θ θ' ζ _ _ hθ.inv_mix.1
            (hη.inv_mix.1.cons (κ := .star) h𝒳 h𝒳 hrel)).2.2
          (ih _ (List.getElem_mem hc) ρ θ' θ ζ _ _ hθ.inv_mix.2
            (hη.inv_mix.2.cons (κ := .star) h𝒳 h𝒳 hrel)).2.2
      · rw [interpAt_out W ρ θ S c _ _ (by omega), interpAt_out W ρ θ' S c _ _ (by omega)]
  | @nu Δ Δb m a R π hπ _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    have hG : ∀ (θ₀ : TEnv) (η₀ : Env), TRel W Δ θ₀ θ₀ → BRel W Δb η₀ η₀ →
        ∀ d < R.length, ∀ 𝒳, Cand W 𝒳 →
          Cand W (interpAt W ρ θ₀ R d ζ (Env.cons (PSem.ofSem .star 𝒳) η₀)) := by
      intro θ₀ η₀ hθ₀ hη₀ d hd 𝒳 h𝒳
      rw [interpAt_eq W ρ θ₀ R d _ _ hd]
      exact (ih _ (List.getElem_mem hd) ρ θ₀ θ₀ ζ _ _ (hθ₀.inv_refl π)
        ((hη₀.inv_refl π).cons (κ := .star) h𝒳 h𝒳 (PolRel.refl π (W := W) h𝒳))).1
    simp only [Kind.erase_star, interp_nu_star]
    refine ⟨nuSet_cand hW _ (hG θ η hθ.left hη.left) _,
      nuSet_cand hW _ (hG θ' η' hθ.right hη.right) _, ?_⟩
    rcases hπ with rfl | rfl
    · apply nuSet_mono_cand hW (hG θ η hθ.left hη.left) (hG θ' η' hθ.right hη.right)
      intro d hd 𝒳 𝒴 h𝒳 h𝒴 hsub
      rw [interpAt_eq W ρ θ R d _ _ hd, interpAt_eq W ρ θ' R d _ _ hd]
      exact (ih _ (List.getElem_mem hd) ρ θ θ' ζ _ _ hθ.inv_pos
        (hη.inv_pos.cons (κ := .star) h𝒳 h𝒴 hsub)).2.2
    · apply subset_of_eq
      apply nuSet_congr_cand hW (hG θ η hθ.left hη.left)
      intro d hd 𝒳 h𝒳
      rw [interpAt_eq W ρ θ R d _ _ hd, interpAt_eq W ρ θ' R d _ _ hd]
      have hrel : PolRel W .mix .star (ι := .star) 𝒳 𝒳 := PolRel.refl _ (W := W) h𝒳
      exact Set.Subset.antisymm
        (ih _ (List.getElem_mem hd) ρ θ θ' ζ _ _ hθ.inv_mix.1
          (hη.inv_mix.1.cons (κ := .star) h𝒳 h𝒳 hrel)).2.2
        (ih _ (List.getElem_mem hd) ρ θ' θ ζ _ _ hθ.inv_mix.2
          (hη.inv_mix.2.cons (κ := .star) h𝒳 h𝒳 hrel)).2.2
  | @allT Δ Δb m κ B _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    refine ⟨allTSet_cand hW fun X hX => ?_, allTSet_cand hW fun X hX => ?_,
      allTSet_mono fun X hX => ?_⟩
    · exact (ih ρ θ θ ζ _ _ hθ.left (hη.left.cons hX hX (PolRel.refl _ hX))).1
    · exact (ih ρ θ' θ' ζ _ _ hθ.right (hη.right.cons hX hX (PolRel.refl _ hX))).1
    · exact (ih ρ θ θ' ζ _ _ hθ (hη.cons hX hX (PolRel.refl _ hX))).2.2
  | @exT Δ Δb m κ B _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    refine ⟨introSet_cand hW _, introSet_cand hW _, exTSet_mono fun X hX => ?_⟩
    exact (ih ρ θ θ' ζ _ _ hθ (hη.cons hX hX (PolRel.refl _ hX))).2.2
  | allS _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    refine ⟨allSSet_cand hW fun β _ => ?_, allSSet_cand hW fun β _ => ?_,
      allSSet_mono fun β => ?_⟩
    · exact (ih ρ θ θ _ η η hθ.left hη.left).1
    · exact (ih ρ θ' θ' _ η' η' hθ.right hη.right).1
    · exact (ih ρ θ θ' _ η η' hθ hη).2.2
  | exS _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    exact ⟨introSet_cand hW _, introSet_cand hW _,
      exSSet_mono fun β => (ih ρ θ θ' _ η η' hθ hη).2.2⟩
  | sub _ hsub ih =>
    intro ρ θ θ' ζ η η' hθ hη
    rw [← hsub.erase_eq]
    have h := ih ρ θ θ' ζ η η' hθ hη
    exact ⟨Good.sub hsub h.1, Good.sub hsub h.2.1, SemLe.sub hsub h.1 h.2.1 h.2.2⟩

/-! ## Agreement on the declared components -/

theorem interp_agree_kinded {W : World} {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m A κ) :
    ∀ (ρ : SizeVal) (θ θ' : TEnv) (ζ : SzEnv) (η η' : Env),
      (∀ X π κ', Δ.lookup X = some (π, κ') → θ X κ'.erase = θ' X κ'.erase) →
      (∀ k π κ', Δb[k]? = some (π, κ') → η k κ'.erase = η' k κ'.erase) →
      interp W ρ θ A κ.erase ζ η = interp W ρ θ' A κ.erase ζ η' := by
  induction h with
  | unit => intros; rfl
  | prod _ _ ihA ihB =>
    intro ρ θ θ' ζ η η' hθ hη
    have h1 := ihA ρ θ θ' ζ η η' hθ hη
    have h2 := ihB ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star] at h1 h2 ⊢
    rw [interp_prod_star, interp_prod_star, h1, h2]
  | @arr Δ Δb m A B _ _ ihA ihB =>
    intro ρ θ θ' ζ η η' hθ hη
    have hθ' : ∀ X π κ', (KCtx.inv .neg Δ).lookup X = some (π, κ') →
        θ X κ'.erase = θ' X κ'.erase := by
      intro X π κ' hX
      rw [KCtx.lookup_inv] at hX
      obtain ⟨⟨π', κ''⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hθ X π' _ hX'
    have hη' : ∀ k π κ', (BCtx.inv .neg Δb)[k]? = some (π, κ') →
        η k κ'.erase = η' k κ'.erase := by
      intro k π κ' hk
      rw [BCtx.getElem?_inv] at hk
      obtain ⟨⟨π', κ''⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hη k π' _ hk'
    have h1 := ihA ρ θ θ' ζ η η' hθ' hη'
    have h2 := ihB ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star] at h1 h2 ⊢
    rw [interp_arr_star, interp_arr_star, h1, h2]
  | var hk _ =>
    intro ρ θ θ' ζ η η' _ hη
    exact hη _ _ _ hk
  | fvar hX _ =>
    intro ρ θ θ' ζ η η' hθ _
    exact hθ _ _ _ hX
  | @lam Δ Δb m ι F π κ₁ κ₂ hι _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    subst hι
    simp only [Kind.erase_arr, interp_lam_arr]
    funext X
    apply ih ρ θ θ' ζ _ _ hθ
    intro k π' κ' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rfl
    | succ k => exact hη k π' κ' (by simpa using hk)
  | @app Δ Δb m F G ι π κ₁ κ₂ _ _ hι ihF ihG =>
    intro ρ θ θ' ζ η η' hθ hη
    subst hι
    have hθ' : ∀ X π' κ', (KCtx.inv π Δ).lookup X = some (π', κ') →
        θ X κ'.erase = θ' X κ'.erase := by
      intro X π' κ' hX
      rw [KCtx.lookup_inv] at hX
      obtain ⟨⟨π'', κ''⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hθ X π'' _ hX'
    have hη' : ∀ k π' κ', (BCtx.inv π Δb)[k]? = some (π', κ') →
        η k κ'.erase = η' k κ'.erase := by
      intro k π' κ' hk
      rw [BCtx.getElem?_inv] at hk
      obtain ⟨⟨π'', κ''⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hη k π'' _ hk'
    have h1 := ihF ρ θ θ' ζ η η' hθ hη
    have h2 := ihG ρ θ θ' ζ η η' hθ' hη'
    simp only [Kind.erase_arr] at h1
    rw [interp_app, interp_app, h1, h2]
  | @mu Δ Δb m a S π _ _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    have hθ' : ∀ X π' κ', (KCtx.inv π Δ).lookup X = some (π', κ') →
        θ X κ'.erase = θ' X κ'.erase := by
      intro X π' κ' hX
      rw [KCtx.lookup_inv] at hX
      obtain ⟨⟨π'', κ''⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hθ X π'' _ hX'
    simp only [Kind.erase_star, interp_mu_star]
    congr 1
    funext c 𝒳
    apply interpAt_congr
    intro c hc
    apply ih _ (List.getElem_mem hc) ρ θ θ' ζ _ _ hθ'
    intro k π' κ' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rfl
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      rw [BCtx.getElem?_inv] at hk
      obtain ⟨⟨π'', κ''⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hη k π'' _ hk'
  | @nu Δ Δb m a R π _ _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    have hθ' : ∀ X π' κ', (KCtx.inv π Δ).lookup X = some (π', κ') →
        θ X κ'.erase = θ' X κ'.erase := by
      intro X π' κ' hX
      rw [KCtx.lookup_inv] at hX
      obtain ⟨⟨π'', κ''⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hθ X π'' _ hX'
    simp only [Kind.erase_star, interp_nu_star]
    congr 1
    funext d 𝒳
    apply interpAt_congr
    intro c hc
    apply ih _ (List.getElem_mem hc) ρ θ θ' ζ _ _ hθ'
    intro k π' κ' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rfl
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      rw [BCtx.getElem?_inv] at hk
      obtain ⟨⟨π'', κ''⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hη k π'' _ hk'
  | @allT Δ Δb m κ B _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star, interp_allT_star]
    congr 1
    funext X
    apply ih ρ θ θ' ζ _ _ hθ
    intro k π' κ' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rfl
    | succ k => exact hη k π' κ' (by simpa using hk)
  | @exT Δ Δb m κ B _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star, interp_exT_star]
    congr 1
    funext X
    apply ih ρ θ θ' ζ _ _ hθ
    intro k π' κ' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rfl
    | succ k => exact hη k π' κ' (by simpa using hk)
  | allS _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star, interp_allS_star]
    congr 1
    funext β
    exact ih ρ θ θ' _ η η' hθ hη
  | exS _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star, interp_exS_star]
    congr 1
    funext β
    exact ih ρ θ θ' _ η η' hθ hη
  | sub _ hsub ih =>
    intro ρ θ θ' ζ η η' hθ hη
    rw [← hsub.erase_eq]
    exact ih ρ θ θ' ζ η η' hθ hη

end NishtAbel2024V5
