import Solutions.V5.Size

/-! # V5: scoping and substitution lemmas for the interpretation -/

namespace NishtAbel2024V5

/-! ## Scoping -/

/-- `Ψ; Θ; k; m ⊢ A` (scoping only): free sizes in `Ψ`, free type variables in `Θ`, bound type
variables below `k`, bound size variables below `m`. -/
inductive TyWf (Ψ : SizeCtx) (Θ : List Nat) : Nat → Nat → Ty → Prop where
  | unit (k m : Nat) : TyWf Ψ Θ k m .unit
  | prod {k m : Nat} {A B : Ty} : TyWf Ψ Θ k m A → TyWf Ψ Θ k m B → TyWf Ψ Θ k m (.prod A B)
  | arr {k m : Nat} {A B : Ty} : TyWf Ψ Θ k m A → TyWf Ψ Θ k m B → TyWf Ψ Θ k m (.arr A B)
  | var {k m X : Nat} : X < k → TyWf Ψ Θ k m (.var X)
  | fvar {k m X : Nat} : X ∈ Θ → TyWf Ψ Θ k m (.fvar X)
  | lam {k m : Nat} {ι : SKind} {F : Ty} : TyWf Ψ Θ (k + 1) m F → TyWf Ψ Θ k m (.lam ι F)
  | app {k m : Nat} {F G : Ty} {ι : SKind} :
      TyWf Ψ Θ k m F → TyWf Ψ Θ k m G → TyWf Ψ Θ k m (.app F G ι)
  | mu {k m : Nat} {a : Size} {S : List Ty} :
      SizeWfAt Ψ m a → (∀ T ∈ S, TyWf Ψ Θ (k + 1) m T) → TyWf Ψ Θ k m (.mu a S)
  | nu {k m : Nat} {a : Size} {R : List Ty} :
      SizeWfAt Ψ m a → (∀ T ∈ R, TyWf Ψ Θ (k + 1) m T) → TyWf Ψ Θ k m (.nu a R)
  | allT {k m : Nat} {κ : Kind} {B : Ty} : TyWf Ψ Θ (k + 1) m B → TyWf Ψ Θ k m (.allT κ B)
  | exT {k m : Nat} {κ : Kind} {B : Ty} : TyWf Ψ Θ (k + 1) m B → TyWf Ψ Θ k m (.exT κ B)
  | allS {k m : Nat} {a : Size} {B : Ty} :
      SizeWfAt Ψ m a → TyWf Ψ Θ k (m + 1) B → TyWf Ψ Θ k m (.allS a B)
  | exS {k m : Nat} {a : Size} {B : Ty} :
      SizeWfAt Ψ m a → TyWf Ψ Θ k (m + 1) B → TyWf Ψ Θ k m (.exS a B)

/-! ## Environments -/

/-- Insert `X` at position `k`, shifting the variables above. -/
def Env.insert (k : Nat) (X : PSem) (η : Env) : Env := fun n =>
  if n < k then η n else if n = k then X else η (n - 1)

theorem Env.insert_succ_cons (k : Nat) (X Y : PSem) (η : Env) :
    Env.insert (k + 1) X (Env.cons Y η) = Env.cons Y (Env.insert k X η) := by
  funext n
  cases n with
  | zero => simp [Env.insert, Env.cons]
  | succ n =>
    simp only [Env.insert, Env.cons]
    by_cases h1 : n < k
    · simp [h1]
    · by_cases h2 : n = k
      · subst h2; simp
      · have h3 : ¬ n + 1 < k + 1 := by omega
        have h4 : n + 1 ≠ k + 1 := by omega
        simp only [h1, h2, h3, h4, if_false]
        cases n with
        | zero => omega
        | succ n => rfl

theorem Env.insert_zero (X : PSem) (η : Env) : Env.insert 0 X η = Env.cons X η := by
  funext n
  cases n with
  | zero => simp [Env.insert, Env.cons]
  | succ n => simp [Env.insert, Env.cons]

theorem Env.cons_agree {η η' : Env} {k : Nat} (h : ∀ n < k, η n = η' n) (X : PSem) :
    ∀ n < k + 1, Env.cons X η n = Env.cons X η' n
  | 0, _ => rfl
  | n + 1, hn => h n (by omega)

/-! ## Agreement -/

theorem interpAt_congr {W : World} {ρ ρ' : SizeVal} {θ θ' : TEnv} {S : List Ty} {ζ ζ' : SzEnv}
    {η η' : Env} (h : ∀ c (hc : c < S.length),
      interp W ρ θ (S[c]'hc) .star ζ η = interp W ρ' θ' (S[c]'hc) .star ζ' η') (c : Nat) :
    interpAt W ρ θ S c ζ η = interpAt W ρ' θ' S c ζ' η' := by
  by_cases hc : c < S.length
  · rw [interpAt_eq W ρ θ S c _ _ hc, interpAt_eq W ρ' θ' S c _ _ hc]
    exact h c hc
  · rw [interpAt_out W ρ θ S c _ _ (by omega), interpAt_out W ρ' θ' S c _ _ (by omega)]

theorem interp_agree {W : World} {Ψ : SizeCtx} {Θ : List Nat} {k m : Nat} {A : Ty}
    (hA : TyWf Ψ Θ k m A) :
    ∀ (ρ ρ' : SizeVal) (θ θ' : TEnv) (ζ ζ' : SzEnv) (η η' : Env),
      (∀ i ∈ Ψ.dom, ρ i = ρ' i) → (∀ X ∈ Θ, θ X = θ' X) → (∀ x < m, ζ x = ζ' x) →
      (∀ X < k, η X = η' X) → ∀ ι, interp W ρ θ A ι ζ η = interp W ρ' θ' A ι ζ' η' := by
  induction hA with
  | unit k => intro _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  | prod _ _ ihA ihB =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [ihA ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη, ihB ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη]
  | arr _ _ ihA ihB =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [ihA ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη, ihB ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη]
  | var hX => intro _ _ _ _ _ _ η η' _ _ _ hη ι; simp only [interp]; rw [hη _ hX]
  | fvar hX => intro _ _ θ θ' _ _ _ _ _ hθ _ _ ι; simp only [interp]; rw [hθ _ hX]
  | lam _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    congr 1
    funext ι₁ ι₂ X
    exact ih _ _ _ _ _ _ _ _ hρ hθ hζ (Env.cons_agree hη _) ι₂
  | app _ _ ihF ihG =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [ihF ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη, ihG ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη]
  | @mu k m a S ha _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [sizeVal_agree hρ hζ ha]
    congr 2
    funext c 𝒳
    exact interpAt_congr (fun c hc => ih _ (List.getElem_mem hc) _ _ _ _ _ _ _ _ hρ hθ hζ
      (Env.cons_agree hη _) _) c
  | @nu k m a R ha _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [sizeVal_agree hρ hζ ha]
    congr 2
    funext d 𝒳
    exact interpAt_congr (fun c hc => ih _ (List.getElem_mem hc) _ _ _ _ _ _ _ _ hρ hθ hζ
      (Env.cons_agree hη _) _) d
  | allT _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    congr 2
    funext X
    exact ih _ _ _ _ _ _ _ _ hρ hθ hζ (Env.cons_agree hη _) _
  | exT _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    congr 2
    funext X
    exact ih _ _ _ _ _ _ _ _ hρ hθ hζ (Env.cons_agree hη _) _
  | allS ha _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [sizeVal_agree hρ hζ ha]
    congr 2
    funext β
    exact ih _ _ _ _ _ _ _ _ hρ hθ (SzEnv.cons_agree hζ β) hη _
  | exS ha _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [sizeVal_agree hρ hζ ha]
    congr 2
    funext β
    exact ih _ _ _ _ _ _ _ _ hρ hθ (SzEnv.cons_agree hζ β) hη _

/-- Types whose interpretation ignores both bound environments. -/
def EnvFree (W : World) (ρ : SizeVal) (θ : TEnv) (T : Ty) : Prop :=
  ∀ (ι : SKind) (ζ ζ' : SzEnv) (η η' : Env), interp W ρ θ T ι ζ η = interp W ρ θ T ι ζ' η'

/-- Locally closed types depend on neither bound environment. -/
theorem envFree_of_closed {W : World} {Ψ : SizeCtx} {Θ : List Nat} {T : Ty}
    (hT : TyWf Ψ Θ 0 0 T) (ρ : SizeVal) (θ : TEnv) : EnvFree W ρ θ T :=
  fun ι ζ ζ' η η' => interp_agree hT ρ ρ θ θ ζ ζ' η η' (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _)) ι

/-- The kind-polymorphic value denoted by a type. -/
noncomputable def tyVal (W : World) (ρ : SizeVal) (θ : TEnv) (T : Ty) (ζ : SzEnv) (η : Env) :
    PSem :=
  fun ι => interp W ρ θ T ι ζ η

/-! ## Lengths -/

theorem Ty.substSizeList_length (σ : List (Nat × Size)) :
    ∀ S : List Ty, (Ty.substSizeList σ S).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.substSizeList, Ty.substSizeList_length σ S]

theorem Ty.substTyList_length (k : Nat) (T : Ty) :
    ∀ S : List Ty, (Ty.substTyList S k T).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.substTyList, Ty.substTyList_length k T S]

theorem Ty.openSzList_length (k : Nat) (b : Size) :
    ∀ S : List Ty, (Ty.openSzList S k b).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.openSzList, Ty.openSzList_length k b S]

theorem Ty.substFTyList_length (τ : List (Nat × Ty)) :
    ∀ S : List Ty, (Ty.substFTyList τ S).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.substFTyList, Ty.substFTyList_length τ S]

/-! ## Substitution of free size variables -/

mutual

theorem interp_substSize (W : World) (ρ : SizeVal) (θ : TEnv) {σ : List (Nat × Size)}
    (hσ : LCSubst σ) :
    ∀ (A : Ty) (ι : SKind) (ζ : SzEnv) (η : Env),
      interp W ρ θ (A.substSize σ) ι ζ η = interp W (substVal ρ σ) θ A ι ζ η
  | .unit, _, _, _ => rfl
  | .prod A B, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [interp_substSize W ρ θ hσ A, interp_substSize W ρ θ hσ B]
  | .arr A B, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [interp_substSize W ρ θ hσ A, interp_substSize W ρ θ hσ B]
  | .var _, _, _, _ => rfl
  | .fvar _, _, _, _ => rfl
  | .lam ι' F, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    congr 1
    funext ι₁ ι₂ X
    exact interp_substSize W ρ θ hσ F ι₂ ζ _
  | .app F G ι', ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [interp_substSize W ρ θ hσ F, interp_substSize W ρ θ hσ G]
  | .mu a S, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ]
    congr 2
    funext c 𝒳
    exact interpAt_substSize W ρ θ hσ S c ζ _
  | .nu a R, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ, Ty.substSizeList_length]
    congr 2
    funext d 𝒳
    exact interpAt_substSize W ρ θ hσ R d ζ _
  | .allT κ B, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    congr 2
    funext X
    exact interp_substSize W ρ θ hσ B _ ζ _
  | .exT κ B, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    congr 2
    funext X
    exact interp_substSize W ρ θ hσ B _ ζ _
  | .allS a B, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ]
    congr 2
    funext β
    exact interp_substSize W ρ θ hσ B _ _ η
  | .exS a B, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ]
    congr 2
    funext β
    exact interp_substSize W ρ θ hσ B _ _ η

theorem interpAt_substSize (W : World) (ρ : SizeVal) (θ : TEnv) {σ : List (Nat × Size)}
    (hσ : LCSubst σ) :
    ∀ (S : List Ty) (c : Nat) (ζ : SzEnv) (η : Env),
      interpAt W ρ θ (Ty.substSizeList σ S) c ζ η = interpAt W (substVal ρ σ) θ S c ζ η
  | [], c, _, _ => by cases c <;> rfl
  | A :: _, 0, ζ, η => interp_substSize W ρ θ hσ A .star ζ η
  | _ :: S, c + 1, ζ, η => interpAt_substSize W ρ θ hσ S c ζ η

end

/-! ## Substitution of bound type variables -/

mutual

theorem interp_substTy (W : World) (ρ : SizeVal) (θ : TEnv) {T : Ty} (hT : EnvFree W ρ θ T) :
    ∀ (A : Ty) (k : Nat) (ι : SKind) (ζ : SzEnv) (η : Env),
      interp W ρ θ (A.substTy k T) ι ζ η =
        interp W ρ θ A ι ζ (Env.insert k (tyVal W ρ θ T ζ η) η)
  | .unit, _, _, _, _ => rfl
  | .prod A B, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    rw [interp_substTy W ρ θ hT A k, interp_substTy W ρ θ hT B k]
  | .arr A B, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    rw [interp_substTy W ρ θ hT A k, interp_substTy W ρ θ hT B k]
  | .var X, k, ι, ζ, η => by
    by_cases h1 : X = k
    · subst h1; simp [Ty.substTy, interp, Env.insert, tyVal]
    · by_cases h2 : k < X
      · have h3 : ¬ X < k := by omega
        simp [Ty.substTy, h1, h2, h3, interp, Env.insert]
      · have h3 : X < k := by omega
        simp [Ty.substTy, h1, h2, h3, interp, Env.insert]
  | .fvar _, _, _, _, _ => rfl
  | .lam ι' F, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    congr 1
    funext ι₁ ι₂ X
    rw [interp_substTy W ρ θ hT F (k + 1), Env.insert_succ_cons]
    congr 3
    funext ι₃
    exact hT ι₃ ζ ζ _ η
  | .app F G ι', k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    rw [interp_substTy W ρ θ hT F k, interp_substTy W ρ θ hT G k]
  | .mu a S, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    congr 2
    funext c 𝒳
    rw [interpAt_substTy W ρ θ hT S c (k + 1), Env.insert_succ_cons]
    congr 3
    funext ι₃
    exact hT ι₃ ζ ζ _ η
  | .nu a R, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    rw [Ty.substTyList_length]
    congr 2
    funext d 𝒳
    rw [interpAt_substTy W ρ θ hT R d (k + 1), Env.insert_succ_cons]
    congr 3
    funext ι₃
    exact hT ι₃ ζ ζ _ η
  | .allT κ B, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    congr 2
    funext X
    rw [interp_substTy W ρ θ hT B (k + 1), Env.insert_succ_cons]
    congr 3
    funext ι₃
    exact hT ι₃ ζ ζ _ η
  | .exT κ B, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    congr 2
    funext X
    rw [interp_substTy W ρ θ hT B (k + 1), Env.insert_succ_cons]
    congr 3
    funext ι₃
    exact hT ι₃ ζ ζ _ η
  | .allS a B, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    congr 2
    funext β
    rw [interp_substTy W ρ θ hT B k]
    congr 2
    funext ι₃
    exact hT ι₃ _ ζ η η
  | .exS a B, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    congr 2
    funext β
    rw [interp_substTy W ρ θ hT B k]
    congr 2
    funext ι₃
    exact hT ι₃ _ ζ η η

theorem interpAt_substTy (W : World) (ρ : SizeVal) (θ : TEnv) {T : Ty} (hT : EnvFree W ρ θ T) :
    ∀ (S : List Ty) (c k : Nat) (ζ : SzEnv) (η : Env),
      interpAt W ρ θ (Ty.substTyList S k T) c ζ η =
        interpAt W ρ θ S c ζ (Env.insert k (tyVal W ρ θ T ζ η) η)
  | [], c, _, _, _ => by cases c <;> rfl
  | A :: _, 0, k, ζ, η => interp_substTy W ρ θ hT A k .star ζ η
  | _ :: S, c + 1, k, ζ, η => interpAt_substTy W ρ θ hT S c k ζ η

end

/-! ## Opening bound size variables -/

mutual

theorem interp_openSz (W : World) (ρ : SizeVal) (θ : TEnv) {b : Size} (hb : b.LC) :
    ∀ (A : Ty) (k : Nat) (ι : SKind) (ζ : SzEnv) (η : Env),
      interp W ρ θ (A.openSz k b) ι ζ η =
        interp W ρ θ A ι (SzEnv.insert k (sizeVal ρ ζ b) ζ) η
  | .unit, _, _, _, _ => rfl
  | .prod A B, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [interp_openSz W ρ θ hb A k, interp_openSz W ρ θ hb B k]
  | .arr A B, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [interp_openSz W ρ θ hb A k, interp_openSz W ρ θ hb B k]
  | .var _, _, _, _, _ => rfl
  | .fvar _, _, _, _, _ => rfl
  | .lam ι' F, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    congr 1
    funext ι₁ ι₂ X
    exact interp_openSz W ρ θ hb F k ι₂ ζ _
  | .app F G ι', k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [interp_openSz W ρ θ hb F k, interp_openSz W ρ θ hb G k]
  | .mu a S, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [sizeVal_openAt ρ ζ k hb]
    congr 2
    funext c 𝒳
    exact interpAt_openSz W ρ θ hb S c k ζ _
  | .nu a R, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [sizeVal_openAt ρ ζ k hb, Ty.openSzList_length]
    congr 2
    funext d 𝒳
    exact interpAt_openSz W ρ θ hb R d k ζ _
  | .allT κ B, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    congr 2
    funext X
    exact interp_openSz W ρ θ hb B k _ ζ _
  | .exT κ B, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    congr 2
    funext X
    exact interp_openSz W ρ θ hb B k _ ζ _
  | .allS a B, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [sizeVal_openAt ρ ζ k hb]
    congr 2
    funext β
    rw [interp_openSz W ρ θ hb B (k + 1), SzEnv.insert_succ_cons,
      sizeVal_lc ρ (SzEnv.cons β ζ) ζ hb]
  | .exS a B, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [sizeVal_openAt ρ ζ k hb]
    congr 2
    funext β
    rw [interp_openSz W ρ θ hb B (k + 1), SzEnv.insert_succ_cons,
      sizeVal_lc ρ (SzEnv.cons β ζ) ζ hb]

theorem interpAt_openSz (W : World) (ρ : SizeVal) (θ : TEnv) {b : Size} (hb : b.LC) :
    ∀ (S : List Ty) (c k : Nat) (ζ : SzEnv) (η : Env),
      interpAt W ρ θ (Ty.openSzList S k b) c ζ η =
        interpAt W ρ θ S c (SzEnv.insert k (sizeVal ρ ζ b) ζ) η
  | [], c, _, _, _ => by cases c <;> rfl
  | A :: _, 0, k, ζ, η => interp_openSz W ρ θ hb A k .star ζ η
  | _ :: S, c + 1, k, ζ, η => interpAt_openSz W ρ θ hb S c k ζ η

end

/-! ## Substitution of free type variables -/

/-- The type environment induced by a substitution of types for free type variables. -/
noncomputable def substTVal (W : World) (ρ : SizeVal) (θ : TEnv) (τ : List (Nat × Ty)) : TEnv :=
  fun X =>
    match τ.lookup X with
    | some T => tyVal W ρ θ T SzEnv.zero Env.empty
    | none => θ X

mutual

theorem interp_substFTy (W : World) (ρ : SizeVal) (θ : TEnv) {τ : List (Nat × Ty)}
    (hτ : ∀ X T, τ.lookup X = some T → EnvFree W ρ θ T) :
    ∀ (A : Ty) (ι : SKind) (ζ : SzEnv) (η : Env),
      interp W ρ θ (A.substFTy τ) ι ζ η = interp W ρ (substTVal W ρ θ τ) A ι ζ η
  | .unit, _, _, _ => rfl
  | .prod A B, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    rw [interp_substFTy W ρ θ hτ A, interp_substFTy W ρ θ hτ B]
  | .arr A B, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    rw [interp_substFTy W ρ θ hτ A, interp_substFTy W ρ θ hτ B]
  | .var _, _, _, _ => rfl
  | .fvar X, ι, ζ, η => by
    show interp W ρ θ ((τ.lookup X).getD (.fvar X)) ι ζ η = substTVal W ρ θ τ X ι
    unfold substTVal
    cases h : τ.lookup X with
    | none => rfl
    | some T => exact hτ X T h ι ζ SzEnv.zero η Env.empty
  | .lam ι' F, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    congr 1
    funext ι₁ ι₂ X
    exact interp_substFTy W ρ θ hτ F ι₂ ζ _
  | .app F G ι', ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    rw [interp_substFTy W ρ θ hτ F, interp_substFTy W ρ θ hτ G]
  | .mu a S, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    congr 2
    funext c 𝒳
    exact interpAt_substFTy W ρ θ hτ S c ζ _
  | .nu a R, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    rw [Ty.substFTyList_length]
    congr 2
    funext d 𝒳
    exact interpAt_substFTy W ρ θ hτ R d ζ _
  | .allT κ B, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    congr 2
    funext X
    exact interp_substFTy W ρ θ hτ B _ ζ _
  | .exT κ B, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    congr 2
    funext X
    exact interp_substFTy W ρ θ hτ B _ ζ _
  | .allS a B, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    congr 2
    funext β
    exact interp_substFTy W ρ θ hτ B _ _ η
  | .exS a B, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    congr 2
    funext β
    exact interp_substFTy W ρ θ hτ B _ _ η

theorem interpAt_substFTy (W : World) (ρ : SizeVal) (θ : TEnv) {τ : List (Nat × Ty)}
    (hτ : ∀ X T, τ.lookup X = some T → EnvFree W ρ θ T) :
    ∀ (S : List Ty) (c : Nat) (ζ : SzEnv) (η : Env),
      interpAt W ρ θ (Ty.substFTyList τ S) c ζ η = interpAt W ρ (substTVal W ρ θ τ) S c ζ η
  | [], c, _, _ => by cases c <;> rfl
  | A :: _, 0, ζ, η => interp_substFTy W ρ θ hτ A .star ζ η
  | _ :: S, c + 1, ζ, η => interpAt_substFTy W ρ θ hτ S c ζ η

end

/-! ## Unfolding and opening -/

/-- A `*`-former denotes the same kind-polymorphic value as its `*`-component. -/
theorem tyVal_mu (W : World) (ρ : SizeVal) (θ : TEnv) (b : Size) (S : List Ty) (ζ : SzEnv)
    (η : Env) :
    tyVal W ρ θ (.mu b S) ζ η = PSem.ofSem .star (interp W ρ θ (.mu b S) .star ζ η) := by
  funext ι
  cases ι with
  | star => rfl
  | arr ι₁ ι₂ => rfl

theorem tyVal_nu (W : World) (ρ : SizeVal) (θ : TEnv) (b : Size) (R : List Ty) (ζ : SzEnv)
    (η : Env) :
    tyVal W ρ θ (.nu b R) ζ η = PSem.ofSem .star (interp W ρ θ (.nu b R) .star ζ η) := by
  funext ι
  cases ι with
  | star => rfl
  | arr ι₁ ι₂ => rfl

/-- Unfolding a branch: `⟦S_c[μ^b S]⟧ = ⟦S_c⟧(stage ⟦b⟧)`. -/
theorem interp_unfold_mu {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {b : Size} {S : List Ty} {c : Nat} (hc : c < S.length) (hwf : TyWf Ψ Θ 0 0 (.mu b S))
    (ζ : SzEnv) (η : Env) :
    interp W ρ θ ((S[c]'hc).substTy 0 (.mu b S)) .star ζ η =
      interpAt W ρ θ S c ζ (Env.cons (PSem.ofSem .star
        (MuSet W (fun c 𝒳 => interpAt W ρ θ S c ζ (Env.cons (PSem.ofSem .star 𝒳) η))
          (sizeVal ρ ζ b))) η) := by
  rw [interp_substTy W ρ θ (envFree_of_closed hwf ρ θ) _ 0 .star ζ η, Env.insert_zero,
    interpAt_eq W ρ θ S c _ _ hc, tyVal_mu]
  rfl

theorem interp_unfold_nu {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {b : Size} {R : List Ty} {d : Nat} (hd : d < R.length) (hwf : TyWf Ψ Θ 0 0 (.nu b R))
    (ζ : SzEnv) (η : Env) :
    interp W ρ θ ((R[d]'hd).substTy 0 (.nu b R)) .star ζ η =
      interpAt W ρ θ R d ζ (Env.cons (PSem.ofSem .star (NuSet W R.length
        (fun d 𝒳 => interpAt W ρ θ R d ζ (Env.cons (PSem.ofSem .star 𝒳) η))
          (sizeVal ρ ζ b))) η) := by
  rw [interp_substTy W ρ θ (envFree_of_closed hwf ρ θ) _ 0 .star ζ η, Env.insert_zero,
    interpAt_eq W ρ θ R d _ _ hd, tyVal_nu]
  rfl

/-- Opening a type binder with a type. -/
theorem interp_openTy {W : World} {ρ : SizeVal} {θ : TEnv} {T : Ty} (hT : EnvFree W ρ θ T)
    (B : Ty) (ι : SKind) (ζ : SzEnv) (η : Env) :
    interp W ρ θ (B.substTy 0 T) ι ζ η = interp W ρ θ B ι ζ (Env.cons (tyVal W ρ θ T ζ η) η) := by
  rw [interp_substTy W ρ θ hT B 0 ι ζ η, Env.insert_zero]

/-- Opening a size binder with a locally closed size. -/
theorem interp_openSz0 (W : World) (ρ : SizeVal) (θ : TEnv) {b : Size} (hb : b.LC) (B : Ty)
    (ι : SKind) (ζ : SzEnv) (η : Env) :
    interp W ρ θ (B.openSz 0 b) ι ζ η =
      interp W ρ θ B ι (SzEnv.cons (sizeVal ρ ζ b) ζ) η := by
  rw [interp_openSz W ρ θ hb B 0 ι ζ η, SzEnv.insert_zero]

end NishtAbel2024V5
