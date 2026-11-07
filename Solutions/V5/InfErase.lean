import Solutions.V5.InfCheck
import Solutions.V5.Match

/-! # V5 inference: size erasure and kinding -/

namespace NishtAbel2024V5

/-- All size expressions of a type are well formed: free size variables in `Ψ`, bound size
variables below the binder depth. -/
inductive SizesWf (Ψ : SizeCtx) : Nat → Ty → Prop where
  | unit (m : Nat) : SizesWf Ψ m .unit
  | prod {m : Nat} {A B : Ty} : SizesWf Ψ m A → SizesWf Ψ m B → SizesWf Ψ m (.prod A B)
  | arr {m : Nat} {A B : Ty} : SizesWf Ψ m A → SizesWf Ψ m B → SizesWf Ψ m (.arr A B)
  | var (m k : Nat) : SizesWf Ψ m (.var k)
  | fvar (m X : Nat) : SizesWf Ψ m (.fvar X)
  | lam {m : Nat} {ι : SKind} {F : Ty} : SizesWf Ψ m F → SizesWf Ψ m (.lam ι F)
  | app {m : Nat} {F G : Ty} {ι : SKind} :
      SizesWf Ψ m F → SizesWf Ψ m G → SizesWf Ψ m (.app F G ι)
  | mu {m : Nat} {a : Size} {S : List Ty} :
      SizeWfAt Ψ m a → (∀ T ∈ S, SizesWf Ψ m T) → SizesWf Ψ m (.mu a S)
  | nu {m : Nat} {a : Size} {R : List Ty} :
      SizeWfAt Ψ m a → (∀ T ∈ R, SizesWf Ψ m T) → SizesWf Ψ m (.nu a R)
  | allT {m : Nat} {κ : Kind} {B : Ty} : SizesWf Ψ m B → SizesWf Ψ m (.allT κ B)
  | exT {m : Nat} {κ : Kind} {B : Ty} : SizesWf Ψ m B → SizesWf Ψ m (.exT κ B)
  | allS {m : Nat} {a : Size} {B : Ty} :
      SizeWfAt Ψ m a → SizesWf Ψ (m + 1) B → SizesWf Ψ m (.allS a B)
  | exS {m : Nat} {a : Size} {B : Ty} :
      SizeWfAt Ψ m a → SizesWf Ψ (m + 1) B → SizesWf Ψ m (.exS a B)

theorem Ty.mem_eraseSzList {S : List Ty} {T : Ty} (h : T ∈ S) : T.eraseSz ∈ Ty.eraseSzList S := by
  induction S with
  | nil => simp at h
  | cons A S ih =>
    simp only [Ty.eraseSzList, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (ih h)

theorem Ty.mem_eraseSzList_inv {S : List Ty} {T₀ : Ty} (h : T₀ ∈ Ty.eraseSzList S) :
    ∃ T ∈ S, T.eraseSz = T₀ := by
  induction S with
  | nil => simp [Ty.eraseSzList] at h
  | cons A S ih =>
    simp only [Ty.eraseSzList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨A, by simp, rfl⟩
    · obtain ⟨T, hT, he⟩ := ih h
      exact ⟨T, by simp [hT], he⟩

/-- Kinding of the size erasure, with well-formed sizes, gives kinding. -/
theorem kinding_of_erase {Δ : KCtx} {Δb : BCtx} {m : Nat} {A₀ : Ty} {κ : Kind}
    (h : Kinding [] Δ Δb m A₀ κ) :
    ∀ {Ψ : SizeCtx} {A : Ty}, A.eraseSz = A₀ → SizesWf Ψ m A → Kinding Ψ Δ Δb m A κ := by
  induction h with
  | unit =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    exact .unit
  | prod _ _ ihA ihB =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨rfl, rfl⟩ := he
    cases hw with
    | prod h₁ h₂ => exact .prod (ihA rfl h₁) (ihB rfl h₂)
  | arr _ _ ihA ihB =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨rfl, rfl⟩ := he
    cases hw with
    | arr h₁ h₂ => exact .arr (ihA rfl h₁) (ihB rfl h₂)
  | var hk hπ =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    subst he
    exact .var hk hπ
  | fvar hX hπ =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    subst he
    exact .fvar hX hπ
  | lam hι _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨rfl, rfl⟩ := he
    cases hw with
    | lam h₁ => exact .lam hι (ih rfl h₁)
  | app _ _ hι ihF ihG =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    cases hw with
    | app h₁ h₂ => exact .app (ihF rfl h₁) (ihG rfl h₂) hι
  | mu hπ _ _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨_, rfl⟩ := he
    cases hw with
    | mu ha hS =>
      refine .mu hπ ha fun T hT => ?_
      exact ih _ (Ty.mem_eraseSzList hT) rfl (hS T hT)
  | nu hπ _ _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨_, rfl⟩ := he
    cases hw with
    | nu ha hR =>
      refine .nu hπ ha fun T hT => ?_
      exact ih _ (Ty.mem_eraseSzList hT) rfl (hR T hT)
  | allT _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨rfl, rfl⟩ := he
    cases hw with
    | allT h₁ => exact .allT (ih rfl h₁)
  | exT _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨rfl, rfl⟩ := he
    cases hw with
    | exT h₁ => exact .exT (ih rfl h₁)
  | allS _ _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨_, rfl⟩ := he
    cases hw with
    | allS ha h₁ => exact .allS ha (ih rfl h₁)
  | exS _ _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨_, rfl⟩ := he
    cases hw with
    | exS ha h₁ => exact .exS ha (ih rfl h₁)
  | sub _ hs ih =>
    intro Ψ A he hw
    exact .sub (ih he hw) hs

/-- Kinding of an annotated type gives kinding of its size erasure. -/
theorem Kinding.erase {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m A κ) : Kinding [] Δ Δb m A.eraseSz κ := by
  induction h with
  | unit => exact .unit
  | prod _ _ ihA ihB => exact .prod ihA ihB
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | var hk hπ => exact .var hk hπ
  | fvar hX hπ => exact .fvar hX hπ
  | lam hι _ ih => exact .lam hι ih
  | app _ _ hι ihF ihG => exact .app ihF ihG hι
  | mu hπ _ _ ih =>
    refine .mu hπ trivial fun T hT => ?_
    obtain ⟨T', hT', rfl⟩ := Ty.mem_eraseSzList_inv hT
    exact ih T' hT'
  | nu hπ _ _ ih =>
    refine .nu hπ trivial fun T hT => ?_
    obtain ⟨T', hT', rfl⟩ := Ty.mem_eraseSzList_inv hT
    exact ih T' hT'
  | allT _ ih => exact .allT ih
  | exT _ ih => exact .exT ih
  | allS _ _ ih => exact .allS trivial ih
  | exS _ _ ih => exact .exS trivial ih
  | sub _ hs ih => exact .sub ih hs

/-- Kinding gives well-formed sizes. -/
theorem Kinding.sizesWf {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m A κ) : SizesWf Ψ m A := by
  induction h with
  | unit => exact .unit _
  | prod _ _ ihA ihB => exact .prod ihA ihB
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | var => exact .var _ _
  | fvar => exact .fvar _ _
  | lam _ _ ih => exact .lam ih
  | app _ _ _ ihF ihG => exact .app ihF ihG
  | mu _ ha _ ih => exact .mu ha ih
  | nu _ ha _ ih => exact .nu ha ih
  | allT _ ih => exact .allT ih
  | exT _ ih => exact .exT ih
  | allS ha _ ih => exact .allS ha ih
  | exS ha _ ih => exact .exS ha ih
  | sub _ _ ih => exact ih

/-- From size-erased kinding. -/
theorem EKinding.kinding {Δ : KCtx} {Δb : BCtx} {A : Ty} {κ : Kind} (h : EKinding Δ Δb A κ)
    {Ψ : SizeCtx} (hw : SizesWf Ψ 0 A) : Kinding Ψ Δ Δb 0 A κ :=
  kinding_of_erase h rfl hw

/-! ## Erasure ignores sizes -/

mutual
theorem Ty.eraseSz_substSize (σ : List (Nat × Size)) :
    ∀ A : Ty, (A.substSize σ).eraseSz = A.eraseSz
  | .unit => rfl
  | .prod A B => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ A, Ty.eraseSz_substSize σ B]
  | .arr A B => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ A, Ty.eraseSz_substSize σ B]
  | .var _ => rfl
  | .fvar _ => rfl
  | .lam ι F => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ F]
  | .app F G ι => by
    simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ F, Ty.eraseSz_substSize σ G]
  | .mu a S => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSzList_substSizeList σ S]
  | .nu a R => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSzList_substSizeList σ R]
  | .allT κ B => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ B]
  | .exT κ B => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ B]
  | .allS a B => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ B]
  | .exS a B => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ B]
theorem Ty.eraseSzList_substSizeList (σ : List (Nat × Size)) :
    ∀ S : List Ty, Ty.eraseSzList (Ty.substSizeList σ S) = Ty.eraseSzList S
  | [] => rfl
  | A :: S => by
    simp [Ty.substSizeList, Ty.eraseSzList, Ty.eraseSz_substSize σ A,
      Ty.eraseSzList_substSizeList σ S]
end

/-! ## Well-formed sizes under substitution -/

theorem SizesWf.substSize {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A) {Ψ' : SizeCtx}
    {σ : List (Nat × Size)} (hσ : ∀ i ∈ Ψ.dom, SizeWf Ψ' ((Size.var i 0).subst σ)) :
    SizesWf Ψ' m (A.substSize σ) := by
  induction h with
  | unit => exact .unit _
  | prod _ _ ihA ihB => exact .prod ihA ihB
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | var => exact .var _ _
  | fvar => exact .fvar _ _
  | lam _ ih => exact .lam ih
  | app _ _ ihF ihG => exact .app ihF ihG
  | mu ha _ ih =>
    simp only [Ty.substSize]
    refine .mu (SizeWfAt.subst hσ ha) fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substSizeList hT'
    exact ih B hB
  | nu ha _ ih =>
    simp only [Ty.substSize]
    refine .nu (SizeWfAt.subst hσ ha) fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substSizeList hT'
    exact ih B hB
  | allT _ ih => exact .allT ih
  | exT _ ih => exact .exT ih
  | allS ha _ ih => exact .allS (SizeWfAt.subst hσ ha) ih
  | exS ha _ ih => exact .exS (SizeWfAt.subst hσ ha) ih

end NishtAbel2024V5
