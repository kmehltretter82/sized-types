import Solutions.V3.Interp

/-! # V3: syntactic lemmas about well-formed types -/

namespace NishtAbel2024V3

theorem SizeWf.weaken {Ψ Ψ' : SizeCtx} (h : ∀ i ∈ Ψ.dom, i ∈ Ψ'.dom) {a : Size} (ha : SizeWf Ψ a) :
    SizeWf Ψ' a := by
  cases a with
  | inf => trivial
  | var i n => exact h i ha

theorem TyWf.weaken {Ψ : SizeCtx} {k : Nat} {A : Ty} (hA : TyWf Ψ k A) :
    ∀ (Ψ' : SizeCtx) (k' : Nat), (∀ i ∈ Ψ.dom, i ∈ Ψ'.dom) → k ≤ k' → TyWf Ψ' k' A := by
  induction hA with
  | unit k => intro _ _ _ _; exact .unit _
  | prod _ _ ihA ihB => intro Ψ' k' h hk; exact .prod (ihA Ψ' k' h hk) (ihB Ψ' k' h hk)
  | arr _ _ ihA ihB => intro Ψ' k' h hk; exact .arr (ihA Ψ' k' h hk) (ihB Ψ' k' h hk)
  | var hX => intro _ _ _ hk; exact .var (by omega)
  | mu ha _ hpos ih =>
    intro Ψ' k' h hk
    exact .mu (ha.weaken h) (fun T hT => ih T hT Ψ' (k' + 1) h (by omega)) hpos
  | nu ha _ hpos ih =>
    intro Ψ' k' h hk
    exact .nu (ha.weaken h) (fun T hT => ih T hT Ψ' (k' + 1) h (by omega)) hpos

theorem dom_append_left {Ψ Ψ' : SizeCtx} : ∀ i ∈ Ψ.dom, i ∈ (Ψ ++ Ψ').dom := by
  intro i hi
  simp only [SizeCtx.dom, List.map_append, List.mem_append]
  exact Or.inl hi

/-- Variables at or above the level do not occur, so any polarity holds. -/
theorem TyWf.polIn {Ψ : SizeCtx} {k : Nat} {A : Ty} (hA : TyWf Ψ k A) :
    ∀ (b : Bool) (j : Nat), k ≤ j → PolIn b j A := by
  induction hA with
  | unit k => intro b j _; exact .unit _ _
  | prod _ _ ihA ihB => intro b j h; exact .prod (ihA b j h) (ihB b j h)
  | arr _ _ ihA ihB => intro b j h; exact .arr (ihA (!b) j h) (ihB b j h)
  | var hX => intro b j h; exact .var_other (by omega)
  | mu _ _ _ ih => intro b j h; exact .mu (fun T hT => ih T hT b (j + 1) (by omega))
  | nu _ _ _ ih => intro b j h; exact .nu (fun T hT => ih T hT b (j + 1) (by omega))

/-- Substituting a closed type below a position keeps polarities above it. -/
theorem PolIn.substTy {b : Bool} {j : Nat} {B : Ty} (hB : PolIn b j B) :
    ∀ (Ψ : SizeCtx) (T : Ty) (k : Nat), TyWf Ψ 0 T → j < k → PolIn b j (B.substTy k T) := by
  induction hB with
  | unit b j => intro _ _ _ _ _; exact .unit _ _
  | prod _ _ ihA ihB =>
    intro Ψ T k hT hjk; exact .prod (ihA Ψ T k hT hjk) (ihB Ψ T k hT hjk)
  | arr _ _ ihA ihB =>
    intro Ψ T k hT hjk; exact .arr (ihA Ψ T k hT hjk) (ihB Ψ T k hT hjk)
  | var_self j =>
    intro _ _ k hT hjk
    have h1 : j ≠ k := by omega
    have h2 : ¬ k < j := by omega
    simp only [Ty.substTy, h1, h2, if_false]
    exact .var_self j
  | @var_other b j X hne =>
    intro _ T k hT hjk
    simp only [Ty.substTy]
    by_cases h1 : X = k
    · simp only [h1, if_true]; exact hT.polIn b j (by omega)
    · by_cases h2 : k < X
      · simp only [h1, h2, if_true, if_false]; exact .var_other (by omega)
      · simp only [h1, h2, if_false]; exact .var_other hne
  | mu _ ih =>
    intro _ _ _ hT hjk
    simp only [Ty.substTy]
    refine .mu fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    exact ih B hB _ _ _ hT (by omega)
  | nu _ ih =>
    intro _ _ _ hT hjk
    simp only [Ty.substTy]
    refine .nu fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    exact ih B hB _ _ _ hT (by omega)
where
  Ty.mem_substTyList {S : List Ty} {k : Nat} {T T' : Ty} (h : T' ∈ Ty.substTyList S k T) :
      ∃ B ∈ S, T' = B.substTy k T := by
    induction S with
    | nil => simp [Ty.substTyList] at h
    | cons A S ih =>
      simp only [Ty.substTyList, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨A, by simp, rfl⟩
      · obtain ⟨B, hB, rfl⟩ := ih h; exact ⟨B, by simp [hB], rfl⟩

theorem Ty.mem_substTyList' {S : List Ty} {k : Nat} {T T' : Ty} (h : T' ∈ Ty.substTyList S k T) :
    ∃ B ∈ S, T' = B.substTy k T := PolIn.substTy.Ty.mem_substTyList h

/-- Substituting a closed type for the variable at the level lowers the level. -/
theorem TyWf.substTy {Ψ : SizeCtx} {n : Nat} {A : Ty} (hA : TyWf Ψ n A) :
    ∀ (k : Nat) (T : Ty), n = k + 1 → TyWf Ψ 0 T → TyWf Ψ k (A.substTy k T) := by
  induction hA with
  | unit _ => intro _ _ _ _; exact .unit _
  | prod _ _ ihA ihB => intro k T hn hT; exact .prod (ihA k T hn hT) (ihB k T hn hT)
  | arr _ _ ihA ihB => intro k T hn hT; exact .arr (ihA k T hn hT) (ihB k T hn hT)
  | @var n X hX =>
    intro k T hn hT
    simp only [Ty.substTy]
    by_cases h1 : X = k
    · simp only [h1, if_true]; exact hT.weaken _ _ (fun i hi => hi) (by omega)
    · have h2 : ¬ k < X := by omega
      simp only [h1, h2, if_false]; exact .var (by omega)
  | mu ha _ hpos ih =>
    intro k T hn hT
    simp only [Ty.substTy]
    refine .mu ha (fun T' hT' => ?_) (fun T' hT' => ?_)
    · obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList' hT'
      exact ih B hB _ _ (by omega) hT
    · obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList' hT'
      exact (hpos B hB).substTy _ _ _ hT (by omega)
  | nu ha _ hpos ih =>
    intro k T hn hT
    simp only [Ty.substTy]
    refine .nu ha (fun T' hT' => ?_) (fun T' hT' => ?_)
    · obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList' hT'
      exact ih B hB _ _ (by omega) hT
    · obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList' hT'
      exact (hpos B hB).substTy _ _ _ hT (by omega)

/-- The unfolded branch of a well-formed closed `μ`/`ν` is well-formed. -/
theorem TyWf.unfold_mu {Ψ : SizeCtx} {a b : Size} {S : List Ty} {c : Nat} {Sc : Ty}
    (hwf : TyWf Ψ 0 (.mu a S)) (hc : S[c]? = some Sc) (hb : SizeWf Ψ b) :
    TyWf Ψ 0 (Sc.substTy 0 (.mu b S)) := by
  cases hwf with
  | mu _ hS hpos =>
    have hmem : Sc ∈ S := List.mem_of_getElem? hc
    exact (hS Sc hmem).substTy 0 _ rfl (.mu hb hS hpos)

theorem TyWf.unfold_nu {Ψ : SizeCtx} {a b : Size} {R : List Ty} {d : Nat} {Rd : Ty}
    (hwf : TyWf Ψ 0 (.nu a R)) (hd : R[d]? = some Rd) (hb : SizeWf Ψ b) :
    TyWf Ψ 0 (Rd.substTy 0 (.nu b R)) := by
  cases hwf with
  | nu _ hR hpos =>
    have hmem : Rd ∈ R := List.mem_of_getElem? hd
    exact (hR Rd hmem).substTy 0 _ rfl (.nu hb hR hpos)

/-! ## Size substitution commutes with type substitution -/

mutual

theorem Ty.substSize_substTy (σ : List (Nat × Size)) (T : Ty) :
    ∀ (A : Ty) (k : Nat), (A.substTy k T).substSize σ = (A.substSize σ).substTy k (T.substSize σ)
  | .unit, _ => rfl
  | .prod A B, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T A k, Ty.substSize_substTy σ T B k]
  | .arr A B, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T A k, Ty.substSize_substTy σ T B k]
  | .var X, k => by
    simp only [Ty.substTy, Ty.substSize]
    by_cases h1 : X = k
    · simp [h1]
    · by_cases h2 : k < X
      · simp [h1, h2, Ty.substSize]
      · simp [h1, h2, Ty.substSize]
  | .mu a S, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSizeList_substTyList σ T S (k + 1)]
  | .nu a R, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSizeList_substTyList σ T R (k + 1)]

theorem Ty.substSizeList_substTyList (σ : List (Nat × Size)) (T : Ty) :
    ∀ (S : List Ty) (k : Nat), Ty.substSizeList σ (Ty.substTyList S k T) =
      Ty.substTyList (Ty.substSizeList σ S) k (T.substSize σ)
  | [], _ => rfl
  | A :: S, k => by
    simp only [Ty.substTyList, Ty.substSizeList]
    rw [Ty.substSize_substTy σ T A k, Ty.substSizeList_substTyList σ T S k]

end

/-! ## Fresh variables do not matter to size substitution -/

theorem Size.subst_cons_fresh {Ψ : SizeCtx} {a : Size} (ha : SizeWf Ψ a) {i : Nat} (hi : i ∉ Ψ.dom)
    (b : Size) (σ : List (Nat × Size)) : a.subst ((i, b) :: σ) = a.subst σ := by
  cases a with
  | inf => rfl
  | var x n =>
    have hx : x ≠ i := fun h => hi (h ▸ ha)
    simp only [Size.subst, List.lookup_cons]
    have : (x == i) = false := beq_eq_false_iff_ne.mpr hx
    simp [this]

theorem TyWf.substSize_cons_fresh {Ψ : SizeCtx} {k : Nat} {A : Ty} (hA : TyWf Ψ k A) {i : Nat}
    (hi : i ∉ Ψ.dom) (b : Size) (σ : List (Nat × Size)) :
    A.substSize ((i, b) :: σ) = A.substSize σ := by
  induction hA with
  | unit _ => rfl
  | prod _ _ ihA ihB => simp only [Ty.substSize]; rw [ihA, ihB]
  | arr _ _ ihA ihB => simp only [Ty.substSize]; rw [ihA, ihB]
  | var _ => rfl
  | @mu k a S ha _ _ ih =>
    simp only [Ty.substSize]
    rw [Size.subst_cons_fresh ha hi]
    congr 1
    exact substSizeList_congr ih
  | @nu k a R ha _ _ ih =>
    simp only [Ty.substSize]
    rw [Size.subst_cons_fresh ha hi]
    congr 1
    exact substSizeList_congr ih
where
  substSizeList_congr {S : List Ty} {σ₁ σ₂ : List (Nat × Size)}
      (h : ∀ T ∈ S, T.substSize σ₁ = T.substSize σ₂) :
      Ty.substSizeList σ₁ S = Ty.substSizeList σ₂ S := by
    induction S with
    | nil => rfl
    | cons A S ih =>
      simp only [Ty.substSizeList]
      rw [h A (by simp), ih (fun T hT => h T (by simp [hT]))]

end NishtAbel2024V3
