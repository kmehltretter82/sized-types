import Solutions.V4.Interp

/-! # V4: syntactic lemmas about well-formed types -/

namespace NishtAbel2024V4

/-! ## List membership under the list-mapping operations -/

theorem Ty.mem_substTyList {S : List Ty} {k : Nat} {T T' : Ty} (h : T' ∈ Ty.substTyList S k T) :
    ∃ B ∈ S, T' = B.substTy k T := by
  induction S with
  | nil => simp [Ty.substTyList] at h
  | cons A S ih =>
    simp only [Ty.substTyList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨A, by simp, rfl⟩
    · obtain ⟨B, hB, rfl⟩ := ih h; exact ⟨B, by simp [hB], rfl⟩

theorem Ty.mem_openSzList {S : List Ty} {k : Nat} {b : Size} {T' : Ty}
    (h : T' ∈ Ty.openSzList S k b) : ∃ B ∈ S, T' = B.openSz k b := by
  induction S with
  | nil => simp [Ty.openSzList] at h
  | cons A S ih =>
    simp only [Ty.openSzList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨A, by simp, rfl⟩
    · obtain ⟨B, hB, rfl⟩ := ih h; exact ⟨B, by simp [hB], rfl⟩

theorem Ty.mem_substSizeList {S : List Ty} {σ : List (Nat × Size)} {T' : Ty}
    (h : T' ∈ Ty.substSizeList σ S) : ∃ B ∈ S, T' = B.substSize σ := by
  induction S with
  | nil => simp [Ty.substSizeList] at h
  | cons A S ih =>
    simp only [Ty.substSizeList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨A, by simp, rfl⟩
    · obtain ⟨B, hB, rfl⟩ := ih h; exact ⟨B, by simp [hB], rfl⟩

theorem Ty.mem_substFTyList {S : List Ty} {τ : List (Nat × Ty)} {T' : Ty}
    (h : T' ∈ Ty.substFTyList τ S) : ∃ B ∈ S, T' = B.substFTy τ := by
  induction S with
  | nil => simp [Ty.substFTyList] at h
  | cons A S ih =>
    simp only [Ty.substFTyList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨A, by simp, rfl⟩
    · obtain ⟨B, hB, rfl⟩ := ih h; exact ⟨B, by simp [hB], rfl⟩

/-! ## Weakening -/

theorem SizeWfAt.weaken {Ψ Ψ' : SizeCtx} {m m' : Nat} (h : ∀ i ∈ Ψ.dom, i ∈ Ψ'.dom)
    (hm : m ≤ m') {a : Size} (ha : SizeWfAt Ψ m a) : SizeWfAt Ψ' m' a := by
  cases a with
  | inf => trivial
  | var i n => exact h i ha
  | bvar k n => exact lt_of_lt_of_le (show k < m from ha) hm

theorem TyWf.weaken {Ψ : SizeCtx} {Θ : List Nat} {k m : Nat} {A : Ty} (hA : TyWf Ψ Θ k m A) :
    ∀ (Ψ' : SizeCtx) (Θ' : List Nat) (k' m' : Nat), (∀ i ∈ Ψ.dom, i ∈ Ψ'.dom) →
      (∀ X ∈ Θ, X ∈ Θ') → k ≤ k' → m ≤ m' → TyWf Ψ' Θ' k' m' A := by
  induction hA with
  | unit k m => intro _ _ _ _ _ _ _ _; exact .unit _ _
  | prod _ _ ihA ihB =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .prod (ihA Ψ' Θ' k' m' h hΘ hk hm) (ihB Ψ' Θ' k' m' h hΘ hk hm)
  | arr _ _ ihA ihB =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .arr (ihA Ψ' Θ' k' m' h hΘ hk hm) (ihB Ψ' Θ' k' m' h hΘ hk hm)
  | var hX => intro _ _ _ _ _ _ hk _; exact .var (by omega)
  | fvar hX => intro _ _ _ _ _ hΘ _ _; exact .fvar (hΘ _ hX)
  | mu ha _ hpos ih =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .mu (ha.weaken h hm) (fun T hT => ih T hT Ψ' Θ' (k' + 1) m' h hΘ (by omega) hm) hpos
  | nu ha _ hpos ih =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .nu (ha.weaken h hm) (fun T hT => ih T hT Ψ' Θ' (k' + 1) m' h hΘ (by omega) hm) hpos
  | allT _ ih =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .allT (ih Ψ' Θ' (k' + 1) m' h hΘ (by omega) hm)
  | exT _ ih =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .exT (ih Ψ' Θ' (k' + 1) m' h hΘ (by omega) hm)
  | allS ha _ ih =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .allS (ha.weaken h hm) (ih Ψ' Θ' k' (m' + 1) h hΘ hk (by omega))
  | exS ha _ ih =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .exS (ha.weaken h hm) (ih Ψ' Θ' k' (m' + 1) h hΘ hk (by omega))

theorem dom_append_left {Ψ Ψ' : SizeCtx} : ∀ i ∈ Ψ.dom, i ∈ (Ψ ++ Ψ').dom := by
  intro i hi
  simp only [SizeCtx.dom, List.map_append, List.mem_append]
  exact Or.inl hi

theorem mem_append_left' {Θ Θ' : List Nat} : ∀ X ∈ Θ, X ∈ Θ ++ Θ' :=
  fun _ h => List.mem_append_left _ h

/-- Weakening of locally closed types to larger contexts. -/
theorem TyWf.mono {Ψ : SizeCtx} {Θ : List Nat} {A : Ty} (hA : TyWf Ψ Θ 0 0 A) {Ψ' : SizeCtx}
    {Θ' : List Nat} (h : ∀ i ∈ Ψ.dom, i ∈ Ψ'.dom) (hΘ : ∀ X ∈ Θ, X ∈ Θ') : TyWf Ψ' Θ' 0 0 A :=
  hA.weaken Ψ' Θ' 0 0 h hΘ le_rfl le_rfl

/-! ## Polarity -/

/-- Variables at or above the level do not occur, so any polarity holds. -/
theorem TyWf.polIn {Ψ : SizeCtx} {Θ : List Nat} {k m : Nat} {A : Ty} (hA : TyWf Ψ Θ k m A) :
    ∀ (b : Bool) (j : Nat), k ≤ j → PolIn b j A := by
  induction hA with
  | unit k m => intro b j _; exact .unit _ _
  | prod _ _ ihA ihB => intro b j h; exact .prod (ihA b j h) (ihB b j h)
  | arr _ _ ihA ihB => intro b j h; exact .arr (ihA (!b) j h) (ihB b j h)
  | var hX => intro b j h; exact .var_other (by omega)
  | fvar _ => intro b j _; exact .fvar _ _ _
  | mu _ _ _ ih => intro b j h; exact .mu (fun T hT => ih T hT b (j + 1) (by omega))
  | nu _ _ _ ih => intro b j h; exact .nu (fun T hT => ih T hT b (j + 1) (by omega))
  | allT _ ih => intro b j h; exact .allT (ih b (j + 1) (by omega))
  | exT _ ih => intro b j h; exact .exT (ih b (j + 1) (by omega))
  | allS _ _ ih => intro b j h; exact .allS (ih b j h)
  | exS _ _ ih => intro b j h; exact .exS (ih b j h)

/-- Substituting a closed type below a position keeps polarities above it. -/
theorem PolIn.substTy {b : Bool} {j : Nat} {B : Ty} (hB : PolIn b j B) :
    ∀ (Ψ : SizeCtx) (Θ : List Nat) (T : Ty) (k : Nat), TyWf Ψ Θ 0 0 T → j < k →
      PolIn b j (B.substTy k T) := by
  induction hB with
  | unit b j => intro _ _ _ _ _ _; exact .unit _ _
  | prod _ _ ihA ihB =>
    intro Ψ Θ T k hT hjk; exact .prod (ihA Ψ Θ T k hT hjk) (ihB Ψ Θ T k hT hjk)
  | arr _ _ ihA ihB =>
    intro Ψ Θ T k hT hjk; exact .arr (ihA Ψ Θ T k hT hjk) (ihB Ψ Θ T k hT hjk)
  | var_self j =>
    intro _ _ _ k hT hjk
    have h1 : j ≠ k := by omega
    have h2 : ¬ k < j := by omega
    simp only [Ty.substTy, h1, h2, if_false]
    exact .var_self j
  | @var_other b j X hne =>
    intro _ _ T k hT hjk
    simp only [Ty.substTy]
    by_cases h1 : X = k
    · simp only [h1, if_true]; exact hT.polIn b j (by omega)
    · by_cases h2 : k < X
      · simp only [h1, h2, if_true, if_false]; exact .var_other (by omega)
      · simp only [h1, h2, if_false]; exact .var_other hne
  | fvar b j X => intro _ _ _ _ _ _; exact .fvar _ _ _
  | mu _ ih =>
    intro Ψ Θ T k hT hjk
    simp only [Ty.substTy]
    refine .mu fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    exact ih B hB _ _ _ _ hT (by omega)
  | nu _ ih =>
    intro Ψ Θ T k hT hjk
    simp only [Ty.substTy]
    refine .nu fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    exact ih B hB _ _ _ _ hT (by omega)
  | allT _ ih => intro Ψ Θ T k hT hjk; exact .allT (ih Ψ Θ T (k + 1) hT (by omega))
  | exT _ ih => intro Ψ Θ T k hT hjk; exact .exT (ih Ψ Θ T (k + 1) hT (by omega))
  | allS _ ih => intro Ψ Θ T k hT hjk; exact .allS (ih Ψ Θ T k hT hjk)
  | exS _ ih => intro Ψ Θ T k hT hjk; exact .exS (ih Ψ Θ T k hT hjk)

/-- Sizes do not affect polarities. -/
theorem PolIn.openSz {b : Bool} {j : Nat} {B : Ty} (hB : PolIn b j B) :
    ∀ (k : Nat) (c : Size), PolIn b j (B.openSz k c) := by
  induction hB with
  | unit b j => intro _ _; exact .unit _ _
  | prod _ _ ihA ihB => intro k c; exact .prod (ihA k c) (ihB k c)
  | arr _ _ ihA ihB => intro k c; exact .arr (ihA k c) (ihB k c)
  | var_self j => intro _ _; exact .var_self j
  | var_other hne => intro _ _; exact .var_other hne
  | fvar b j X => intro _ _; exact .fvar _ _ _
  | mu _ ih =>
    intro k c
    simp only [Ty.openSz]
    refine .mu fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_openSzList hT'
    exact ih B hB k c
  | nu _ ih =>
    intro k c
    simp only [Ty.openSz]
    refine .nu fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_openSzList hT'
    exact ih B hB k c
  | allT _ ih => intro k c; exact .allT (ih k c)
  | exT _ ih => intro k c; exact .exT (ih k c)
  | allS _ ih => intro k c; exact .allS (ih (k + 1) c)
  | exS _ ih => intro k c; exact .exS (ih (k + 1) c)

/-! ## Well-formedness of instantiations -/

/-- Substituting a closed type for the bound type variable at the level lowers the level. -/
theorem TyWf.substTy {Ψ : SizeCtx} {Θ : List Nat} {n m : Nat} {A : Ty} (hA : TyWf Ψ Θ n m A) :
    ∀ (k : Nat) (T : Ty), n = k + 1 → TyWf Ψ Θ 0 0 T → TyWf Ψ Θ k m (A.substTy k T) := by
  induction hA with
  | unit _ _ => intro _ _ _ _; exact .unit _ _
  | prod _ _ ihA ihB => intro k T hn hT; exact .prod (ihA k T hn hT) (ihB k T hn hT)
  | arr _ _ ihA ihB => intro k T hn hT; exact .arr (ihA k T hn hT) (ihB k T hn hT)
  | @var n m X hX =>
    intro k T hn hT
    simp only [Ty.substTy]
    by_cases h1 : X = k
    · simp only [h1, if_true]; exact hT.weaken _ _ _ _ (fun i hi => hi) (fun X h => h) (by omega) (by omega)
    · have h2 : ¬ k < X := by omega
      simp only [h1, h2, if_false]; exact .var (by omega)
  | fvar hX => intro _ _ _ _; exact .fvar hX
  | mu ha _ hpos ih =>
    intro k T hn hT
    simp only [Ty.substTy]
    refine .mu ha (fun T' hT' => ?_) (fun T' hT' => ?_)
    · obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
      exact ih B hB _ _ (by omega) hT
    · obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
      exact (hpos B hB).substTy _ _ _ _ hT (by omega)
  | nu ha _ hpos ih =>
    intro k T hn hT
    simp only [Ty.substTy]
    refine .nu ha (fun T' hT' => ?_) (fun T' hT' => ?_)
    · obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
      exact ih B hB _ _ (by omega) hT
    · obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
      exact (hpos B hB).substTy _ _ _ _ hT (by omega)
  | allT _ ih => intro k T hn hT; exact .allT (ih (k + 1) T (by omega) hT)
  | exT _ ih => intro k T hn hT; exact .exT (ih (k + 1) T (by omega) hT)
  | allS ha _ ih => intro k T hn hT; exact .allS ha (ih k T hn hT)
  | exS ha _ ih => intro k T hn hT; exact .exS ha (ih k T hn hT)

theorem SizeWfAt.openAt {Ψ : SizeCtx} {n : Nat} {a : Size} (ha : SizeWfAt Ψ n a) (m : Nat)
    (hn : n = m + 1) {c : Size} (hc : SizeWf Ψ c) : SizeWfAt Ψ m (a.openAt m c) := by
  cases a with
  | inf => trivial
  | var i k => exact ha
  | bvar k' k =>
    simp only [Size.openAt]
    have hk' : k' < n := ha
    by_cases h1 : k' = m
    · simp only [h1, if_true]
      cases c with
      | inf => trivial
      | var i l => exact hc
      | bvar l l' => exact absurd hc (Nat.not_lt_zero _)
    · have h2 : ¬ m < k' := by omega
      simp only [h1, h2, if_false]
      show k' < m
      omega

/-- Opening the bound size variable at the level with a locally closed size lowers the level. -/
theorem TyWf.openSz {Ψ : SizeCtx} {Θ : List Nat} {k n : Nat} {A : Ty} (hA : TyWf Ψ Θ k n A) :
    ∀ (m : Nat) (c : Size), n = m + 1 → SizeWf Ψ c → TyWf Ψ Θ k m (A.openSz m c) := by
  induction hA with
  | unit _ _ => intro _ _ _ _; exact .unit _ _
  | prod _ _ ihA ihB => intro m c hn hc; exact .prod (ihA m c hn hc) (ihB m c hn hc)
  | arr _ _ ihA ihB => intro m c hn hc; exact .arr (ihA m c hn hc) (ihB m c hn hc)
  | var hX => intro _ _ _ _; exact .var hX
  | fvar hX => intro _ _ _ _; exact .fvar hX
  | mu ha _ hpos ih =>
    intro m c hn hc
    simp only [Ty.openSz]
    refine .mu (ha.openAt m hn hc) (fun T' hT' => ?_) (fun T' hT' => ?_)
    · obtain ⟨B, hB, rfl⟩ := Ty.mem_openSzList hT'
      exact ih B hB m c hn hc
    · obtain ⟨B, hB, rfl⟩ := Ty.mem_openSzList hT'
      exact (hpos B hB).openSz _ _
  | nu ha _ hpos ih =>
    intro m c hn hc
    simp only [Ty.openSz]
    refine .nu (ha.openAt m hn hc) (fun T' hT' => ?_) (fun T' hT' => ?_)
    · obtain ⟨B, hB, rfl⟩ := Ty.mem_openSzList hT'
      exact ih B hB m c hn hc
    · obtain ⟨B, hB, rfl⟩ := Ty.mem_openSzList hT'
      exact (hpos B hB).openSz _ _
  | allT _ ih => intro m c hn hc; exact .allT (ih m c hn hc)
  | exT _ ih => intro m c hn hc; exact .exT (ih m c hn hc)
  | allS ha _ ih => intro m c hn hc; exact .allS (ha.openAt m hn hc) (ih (m + 1) c (by omega) hc)
  | exS ha _ ih => intro m c hn hc; exact .exS (ha.openAt m hn hc) (ih (m + 1) c (by omega) hc)

/-- The unfolded branch of a well-formed closed `μ`/`ν` is well-formed. -/
theorem TyWf.unfold_mu {Ψ : SizeCtx} {Θ : List Nat} {a b : Size} {S : List Ty} {c : Nat}
    {Sc : Ty} (hwf : TyWf Ψ Θ 0 0 (.mu a S)) (hc : S[c]? = some Sc) (hb : SizeWf Ψ b) :
    TyWf Ψ Θ 0 0 (Sc.substTy 0 (.mu b S)) := by
  cases hwf with
  | mu _ hS hpos =>
    have hmem : Sc ∈ S := List.mem_of_getElem? hc
    exact (hS Sc hmem).substTy 0 _ rfl (.mu hb hS hpos)

theorem TyWf.unfold_nu {Ψ : SizeCtx} {Θ : List Nat} {a b : Size} {R : List Ty} {d : Nat}
    {Rd : Ty} (hwf : TyWf Ψ Θ 0 0 (.nu a R)) (hd : R[d]? = some Rd) (hb : SizeWf Ψ b) :
    TyWf Ψ Θ 0 0 (Rd.substTy 0 (.nu b R)) := by
  cases hwf with
  | nu _ hR hpos =>
    have hmem : Rd ∈ R := List.mem_of_getElem? hd
    exact (hR Rd hmem).substTy 0 _ rfl (.nu hb hR hpos)

/-- Opening `∀X`/`∃X` with a closed type. -/
theorem TyWf.open_ty {Ψ : SizeCtx} {Θ : List Nat} {B T : Ty} (hB : TyWf Ψ Θ 1 0 B)
    (hT : TyWf Ψ Θ 0 0 T) : TyWf Ψ Θ 0 0 (B.substTy 0 T) :=
  hB.substTy 0 T rfl hT

/-- Opening `∀(j<a)`/`∃(j<a)` with a locally closed size. -/
theorem TyWf.open_sz {Ψ : SizeCtx} {Θ : List Nat} {B : Ty} {c : Size} (hB : TyWf Ψ Θ 0 1 B)
    (hc : SizeWf Ψ c) : TyWf Ψ Θ 0 0 (B.openSz 0 c) :=
  hB.openSz 0 c rfl hc

/-! ## Commutation of the substitutions -/

theorem Size.shift_shift (a : Size) (m n : Nat) : (a.shift m).shift n = a.shift (m + n) := by
  cases a <;> simp [Size.shift, Nat.add_assoc]

theorem Size.subst_shift_var {σ : List (Nat × Size)} (hσ : VarSubst σ) (j m n : Nat) :
    ((Size.var j m).shift n).subst σ = ((Size.var j m).subst σ).shift n := by
  simp only [Size.shift, Size.subst]
  cases h : σ.lookup j with
  | none => rfl
  | some b =>
    obtain ⟨j', m', rfl⟩ := hσ j _ h
    simp [Size.shift, Nat.add_assoc]

theorem Size.subst_openAt {σ : List (Nat × Size)} (hσ : VarSubst σ) (a : Size) (k j m : Nat) :
    (a.openAt k (.var j m)).subst σ = (a.subst σ).openAt k ((Size.var j m).subst σ) := by
  cases a with
  | inf => rfl
  | var i n =>
    simp only [Size.openAt, Size.subst]
    cases h : σ.lookup i with
    | none => rfl
    | some b =>
      obtain ⟨j', m', rfl⟩ := hσ i _ h
      rfl
  | bvar k' n =>
    show (Size.openAt (.bvar k' n) k (.var j m)).subst σ =
      Size.openAt (.bvar k' n) k ((Size.var j m).subst σ)
    simp only [Size.openAt]
    by_cases h1 : k' = k
    · simp only [h1, if_true]
      exact Size.subst_shift_var hσ j m n
    · by_cases h2 : k < k'
      · simp only [h1, h2, if_true, if_false]; rfl
      · simp only [h1, h2, if_false]; rfl

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
  | .fvar _, _ => rfl
  | .mu a S, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSizeList_substTyList σ T S (k + 1)]
  | .nu a R, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSizeList_substTyList σ T R (k + 1)]
  | .allT B, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T B (k + 1)]
  | .exT B, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T B (k + 1)]
  | .allS a B, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T B k]
  | .exS a B, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T B k]

theorem Ty.substSizeList_substTyList (σ : List (Nat × Size)) (T : Ty) :
    ∀ (S : List Ty) (k : Nat), Ty.substSizeList σ (Ty.substTyList S k T) =
      Ty.substTyList (Ty.substSizeList σ S) k (T.substSize σ)
  | [], _ => rfl
  | A :: S, k => by
    simp only [Ty.substTyList, Ty.substSizeList]
    rw [Ty.substSize_substTy σ T A k, Ty.substSizeList_substTyList σ T S k]

end

mutual

theorem Ty.substSize_openSz {σ : List (Nat × Size)} (hσ : VarSubst σ) (j m : Nat) :
    ∀ (A : Ty) (k : Nat), (A.openSz k (.var j m)).substSize σ =
      (A.substSize σ).openSz k ((Size.var j m).subst σ)
  | .unit, _ => rfl
  | .prod A B, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Ty.substSize_openSz hσ j m A k, Ty.substSize_openSz hσ j m B k]
  | .arr A B, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Ty.substSize_openSz hσ j m A k, Ty.substSize_openSz hσ j m B k]
  | .var _, _ => rfl
  | .fvar _, _ => rfl
  | .mu a S, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Size.subst_openAt hσ, Ty.substSizeList_openSzList hσ j m S k]
  | .nu a R, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Size.subst_openAt hσ, Ty.substSizeList_openSzList hσ j m R k]
  | .allT B, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Ty.substSize_openSz hσ j m B k]
  | .exT B, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Ty.substSize_openSz hσ j m B k]
  | .allS a B, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Size.subst_openAt hσ, Ty.substSize_openSz hσ j m B (k + 1)]
  | .exS a B, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Size.subst_openAt hσ, Ty.substSize_openSz hσ j m B (k + 1)]

theorem Ty.substSizeList_openSzList {σ : List (Nat × Size)} (hσ : VarSubst σ) (j m : Nat) :
    ∀ (S : List Ty) (k : Nat), Ty.substSizeList σ (Ty.openSzList S k (.var j m)) =
      Ty.openSzList (Ty.substSizeList σ S) k ((Size.var j m).subst σ)
  | [], _ => rfl
  | A :: S, k => by
    simp only [Ty.openSzList, Ty.substSizeList]
    rw [Ty.substSize_openSz hσ j m A k, Ty.substSizeList_openSzList hσ j m S k]

end

/-- Closed types are not affected by substituting for bound type variables. -/
theorem TyWf.substTy_id {Ψ : SizeCtx} {Θ : List Nat} {n m : Nat} {A : Ty} (hA : TyWf Ψ Θ n m A) :
    ∀ (k : Nat) (U : Ty), n ≤ k → A.substTy k U = A := by
  induction hA with
  | unit _ _ => intro _ _ _; rfl
  | prod _ _ ihA ihB => intro k U h; simp only [Ty.substTy]; rw [ihA k U h, ihB k U h]
  | arr _ _ ihA ihB => intro k U h; simp only [Ty.substTy]; rw [ihA k U h, ihB k U h]
  | var hX =>
    intro k U h
    rename_i n m X
    have h1 : X ≠ k := by omega
    have h2 : ¬ k < X := by omega
    simp [Ty.substTy, h1, h2]
  | fvar _ => intro _ _ _; rfl
  | @mu n m a S _ _ _ ih =>
    intro k U h
    simp only [Ty.substTy]
    congr 1
    exact listEq ih (k + 1) U (by omega)
  | @nu n m a R _ _ _ ih =>
    intro k U h
    simp only [Ty.substTy]
    congr 1
    exact listEq ih (k + 1) U (by omega)
  | allT _ ih => intro k U h; simp only [Ty.substTy]; rw [ih (k + 1) U (by omega)]
  | exT _ ih => intro k U h; simp only [Ty.substTy]; rw [ih (k + 1) U (by omega)]
  | allS _ _ ih => intro k U h; simp only [Ty.substTy]; rw [ih k U h]
  | exS _ _ ih => intro k U h; simp only [Ty.substTy]; rw [ih k U h]
where
  listEq {S : List Ty} {n : Nat} (ih : ∀ T ∈ S, ∀ (k : Nat) (U : Ty), n ≤ k → T.substTy k U = T)
      (k : Nat) (U : Ty) (h : n ≤ k) : Ty.substTyList S k U = S := by
    induction S with
    | nil => rfl
    | cons A S ihS =>
      simp only [Ty.substTyList]
      rw [ih A (by simp) k U h, ihS (fun T hT => ih T (by simp [hT]))]

/-- Closed types are not affected by opening bound size variables. -/
theorem TyWf.openSz_id {Ψ : SizeCtx} {Θ : List Nat} {n m : Nat} {A : Ty} (hA : TyWf Ψ Θ n m A) :
    ∀ (k : Nat) (c : Size), m ≤ k → A.openSz k c = A := by
  have hsz : ∀ {m k : Nat} {a : Size} (c : Size), SizeWfAt Ψ m a → m ≤ k → a.openAt k c = a := by
    intro m k a c ha h
    cases a with
    | inf => rfl
    | var i n => rfl
    | bvar k' n =>
      have hk : k' < m := ha
      have h1 : k' ≠ k := by omega
      have h2 : ¬ k < k' := by omega
      simp [Size.openAt, h1, h2]
  induction hA with
  | unit _ _ => intro _ _ _; rfl
  | prod _ _ ihA ihB => intro k c h; simp only [Ty.openSz]; rw [ihA k c h, ihB k c h]
  | arr _ _ ihA ihB => intro k c h; simp only [Ty.openSz]; rw [ihA k c h, ihB k c h]
  | var _ => intro _ _ _; rfl
  | fvar _ => intro _ _ _; rfl
  | @mu n m a S ha _ _ ih =>
    intro k c h
    simp only [Ty.openSz]
    rw [hsz c ha h]
    congr 1
    exact listEq ih k c h
  | @nu n m a R ha _ _ ih =>
    intro k c h
    simp only [Ty.openSz]
    rw [hsz c ha h]
    congr 1
    exact listEq ih k c h
  | allT _ ih => intro k c h; simp only [Ty.openSz]; rw [ih k c h]
  | exT _ ih => intro k c h; simp only [Ty.openSz]; rw [ih k c h]
  | allS ha _ ih => intro k c h; simp only [Ty.openSz]; rw [hsz c ha h, ih (k + 1) c (by omega)]
  | exS ha _ ih => intro k c h; simp only [Ty.openSz]; rw [hsz c ha h, ih (k + 1) c (by omega)]
where
  listEq {S : List Ty} {m : Nat} (ih : ∀ T ∈ S, ∀ (k : Nat) (c : Size), m ≤ k → T.openSz k c = T)
      (k : Nat) (c : Size) (h : m ≤ k) : Ty.openSzList S k c = S := by
    induction S with
    | nil => rfl
    | cons A S ihS =>
      simp only [Ty.openSzList]
      rw [ih A (by simp) k c h, ihS (fun T hT => ih T (by simp [hT]))]

/-- Substitutions for free type variables whose values are closed types. -/
def ClosedTSubst (τ : List (Nat × Ty)) : Prop :=
  ∀ X T, τ.lookup X = some T → ∃ Ψ Θ, TyWf Ψ Θ 0 0 T

mutual

theorem Ty.substFTy_substTy {τ : List (Nat × Ty)} (hτ : ClosedTSubst τ) (T : Ty) :
    ∀ (A : Ty) (k : Nat), (A.substTy k T).substFTy τ = (A.substFTy τ).substTy k (T.substFTy τ)
  | .unit, _ => rfl
  | .prod A B, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T A k, Ty.substFTy_substTy hτ T B k]
  | .arr A B, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T A k, Ty.substFTy_substTy hτ T B k]
  | .var X, k => by
    simp only [Ty.substTy, Ty.substFTy]
    by_cases h1 : X = k
    · simp [h1]
    · by_cases h2 : k < X
      · simp [h1, h2, Ty.substFTy]
      · simp [h1, h2, Ty.substFTy]
  | .fvar X, k => by
    simp only [Ty.substTy, Ty.substFTy]
    cases h : τ.lookup X with
    | none => rfl
    | some U =>
      obtain ⟨Ψ, Θ, hU⟩ := hτ X U h
      simp only [Option.getD_some]
      exact (hU.substTy_id k _ (Nat.zero_le _)).symm
  | .mu a S, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTyList_substTyList hτ T S (k + 1)]
  | .nu a R, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTyList_substTyList hτ T R (k + 1)]
  | .allT B, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T B (k + 1)]
  | .exT B, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T B (k + 1)]
  | .allS a B, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T B k]
  | .exS a B, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T B k]

theorem Ty.substFTyList_substTyList {τ : List (Nat × Ty)} (hτ : ClosedTSubst τ) (T : Ty) :
    ∀ (S : List Ty) (k : Nat), Ty.substFTyList τ (Ty.substTyList S k T) =
      Ty.substTyList (Ty.substFTyList τ S) k (T.substFTy τ)
  | [], _ => rfl
  | A :: S, k => by
    simp only [Ty.substTyList, Ty.substFTyList]
    rw [Ty.substFTy_substTy hτ T A k, Ty.substFTyList_substTyList hτ T S k]

end

mutual

theorem Ty.substFTy_openSz {τ : List (Nat × Ty)} (hτ : ClosedTSubst τ) (c : Size) :
    ∀ (A : Ty) (k : Nat), (A.openSz k c).substFTy τ = (A.substFTy τ).openSz k c
  | .unit, _ => rfl
  | .prod A B, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c A k, Ty.substFTy_openSz hτ c B k]
  | .arr A B, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c A k, Ty.substFTy_openSz hτ c B k]
  | .var _, _ => rfl
  | .fvar X, k => by
    simp only [Ty.openSz, Ty.substFTy]
    cases h : τ.lookup X with
    | none => rfl
    | some U =>
      obtain ⟨Ψ, Θ, hU⟩ := hτ X U h
      simp only [Option.getD_some]
      exact (hU.openSz_id k c (Nat.zero_le _)).symm
  | .mu a S, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTyList_openSzList hτ c S k]
  | .nu a R, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTyList_openSzList hτ c R k]
  | .allT B, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c B k]
  | .exT B, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c B k]
  | .allS a B, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c B (k + 1)]
  | .exS a B, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c B (k + 1)]

theorem Ty.substFTyList_openSzList {τ : List (Nat × Ty)} (hτ : ClosedTSubst τ) (c : Size) :
    ∀ (S : List Ty) (k : Nat),
      Ty.substFTyList τ (Ty.openSzList S k c) = Ty.openSzList (Ty.substFTyList τ S) k c
  | [], _ => rfl
  | A :: S, k => by
    simp only [Ty.openSzList, Ty.substFTyList]
    rw [Ty.substFTy_openSz hτ c A k, Ty.substFTyList_openSzList hτ c S k]

end

/-! ## Fresh variables do not matter to substitution -/

theorem Size.subst_cons_fresh {Ψ : SizeCtx} {m : Nat} {a : Size} (ha : SizeWfAt Ψ m a) {i : Nat}
    (hi : i ∉ Ψ.dom) (b : Size) (σ : List (Nat × Size)) : a.subst ((i, b) :: σ) = a.subst σ := by
  cases a with
  | inf => rfl
  | bvar _ _ => rfl
  | var x n =>
    have hx : x ≠ i := fun h => hi (h ▸ ha)
    simp only [Size.subst, List.lookup_cons]
    have : (x == i) = false := beq_eq_false_iff_ne.mpr hx
    simp [this]

theorem substSizeList_congr {S : List Ty} {σ₁ σ₂ : List (Nat × Size)}
    (h : ∀ T ∈ S, T.substSize σ₁ = T.substSize σ₂) :
    Ty.substSizeList σ₁ S = Ty.substSizeList σ₂ S := by
  induction S with
  | nil => rfl
  | cons A S ih =>
    simp only [Ty.substSizeList]
    rw [h A (by simp), ih (fun T hT => h T (by simp [hT]))]

theorem substFTyList_congr {S : List Ty} {τ₁ τ₂ : List (Nat × Ty)}
    (h : ∀ T ∈ S, T.substFTy τ₁ = T.substFTy τ₂) :
    Ty.substFTyList τ₁ S = Ty.substFTyList τ₂ S := by
  induction S with
  | nil => rfl
  | cons A S ih =>
    simp only [Ty.substFTyList]
    rw [h A (by simp), ih (fun T hT => h T (by simp [hT]))]

theorem TyWf.substSize_cons_fresh {Ψ : SizeCtx} {Θ : List Nat} {k m : Nat} {A : Ty}
    (hA : TyWf Ψ Θ k m A) {i : Nat} (hi : i ∉ Ψ.dom) (b : Size) (σ : List (Nat × Size)) :
    A.substSize ((i, b) :: σ) = A.substSize σ := by
  induction hA with
  | unit _ _ => rfl
  | prod _ _ ihA ihB => simp only [Ty.substSize]; rw [ihA, ihB]
  | arr _ _ ihA ihB => simp only [Ty.substSize]; rw [ihA, ihB]
  | var _ => rfl
  | fvar _ => rfl
  | mu ha _ _ ih =>
    simp only [Ty.substSize]
    rw [Size.subst_cons_fresh ha hi]
    congr 1
    exact substSizeList_congr ih
  | nu ha _ _ ih =>
    simp only [Ty.substSize]
    rw [Size.subst_cons_fresh ha hi]
    congr 1
    exact substSizeList_congr ih
  | allT _ ih => simp only [Ty.substSize]; rw [ih]
  | exT _ ih => simp only [Ty.substSize]; rw [ih]
  | allS ha _ ih => simp only [Ty.substSize]; rw [Size.subst_cons_fresh ha hi, ih]
  | exS ha _ ih => simp only [Ty.substSize]; rw [Size.subst_cons_fresh ha hi, ih]

theorem TyWf.substFTy_cons_fresh {Ψ : SizeCtx} {Θ : List Nat} {k m : Nat} {A : Ty}
    (hA : TyWf Ψ Θ k m A) {X : Nat} (hX : X ∉ Θ) (T : Ty) (τ : List (Nat × Ty)) :
    A.substFTy ((X, T) :: τ) = A.substFTy τ := by
  induction hA with
  | unit _ _ => rfl
  | prod _ _ ihA ihB => simp only [Ty.substFTy]; rw [ihA, ihB]
  | arr _ _ ihA ihB => simp only [Ty.substFTy]; rw [ihA, ihB]
  | var _ => rfl
  | @fvar k m Y hY =>
    have hne : Y ≠ X := fun h => hX (h ▸ hY)
    simp only [Ty.substFTy, List.lookup_cons]
    have : (Y == X) = false := beq_eq_false_iff_ne.mpr hne
    simp [this]
  | mu _ _ _ ih =>
    simp only [Ty.substFTy]
    congr 1
    exact substFTyList_congr ih
  | nu _ _ _ ih =>
    simp only [Ty.substFTy]
    congr 1
    exact substFTyList_congr ih
  | allT _ ih => simp only [Ty.substFTy]; rw [ih]
  | exT _ ih => simp only [Ty.substFTy]; rw [ih]
  | allS _ _ ih => simp only [Ty.substFTy]; rw [ih]
  | exS _ _ ih => simp only [Ty.substFTy]; rw [ih]

theorem Ty.substSizeList_getElem? (σ : List (Nat × Size)) :
    ∀ (S : List Ty) (d : Nat), (Ty.substSizeList σ S)[d]? = (S[d]?).map (Ty.substSize σ)
  | [], d => by simp [Ty.substSizeList]
  | A :: S, 0 => by simp [Ty.substSizeList]
  | A :: S, d + 1 => by
    simp only [Ty.substSizeList, List.getElem?_cons_succ]
    exact Ty.substSizeList_getElem? σ S d

theorem Ty.substFTyList_getElem? (τ : List (Nat × Ty)) :
    ∀ (S : List Ty) (d : Nat), (Ty.substFTyList τ S)[d]? = (S[d]?).map (Ty.substFTy τ)
  | [], d => by simp [Ty.substFTyList]
  | A :: S, 0 => by simp [Ty.substFTyList]
  | A :: S, d + 1 => by
    simp only [Ty.substFTyList, List.getElem?_cons_succ]
    exact Ty.substFTyList_getElem? τ S d

end NishtAbel2024V4
