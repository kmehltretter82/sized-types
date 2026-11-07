import Solutions.V5.InfErase

/-! # V5 inference: comparison of types under a coherent substitution gives subtyping -/

namespace NishtAbel2024V5

/-! ## Well-formed sizes: weakening and type substitution -/

theorem SizesWf.weaken {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A) :
    ∀ {m' : Nat}, m ≤ m' → SizesWf Ψ m' A := by
  induction h with
  | unit => intros; exact .unit _
  | prod _ _ ihA ihB => intro m' hm; exact .prod (ihA hm) (ihB hm)
  | arr _ _ ihA ihB => intro m' hm; exact .arr (ihA hm) (ihB hm)
  | var => intros; exact .var _ _
  | fvar => intros; exact .fvar _ _
  | lam _ ih => intro m' hm; exact .lam (ih hm)
  | app _ _ ihF ihG => intro m' hm; exact .app (ihF hm) (ihG hm)
  | mu ha _ ih => intro m' hm; exact .mu (ha.weaken (fun _ h => h) hm) fun T hT => ih T hT hm
  | nu ha _ ih => intro m' hm; exact .nu (ha.weaken (fun _ h => h) hm) fun T hT => ih T hT hm
  | allT _ ih => intro m' hm; exact .allT (ih hm)
  | exT _ ih => intro m' hm; exact .exT (ih hm)
  | allS ha _ ih => intro m' hm; exact .allS (ha.weaken (fun _ h => h) hm) (ih (by omega))
  | exS ha _ ih => intro m' hm; exact .exS (ha.weaken (fun _ h => h) hm) (ih (by omega))

theorem SizesWf.substTy {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A) :
    ∀ {k : Nat} {G : Ty}, SizesWf Ψ 0 G → SizesWf Ψ m (A.substTy k G) := by
  induction h with
  | unit => intros; exact .unit _
  | prod _ _ ihA ihB => intro k G hG; exact .prod (ihA hG) (ihB hG)
  | arr _ _ ihA ihB => intro k G hG; exact .arr (ihA hG) (ihB hG)
  | var m X =>
    intro k G hG
    simp only [Ty.substTy]
    split
    · exact hG.weaken (Nat.zero_le _)
    · split
      · exact .var _ _
      · exact .var _ _
  | fvar => intros; exact .fvar _ _
  | lam _ ih => intro k G hG; exact .lam (ih hG)
  | app _ _ ihF ihG => intro k G hG; exact .app (ihF hG) (ihG hG)
  | mu ha _ ih =>
    intro k G hG
    simp only [Ty.substTy]
    refine .mu ha fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    exact ih B hB hG
  | nu ha _ ih =>
    intro k G hG
    simp only [Ty.substTy]
    refine .nu ha fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    exact ih B hB hG
  | allT _ ih => intro k G hG; exact .allT (ih hG)
  | exT _ ih => intro k G hG; exact .exT (ih hG)
  | allS ha _ ih => intro k G hG; exact .allS ha (ih hG)
  | exS ha _ ih => intro k G hG; exact .exS ha (ih hG)

theorem SizesWf.open_fvar {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A) (X : Nat) :
    SizesWf Ψ m (A.substTy 0 (.fvar X)) :=
  h.substTy (.fvar 0 X)

/-! ## Constraints of comparisons -/

theorem Coherent.left {φ : FlexSubst} {C₁ C₂ : List SConstr} (h : Coherent φ (C₁ ++ C₂)) :
    Coherent φ C₁ := fun c hc => h c (List.mem_append_left _ hc)

theorem Coherent.right {φ : FlexSubst} {C₁ C₂ : List SConstr} (h : Coherent φ (C₁ ++ C₂)) :
    Coherent φ C₂ := fun c hc => h c (List.mem_append_right _ hc)

theorem Coherent.tail {φ : FlexSubst} {c : SConstr} {C : List SConstr} (h : Coherent φ (c :: C)) :
    Coherent φ C := fun c' hc => h c' (List.mem_cons_of_mem _ hc)

theorem Coherent.head {φ : FlexSubst} {c : SConstr} {C : List SConstr} (h : Coherent φ (c :: C)) :
    c.Holds φ := h c (List.mem_cons_self)

theorem compareList_length {Ψ : SizeCtx} {Δ : KCtx} {X : Nat} {S S' : List Ty}
    {C : List SConstr} (h : CompareList Ψ Δ X S S' C) : S.length = S'.length := by
  induction S generalizing S' C with
  | nil => cases h; rfl
  | cons T S ih =>
    cases h with
    | cons _ h' => simp [ih h']

theorem Ty.substSizeList_length' (σ : List (Nat × Size)) (S : List Ty) :
    (Ty.substSizeList σ S).length = S.length := Ty.substSizeList_length σ S

theorem Ty.substSizeList_getElem?' (σ : List (Nat × Size)) (S : List Ty) (d : Nat) :
    (Ty.substSizeList σ S)[d]? = (S[d]?).map (Ty.substSize σ) := Ty.substSizeList_getElem? σ S d

/-! ## Soundness of comparison -/

theorem mem_substSizeList_of_getElem? {σ : List (Nat × Size)} {S : List Ty} {c : Nat} {T : Ty}
    (h : (Ty.substSizeList σ S)[c]? = some T) : T ∈ Ty.substSizeList σ S :=
  List.mem_of_getElem? h

/-- The statement for one comparison. -/
def CompareOK (φ : FlexSubst) (Ψ : SizeCtx) (Δ : KCtx) (A B : Ty) (κ : Kind) : Prop :=
  SizesWf (Ψ.substBounds φ) 0 (A.substSize φ) → SizesWf (Ψ.substBounds φ) 0 (B.substSize φ) →
    SubTy (Ψ.substBounds φ) Δ (A.substSize φ) (B.substSize φ) κ

theorem SizeCtx.substBounds_dom (φ : FlexSubst) (Ψ : SizeCtx) :
    (Ψ.substBounds φ).dom = Ψ.dom := by
  simp [SizeCtx.substBounds, SizeCtx.dom]

theorem functors_sub {φ : FlexSubst} {Ψ : SizeCtx} {Δ : KCtx} {X : Nat} {S S' : List Ty}
    (hS : ∀ T ∈ Ty.substSizeList φ S, SizesWf (Ψ.substBounds φ) 0 T)
    (hS' : ∀ T ∈ Ty.substSizeList φ S', SizesWf (Ψ.substBounds φ) 0 T)
    (ih : ∀ (c : Nat) (U U' : Ty), S[c]? = some U → S'[c]? = some U' →
      CompareOK φ Ψ (Δ ++ [(X, .mix, .star)]) (U.substTy 0 (.fvar X)) (U'.substTy 0 (.fvar X))
        .star) :
    ∀ (c : Nat) (T T' : Ty), (Ty.substSizeList φ S)[c]? = some T →
      (Ty.substSizeList φ S')[c]? = some T' →
      SubTy (Ψ.substBounds φ) (Δ ++ [(X, .mix, .star)]) (T.substTy 0 (.fvar X))
        (T'.substTy 0 (.fvar X)) .star := by
  intro c T T' hT hT'
  have hTm := mem_substSizeList_of_getElem? hT
  have hTm' := mem_substSizeList_of_getElem? hT'
  rw [Ty.substSizeList_getElem?] at hT hT'
  obtain ⟨U, hU, rfl⟩ := Option.map_eq_some_iff.mp hT
  obtain ⟨U', hU', rfl⟩ := Option.map_eq_some_iff.mp hT'
  have := ih c U U' hU hU' (by rw [Ty.substSize_substTy]; exact (hS _ hTm).open_fvar X)
    (by rw [Ty.substSize_substTy]; exact (hS' _ hTm').open_fvar X)
  simpa [Ty.substSize_substTy, Ty.substSize] using this

theorem positive_sub {φ : FlexSubst} {Ψ : SizeCtx} {Δ : KCtx} {S' : List Ty}
    (hS' : ∀ T ∈ Ty.substSizeList φ S', SizesWf (Ψ.substBounds φ) 0 T)
    (hpos : ∀ T' ∈ S', EKinding Δ [(.pos, .star)] T' .star) :
    ∀ T' ∈ Ty.substSizeList φ S', Kinding (Ψ.substBounds φ) Δ [(.pos, .star)] 0 T' .star := by
  intro T' hT'
  obtain ⟨U, hU, rfl⟩ := Ty.mem_substSizeList hT'
  exact kinding_of_erase (hpos U hU) (Ty.eraseSz_substSize φ U) (hS' _ hT')

theorem compare_sound {φ : FlexSubst} {Ψ : SizeCtx} {Δ : KCtx} {A B : Ty} {κ : Kind}
    {C : List SConstr} (h : Compare Ψ Δ A B κ C) (hc : Coherent φ C) :
    CompareOK φ Ψ Δ A B κ := by
  refine Compare.rec
    (motive_1 := fun Δ A B κ C _ => Coherent φ C → CompareOK φ Ψ Δ A B κ)
    (motive_2 := fun Δ X S S' C _ => Coherent φ C →
      S.length = S'.length ∧ ∀ (c : Nat) (T T' : Ty), S[c]? = some T → S'[c]? = some T' →
        CompareOK φ Ψ Δ (T.substTy 0 (.fvar X)) (T'.substTy 0 (.fvar X)) .star)
    ?refl ?beta_l ?beta_r ?prod ?arr ?app_pos ?app_neg ?app_mix ?app_top ?lam ?allT ?exT
    ?mu_pos ?mu_eqv ?nu_pos ?nu_eqv ?nil ?cons h hc
  case refl =>
    intro Δ A κ hk _ hA _
    refine .refl (kinding_of_erase hk ?_ hA)
    exact Ty.eraseSz_substSize φ A
  case beta_l =>
    intro Δ F G B ι κ C hk _ ih hcoh hA hB
    have hA' := hA
    simp only [Ty.substSize] at hA ⊢
    cases hA with
    | app hlam hG =>
      cases hlam with
      | lam hF =>
        have hk' : KindingC (Ψ.substBounds φ) Δ
            (.app (.lam ι (F.substSize φ)) (G.substSize φ) ι) κ := by
          refine kinding_of_erase hk ?_ (.app (.lam hF) hG)
          simp [Ty.eraseSz, Ty.eraseSz_substSize]
        refine .beta_l hk' ?_
        have := ih hcoh (by rw [Ty.substSize_substTy]; exact hF.substTy hG) hB
        rwa [Ty.substSize_substTy] at this
  case beta_r =>
    intro Δ F G A ι κ C hk _ ih hcoh hA hB
    simp only [Ty.substSize] at hB ⊢
    cases hB with
    | app hlam hG =>
      cases hlam with
      | lam hF =>
        have hk' : KindingC (Ψ.substBounds φ) Δ
            (.app (.lam ι (F.substSize φ)) (G.substSize φ) ι) κ := by
          refine kinding_of_erase hk ?_ (.app (.lam hF) hG)
          simp [Ty.eraseSz, Ty.eraseSz_substSize]
        refine .beta_r hk' ?_
        have := ih hcoh hA (by rw [Ty.substSize_substTy]; exact hF.substTy hG)
        rwa [Ty.substSize_substTy] at this
  case prod =>
    intro Δ A A' B B' C₁ C₂ _ _ ih₁ ih₂ hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | prod hA hB =>
      cases hR with
      | prod hA' hB' => exact .prod (ih₁ hcoh.left hA hA') (ih₂ hcoh.right hB hB')
  case arr =>
    intro Δ A A' B B' C₁ C₂ _ _ ih₁ ih₂ hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | arr hA hB =>
      cases hR with
      | arr hA' hB' => exact .arr (ih₁ hcoh.left hA' hA) (ih₂ hcoh.right hB hB')
  case app_pos =>
    intro Δ F F' G G' ι κ₁ κ₂ C₁ C₂ _ _ hkG hkG' hι ihF ihG hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | app hF hG =>
      cases hR with
      | app hF' hG' =>
        refine .app (ihF hcoh.left hF hF') (fun _ => ihG hcoh.right hG hG')
          (fun h => absurd h (by simp [Pol.le])) (kinding_of_erase hkG ?_ hG)
          (kinding_of_erase hkG' ?_ hG') hι
        · exact Ty.eraseSz_substSize φ G
        · exact Ty.eraseSz_substSize φ G'
  case app_neg =>
    intro Δ F F' G G' ι κ₁ κ₂ C₁ C₂ _ _ hkG hkG' hι ihF ihG hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | app hF hG =>
      cases hR with
      | app hF' hG' =>
        refine .app (ihF hcoh.left hF hF') (fun h => absurd h (by simp [Pol.le]))
          (fun _ => ihG hcoh.right hG' hG) (kinding_of_erase hkG ?_ hG)
          (kinding_of_erase hkG' ?_ hG') hι
        · exact Ty.eraseSz_substSize φ G
        · exact Ty.eraseSz_substSize φ G'
  case app_mix =>
    intro Δ F F' G G' ι κ₁ κ₂ C₁ C₂ C₃ _ _ _ hkG hkG' hι ihF ihG ihG' hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | app hF hG =>
      cases hR with
      | app hF' hG' =>
        refine .app (ihF hcoh.left.left hF hF') (fun _ => ihG hcoh.left.right hG hG')
          (fun _ => ihG' hcoh.right hG' hG) (kinding_of_erase hkG ?_ hG)
          (kinding_of_erase hkG' ?_ hG') hι
        · exact Ty.eraseSz_substSize φ G
        · exact Ty.eraseSz_substSize φ G'
  case app_top =>
    intro Δ F F' G G' ι κ₁ κ₂ C₁ _ hkG hkG' hι ihF hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | app hF hG =>
      cases hR with
      | app hF' hG' =>
        refine .app (ihF hcoh hF hF') (fun h => absurd h (by simp [Pol.le]))
          (fun h => absurd h (by simp [Pol.le])) (kinding_of_erase hkG ?_ hG)
          (kinding_of_erase hkG' ?_ hG') hι
        · exact Ty.eraseSz_substSize φ G
        · exact Ty.eraseSz_substSize φ G'
  case lam =>
    intro Δ F F' ι ι' π κ₁ κ₂ X C hX _ hk hk' ih hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | lam hF =>
      cases hR with
      | lam hF' =>
        refine .lam hX ?_ (kinding_of_erase hk ?_ (.lam hF)) (kinding_of_erase hk' ?_ (.lam hF'))
        · have := ih hcoh (by rw [Ty.substSize_substTy]; exact hF.open_fvar X)
            (by rw [Ty.substSize_substTy]; exact hF'.open_fvar X)
          simpa [Ty.substSize_substTy, Ty.substSize] using this
        · simp [Ty.eraseSz, Ty.eraseSz_substSize]
        · simp [Ty.eraseSz, Ty.eraseSz_substSize]
  case allT =>
    intro Δ κ B B' X C hX _ hk hk' ih hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | allT hB =>
      cases hR with
      | allT hB' =>
        refine .allT (SubKind.refl κ) hX ?_ (kinding_of_erase hk ?_ (.allT hB))
          (kinding_of_erase hk' ?_ (.allT hB'))
        · have := ih hcoh (by rw [Ty.substSize_substTy]; exact hB.open_fvar X)
            (by rw [Ty.substSize_substTy]; exact hB'.open_fvar X)
          simpa [Ty.substSize_substTy, Ty.substSize] using this
        · simp [Ty.eraseSz, Ty.eraseSz_substSize]
        · simp [Ty.eraseSz, Ty.eraseSz_substSize]
  case exT =>
    intro Δ κ B B' X C hX _ hk hk' ih hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | exT hB =>
      cases hR with
      | exT hB' =>
        refine .exT (SubKind.refl κ) hX ?_ (kinding_of_erase hk ?_ (.exT hB))
          (kinding_of_erase hk' ?_ (.exT hB'))
        · have := ih hcoh (by rw [Ty.substSize_substTy]; exact hB.open_fvar X)
            (by rw [Ty.substSize_substTy]; exact hB'.open_fvar X)
          simpa [Ty.substSize_substTy, Ty.substSize] using this
        · simp [Ty.eraseSz, Ty.eraseSz_substSize]
        · simp [Ty.eraseSz, Ty.eraseSz_substSize]
  case mu_pos =>
    intro Δ a b S S' X C hX hlist hpos hk hk' ihlist hcoh hL hR
    have hhead := hcoh.head
    simp only [SConstr.Holds, Bool.false_eq_true, if_false, if_true] at hhead
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | mu ha hS =>
      cases hR with
      | mu hb hS' =>
        obtain ⟨hlen, hfun⟩ := ihlist hcoh.tail
        refine .mu_pos (Or.inr hhead) (by simp [Ty.substSizeList_length, hlen]) hX
          (functors_sub hS hS' hfun) (positive_sub hS' hpos)
          (kinding_of_erase hk ?_ (.mu ha hS)) (kinding_of_erase hk' ?_ (.mu hb hS'))
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
  case mu_eqv =>
    intro Δ a b S S' X C₁ C₂ hX hlist₁ hlist₂ hk hk' ih₁ ih₂ hcoh hL hR
    have hhead := hcoh.head
    simp only [SConstr.Holds, Bool.false_eq_true, if_false, if_true] at hhead
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | mu ha hS =>
      cases hR with
      | mu hb hS' =>
        obtain ⟨hlen, hfun₁⟩ := ih₁ hcoh.tail.left
        obtain ⟨_, hfun₂⟩ := ih₂ hcoh.tail.right
        refine .mu_eqv (Or.inr hhead) (by simp [Ty.substSizeList_length, hlen]) hX
          (functors_sub hS hS' hfun₁) ?_
          (kinding_of_erase hk ?_ (.mu ha hS)) (kinding_of_erase hk' ?_ (.mu hb hS'))
        · intro c T T' hT hT'
          exact functors_sub hS' hS hfun₂ c T' T hT' hT
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
  case nu_pos =>
    intro Δ a b R R' X C hX hlist hpos hk hk' ihlist hcoh hL hR
    have hhead := hcoh.head
    simp only [SConstr.Holds, Bool.false_eq_true, if_false, if_true] at hhead
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | nu ha hS =>
      cases hR with
      | nu hb hS' =>
        obtain ⟨hlen, hfun⟩ := ihlist hcoh.tail
        refine .nu_pos (Or.inr hhead) (by simp [Ty.substSizeList_length, hlen]) hX
          (functors_sub hS hS' hfun) (positive_sub hS' hpos)
          (kinding_of_erase hk ?_ (.nu ha hS)) (kinding_of_erase hk' ?_ (.nu hb hS'))
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
  case nu_eqv =>
    intro Δ a b R R' X C₁ C₂ hX hlist₁ hlist₂ hk hk' ih₁ ih₂ hcoh hL hR
    have hhead := hcoh.head
    simp only [SConstr.Holds, Bool.false_eq_true, if_false, if_true] at hhead
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | nu ha hS =>
      cases hR with
      | nu hb hS' =>
        obtain ⟨hlen, hfun₁⟩ := ih₁ hcoh.tail.left
        obtain ⟨_, hfun₂⟩ := ih₂ hcoh.tail.right
        refine .nu_eqv (Or.inr hhead) (by simp [Ty.substSizeList_length, hlen]) hX
          (functors_sub hS hS' hfun₁) ?_
          (kinding_of_erase hk ?_ (.nu ha hS)) (kinding_of_erase hk' ?_ (.nu hb hS'))
        · intro c T T' hT hT'
          exact functors_sub hS' hS hfun₂ c T' T hT' hT
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
  case nil =>
    intro Δ X _
    exact ⟨rfl, fun c T T' h _ => by simp at h⟩
  case cons =>
    intro Δ X T T' S S' C₁ C₂ _ _ ihT ihS hcoh
    obtain ⟨hlen, hS⟩ := ihS hcoh.right
    refine ⟨by simp [hlen], ?_⟩
    intro c U U' hU hU'
    cases c with
    | zero =>
      simp at hU hU'
      subst hU; subst hU'
      exact ihT hcoh.left
    | succ c => exact hS c U U' (by simpa using hU) (by simpa using hU')

end NishtAbel2024V5
