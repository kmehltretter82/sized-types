import Solutions.V5.SubSound

/-! # V5: semantic contexts and pattern matching soundness -/

namespace NishtAbel2024V5

/-- Free type variables of a typing context denote good values of their kinds. -/
def TEnvOK (W : World) (Θ : TyCtx) (θ : TEnv) : Prop := TRel W Θ.toK θ θ

/-- `σ ∈ ⟦Γ⟧ρθ`: every variable of `Γ` is bound by `σ` to a member of its type, and all values of
`σ` are closed. -/
def SemCtx (W : World) (ρ : SizeVal) (θ : TEnv) (Γ : TermCtx) (σ : TmSubst) : Prop :=
  (∀ x A, Γ.lookup x = some A →
    ∃ v, σ.lookup x = some v ∧ v ∈ interpT W ρ θ A SzEnv.zero Env.empty) ∧
  (∀ x v, σ.lookup x = some v → v.Closed)

/-- Every type in the context is well-kinded. -/
def TermCtxWf (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) : Prop :=
  ∀ p ∈ Γ, KindingC Ψ Θ.toK p.2 .star

theorem interp_cand_closed {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Θ : TyCtx} {A : Ty}
    (hA : KindingC Ψ Θ.toK A .star) (ρ : SizeVal) {θ : TEnv} (hθ : TEnvOK W Θ θ) :
    Cand W (interpT W ρ θ A SzEnv.zero Env.empty) :=
  (kinding_sound hW hA ρ θ θ SzEnv.zero Env.empty Env.empty hθ
    (fun _ _ _ hk => by simp at hk)).1

theorem interp_closed_mem {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Θ : TyCtx} {A : Ty}
    (hA : KindingC Ψ Θ.toK A .star) (ρ : SizeVal) {θ : TEnv} (hθ : TEnvOK W Θ θ) {v : Tm}
    (hv : v ∈ interpT W ρ θ A SzEnv.zero Env.empty) : SNc W v :=
  (interp_cand_closed hW hA ρ hθ).sn v hv

/-! ## Kinding facts for typing contexts -/

theorem KindingC.mono_append {Ψ Ψ' : SizeCtx} {Δ Δ' : KCtx} {A : Ty} {κ : Kind}
    (h : KindingC Ψ Δ A κ) : KindingC (Ψ ++ Ψ') (Δ ++ Δ') A κ :=
  h.mono dom_append_left (fun _ _ h => lookup_append_left h)

theorem KindingC.mono_append_sz {Ψ Ψ' : SizeCtx} {Δ : KCtx} {A : Ty} {κ : Kind}
    (h : KindingC Ψ Δ A κ) : KindingC (Ψ ++ Ψ') Δ A κ :=
  h.mono dom_append_left (fun _ _ h => h)

theorem KindingC.mono_append_ty {Ψ : SizeCtx} {Δ Δ' : KCtx} {A : Ty} {κ : Kind}
    (h : KindingC Ψ Δ A κ) : KindingC Ψ (Δ ++ Δ') A κ :=
  h.mono (fun _ h => h) (fun _ _ h => lookup_append_left h)

theorem KindingC.unfold_mu {Ψ : SizeCtx} {Δ : KCtx} (hΔ : Δ.AllMix) {a b : Size} {S : List Ty}
    {c : Nat} {Sc : Ty} (hwf : KindingC Ψ Δ (.mu a S) .star) (hc : S[c]? = some Sc)
    (hb : SizeWf Ψ b) : KindingC Ψ Δ (Sc.substTy 0 (.mu b S)) .star := by
  obtain ⟨_, π, hπ, _, hS⟩ := Kinding.inv_mu hwf
  rw [hΔ.inv] at hS
  have hS' : ∀ T ∈ S, Kinding Ψ Δ [(π, .star)] 0 T .star := fun T hT => by simpa using hS T hT
  refine Kinding.open_ty (hS' Sc (List.mem_of_getElem? hc)) hΔ ?_
  exact .mu hπ hb (fun T hT => by rw [hΔ.inv]; simpa using hS' T hT)

theorem KindingC.unfold_nu {Ψ : SizeCtx} {Δ : KCtx} (hΔ : Δ.AllMix) {a b : Size} {R : List Ty}
    {d : Nat} {Rd : Ty} (hwf : KindingC Ψ Δ (.nu a R) .star) (hd : R[d]? = some Rd)
    (hb : SizeWf Ψ b) : KindingC Ψ Δ (Rd.substTy 0 (.nu b R)) .star := by
  obtain ⟨_, π, hπ, _, hR⟩ := Kinding.inv_nu hwf
  rw [hΔ.inv] at hR
  have hR' : ∀ T ∈ R, Kinding Ψ Δ [(π, .star)] 0 T .star := fun T hT => by simpa using hR T hT
  refine Kinding.open_ty (hR' Rd (List.mem_of_getElem? hd)) hΔ ?_
  exact .nu hπ hb (fun T hT => by rw [hΔ.inv]; simpa using hR' T hT)

/-- A fixpoint with its size replaced. -/
theorem KindingC.mu_size {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {S : List Ty}
    (hwf : KindingC Ψ Δ (.mu a S) .star) (hb : SizeWf Ψ b) : KindingC Ψ Δ (.mu b S) .star := by
  obtain ⟨_, π, hπ, _, hS⟩ := Kinding.inv_mu hwf
  exact .mu hπ hb hS

theorem KindingC.nu_size {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {R : List Ty}
    (hwf : KindingC Ψ Δ (.nu a R) .star) (hb : SizeWf Ψ b) : KindingC Ψ Δ (.nu b R) .star := by
  obtain ⟨_, π, hπ, _, hR⟩ := Kinding.inv_nu hwf
  exact .nu hπ hb hR

theorem TyCtx.not_mem_toK {Θ : TyCtx} {X : Nat} (hX : X ∉ Θ.map Prod.fst) : X ∉ Θ.toK.dom := by
  simpa using hX

theorem TyCtx.toK_snoc_lookup {Θ : TyCtx} {X : Nat} (hX : X ∉ Θ.map Prod.fst) (κ : Kind) :
    (Θ ++ [(X, κ)]).toK.lookup X = some (.mix, κ) := by
  rw [TyCtx.toK_append]
  exact KCtx.lookup_snoc_fresh (TyCtx.not_mem_toK hX) _

/-- Opening an existential/universal type binder at a fresh type variable. -/
theorem KindingC.open_fresh_ty {Ψ : SizeCtx} {Θ : TyCtx} {κ : Kind} {B : Ty}
    (hB : Kinding Ψ Θ.toK [(.mix, κ)] 0 B .star) {X : Nat} (hX : X ∉ Θ.map Prod.fst) :
    KindingC Ψ (Θ ++ [(X, κ)]).toK (B.substTy 0 (.fvar X)) .star := by
  have hB' : Kinding Ψ (Θ ++ [(X, κ)]).toK [(.mix, κ)] 0 B .star :=
    hB.weaken (fun _ h => h) (fun _ _ h => by rw [TyCtx.toK_append]; exact lookup_append_left h)
      (fun _ _ h => h) le_rfl
  exact Kinding.open_ty hB' (TyCtx.toK_allMix _) (.fvar (TyCtx.toK_snoc_lookup hX κ) trivial)

/-- Opening a size binder at a fresh size variable. -/
theorem KindingC.open_fresh_sz {Ψ : SizeCtx} {Δ : KCtx} {B : Ty} (hB : Kinding Ψ Δ [] 1 B .star)
    (j : Nat) (a : Size) : KindingC (Ψ ++ [(j, a)]) Δ (B.openSz 0 (.var j 0)) .star := by
  have hB' : Kinding (Ψ ++ [(j, a)]) Δ [] 1 B .star :=
    hB.weaken dom_append_left (fun _ _ h => h) (fun _ _ h => h) le_rfl
  exact Kinding.open_sz hB' (sizeWf_fresh_var _ _ _)

/-! ## Type environments -/

theorem TEnvOK.extend {W : World} {Θ : TyCtx} {θ : TEnv} (h : TEnvOK W Θ θ) {X : Nat}
    (hX : X ∉ Θ.map Prod.fst) {κ : Kind} {Y : Sem κ.erase} (hY : Good W κ Y) :
    TEnvOK W (Θ ++ [(X, κ)]) (TEnv.update θ X (PSem.ofSem κ.erase Y)) := by
  unfold TEnvOK
  rw [TyCtx.toK_append]
  exact TRel.extend h (TyCtx.not_mem_toK hX) hY

theorem TEnvOK.agree {W : World} {Θ : TyCtx} {θ θ' : TEnv} (h : TEnvOK W Θ θ)
    (hag : ∀ X ∈ Θ.map Prod.fst, θ' X = θ X) : TEnvOK W Θ θ' :=
  TRel.agree h (fun X hX => hag X (by simpa using hX))

/-! ## Unfolding at fresh variables -/

/-- The payload type of a constructor pattern, opened at a fresh size variable. -/
theorem interp_unfold_mu_fresh {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal}
    {θ : TEnv} {a : Size} {S : List Ty} {c j : Nat} {Sc : Ty} (hwf : TyWf Ψ Θ 0 0 (.mu a S))
    (hj : j ∉ Ψ.dom) (hc : S[c]? = some Sc) (β : Ordinal.{0}) :
    interpT W (SizeVal.update ρ j β) θ (Sc.substTy 0 (.mu (.var j 0) S)) SzEnv.zero Env.empty =
      interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star (MuSet W
        (fun c 𝒳 => interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty))
          β)) Env.empty) := by
  have hcl : c < S.length := (List.getElem?_eq_some_iff.mp hc).1
  have hScEq : S[c] = Sc := (List.getElem?_eq_some_iff.mp hc).2
  have hS : ∀ T ∈ S, TyWf Ψ Θ 1 0 T := by cases hwf with | mu _ h => exact h
  have hag : ∀ i ∈ Ψ.dom, SizeVal.update ρ j β i = ρ i := SizeVal.update_agree hj
  have hwfj : TyWf (Ψ ++ [(j, Size.inf 0)]) Θ 0 0 (.mu (.var j 0) S) :=
    .mu (sizeWf_fresh_var _ _ _)
      (fun T hT => (hS T hT).weaken _ _ _ _ dom_append_left (fun _ h => h) le_rfl le_rfl)
  rw [← hScEq]
  unfold interpT
  rw [interp_unfold_mu hcl hwfj]
  have hval : sizeVal (SizeVal.update ρ j β) SzEnv.zero (.var j 0) = β := by
    simp [sizeVal, SizeVal.update]
  rw [hval]
  have hF : (fun (c : Nat) (𝒳 : Set Tm) => interpAt W (SizeVal.update ρ j β) θ S c SzEnv.zero
        (Env.cons (PSem.ofSem .star 𝒳) Env.empty)) =
      (fun (c : Nat) (𝒳 : Set Tm) =>
        interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty)) := by
    funext c' 𝒳
    exact interpAt_congr (fun c hc => interp_agree (hS _ (List.getElem_mem hc)) _ ρ θ θ _ _ _ _
      hag (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) _) c'
  rw [hF]
  exact interpAt_congr (fun c hc => interp_agree (hS _ (List.getElem_mem hc)) _ ρ θ θ _ _ _ _
    hag (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) _) c

theorem interp_unfold_nu_fresh {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal}
    {θ : TEnv} {a : Size} {R : List Ty} {d j : Nat} {Rd : Ty} (hwf : TyWf Ψ Θ 0 0 (.nu a R))
    (hj : j ∉ Ψ.dom) (hd : R[d]? = some Rd) (β : Ordinal.{0}) :
    interpT W (SizeVal.update ρ j β) θ (Rd.substTy 0 (.nu (.var j 0) R)) SzEnv.zero Env.empty =
      interpAt W ρ θ R d SzEnv.zero (Env.cons (PSem.ofSem .star (NuSet W R.length
        (fun d 𝒳 => interpAt W ρ θ R d SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty))
          β)) Env.empty) := by
  have hdl : d < R.length := (List.getElem?_eq_some_iff.mp hd).1
  have hRd : R[d] = Rd := (List.getElem?_eq_some_iff.mp hd).2
  have hR : ∀ T ∈ R, TyWf Ψ Θ 1 0 T := by cases hwf with | nu _ h => exact h
  have hag : ∀ i ∈ Ψ.dom, SizeVal.update ρ j β i = ρ i := SizeVal.update_agree hj
  have hwfj : TyWf (Ψ ++ [(j, Size.inf 0)]) Θ 0 0 (.nu (.var j 0) R) :=
    .nu (sizeWf_fresh_var _ _ _)
      (fun T hT => (hR T hT).weaken _ _ _ _ dom_append_left (fun _ h => h) le_rfl le_rfl)
  rw [← hRd]
  unfold interpT
  rw [interp_unfold_nu hdl hwfj]
  have hval : sizeVal (SizeVal.update ρ j β) SzEnv.zero (.var j 0) = β := by
    simp [sizeVal, SizeVal.update]
  rw [hval]
  have hG : (fun (d : Nat) (𝒳 : Set Tm) => interpAt W (SizeVal.update ρ j β) θ R d SzEnv.zero
        (Env.cons (PSem.ofSem .star 𝒳) Env.empty)) =
      (fun (d : Nat) (𝒳 : Set Tm) =>
        interpAt W ρ θ R d SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty)) := by
    funext d' 𝒳
    exact interpAt_congr (fun c hc => interp_agree (hR _ (List.getElem_mem hc)) _ ρ θ θ _ _ _ _
      hag (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) _) d'
  rw [hG]
  exact interpAt_congr (fun c hc => interp_agree (hR _ (List.getElem_mem hc)) _ ρ θ θ _ _ _ _
    hag (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) _) d

/-! ## Facts about pattern typing -/

theorem patTy_dom {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
    {Θ' : TyCtx} (h : PatTy Ψ Θ p A Γ Ψ' Θ') : Γ.map Prod.fst = p.vars := by
  induction h with
  | var => rfl
  | unit => rfl
  | pair _ _ ih₁ ih₂ => simp [Pat.vars, ih₁, ih₂]
  | cons _ _ _ ih => simpa [Pat.vars] using ih
  | packT _ _ ih => simpa [Pat.vars] using ih
  | packS _ _ ih => simpa [Pat.vars] using ih

theorem patTy_ctx {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
    {Θ' : TyCtx} (h : PatTy Ψ Θ p A Γ Ψ' Θ') : KindingC Ψ Θ.toK A .star → CtxBoundsWf Ψ →
      TermCtxWf (Ψ ++ Ψ') (Θ ++ Θ') Γ ∧ CtxBoundsWf (Ψ ++ Ψ') := by
  induction h with
  | var Ψ Θ x A =>
    intro hA hb
    refine ⟨?_, by simpa using hb⟩
    intro q hq; simp at hq; subst hq; simpa using hA
  | unit Ψ Θ => intro _ hb; exact ⟨by simp [TermCtxWf], by simpa using hb⟩
  | @pair Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p q A B Γ₁ Γ₂ _ _ ih₁ ih₂ =>
    intro hAB hb
    obtain ⟨_, hA, hB⟩ := Kinding.inv_prod hAB
    obtain ⟨hΓ₁, hb₁⟩ := ih₁ hA hb
    obtain ⟨hΓ₂, hb₂⟩ := ih₂ (by rw [TyCtx.toK_append]; exact KindingC.mono_append hB) hb₁
    refine ⟨?_, by simpa using hb₂⟩
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · have h' := hΓ₁ r hr
      rw [TyCtx.toK_append] at h'
      have h'' : KindingC (Ψ ++ Ψ₁ ++ Ψ₂) (Θ.toK ++ Θ₁.toK ++ Θ₂.toK) r.2 .star :=
        KindingC.mono_append h'
      simpa using h''
    · simpa using hΓ₂ r hr
  | @cons Ψ Ψ' Θ Θ' c j p a S Sc Γ hc hj _ ih =>
    intro hA hb
    obtain ⟨_, _, _, ha, _⟩ := Kinding.inv_mu hA
    have hA' : KindingC (Ψ ++ [(j, a)]) Θ.toK (.mu a S) .star := hA.mono_append_sz
    have hunf := hA'.unfold_mu (TyCtx.toK_allMix Θ) (b := .var j 0) hc (sizeWf_fresh_var _ _ _)
    obtain ⟨hΓ, hb'⟩ := ih hunf (hb.extend ha)
    exact ⟨by simpa using hΓ, by simpa using hb'⟩
  | @packT Ψ Ψ' Θ Θ' X κ p B Γ hX _ ih =>
    intro hA hb
    have hB := (Kinding.inv_exT hA).2
    obtain ⟨hΓ, hb'⟩ := ih (KindingC.open_fresh_ty hB hX) hb
    exact ⟨by simpa using hΓ, hb'⟩
  | @packS Ψ Ψ' Θ Θ' j p a B Γ hj _ ih =>
    intro hA hb
    obtain ⟨_, ha, hB⟩ := Kinding.inv_exS hA
    obtain ⟨hΓ, hb'⟩ := ih (KindingC.open_fresh_sz hB j a) (hb.extend ha)
    exact ⟨by simpa using hΓ, by simpa using hb'⟩

/-! ## Semantic contexts -/

theorem SemCtx.nil (W : World) (ρ : SizeVal) (θ : TEnv) : SemCtx W ρ θ [] [] :=
  ⟨by simp, by simp⟩

theorem lookup_none_of_not_mem {σ : TmSubst} {x : Nat} (h : x ∉ σ.map Prod.fst) :
    σ.lookup x = none := by
  cases hl : σ.lookup x with
  | none => rfl
  | some v => exact absurd (List.mem_map.mpr ⟨(x, v), lookup_mem hl, rfl⟩) h

theorem lookup_none_of_not_mem_ctx {Γ : TermCtx} {x : Nat} (h : Γ.lookup x = none) :
    x ∉ Γ.map Prod.fst := by
  intro hx
  obtain ⟨⟨y, A⟩, hm, rfl⟩ := List.mem_map.mp hx
  induction Γ with
  | nil => simp at hm
  | cons q Γ ih =>
    obtain ⟨z, B⟩ := q
    rw [List.lookup_cons] at h
    by_cases hyz : y = z
    · subst hyz; simp at h
    · have : (y == z) = false := beq_eq_false_iff_ne.mpr hyz
      simp only [this] at h
      rcases List.mem_cons.mp hm with hm | hm
      · simp at hm; exact hyz hm.1
      · exact ih hm h (List.mem_map.mpr ⟨(y, A), hm, rfl⟩)

theorem SemCtx.append {W : World} {ρ : SizeVal} {θ : TEnv} {Γ₁ Γ₂ : TermCtx} {σ₁ σ₂ : TmSubst}
    (h₁ : SemCtx W ρ θ Γ₁ σ₁) (h₂ : SemCtx W ρ θ Γ₂ σ₂)
    (hdom : σ₁.map Prod.fst = Γ₁.map Prod.fst) : SemCtx W ρ θ (Γ₁ ++ Γ₂) (σ₁ ++ σ₂) := by
  refine ⟨?_, ?_⟩
  · intro x A hx
    rw [List.lookup_append] at hx ⊢
    cases hΓ : Γ₁.lookup x with
    | some B =>
      rw [hΓ] at hx; simp at hx; subst hx
      obtain ⟨v, hv, hmem⟩ := h₁.1 x _ hΓ
      exact ⟨v, by simp [hv], hmem⟩
    | none =>
      rw [hΓ] at hx; simp at hx
      have : σ₁.lookup x = none := by
        apply lookup_none_of_not_mem
        rw [hdom]
        exact lookup_none_of_not_mem_ctx hΓ
      obtain ⟨v, hv, hmem⟩ := h₂.1 x _ hx
      exact ⟨v, by simp [this, hv], hmem⟩
  · intro x v hx
    rw [List.lookup_append] at hx
    cases h : σ₁.lookup x with
    | some w => rw [h] at hx; simp at hx; subst hx; exact h₁.2 x _ h
    | none => rw [h] at hx; simp at hx; exact h₂.2 x _ hx

theorem lookup_mem_ctx {Γ : TermCtx} {x : Nat} {A : Ty} (h : Γ.lookup x = some A) :
    (x, A) ∈ Γ := by
  induction Γ with
  | nil => simp at h
  | cons q Γ ih =>
    obtain ⟨y, B⟩ := q
    rw [List.lookup_cons] at h
    by_cases hxy : x = y
    · subst hxy; simp at h; subst h; simp
    · have : (x == y) = false := beq_eq_false_iff_ne.mpr hxy
      simp only [this] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Transport of a semantic context to valuations agreeing on the relevant variables. -/
theorem SemCtx.agree {W : World} {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx}
    (hΓ : TermCtxWf Ψ Θ Γ) {ρ ρ' : SizeVal} {θ θ' : TEnv} (hag : ∀ i ∈ Ψ.dom, ρ i = ρ' i)
    (hagθ : ∀ X ∈ Θ.map Prod.fst, θ X = θ' X) {σ : TmSubst} (h : SemCtx W ρ θ Γ σ) :
    SemCtx W ρ' θ' Γ σ := by
  refine ⟨?_, h.2⟩
  intro x A hx
  obtain ⟨v, hv, hmem⟩ := h.1 x A hx
  refine ⟨v, hv, ?_⟩
  have hA : TyWf Ψ (Θ.map Prod.fst) 0 0 A := by
    have := (hΓ (x, A) (lookup_mem_ctx hx)).tyWf
    simpa using this
  unfold interpT at hmem ⊢
  rwa [← interp_agree hA ρ ρ' θ θ' _ _ _ _ hag hagθ (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _))]

theorem lookup_cons_ty (k x : Nat) (b : Ty) (l : TermCtx) :
    ((k, b) :: l).lookup x = if x = k then some b else l.lookup x := by
  rw [List.lookup_cons]
  by_cases h : x = k
  · subst h; simp
  · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]

/-! ## Pattern matching soundness -/

/-- The conclusion of pattern matching soundness. -/
def PatOK (W : World) (Ψ Ψ' : SizeCtx) (Θ Θ' : TyCtx) (ρ : SizeVal) (θ : TEnv) (Γ : TermCtx)
    (σm : TmSubst) : Prop :=
  ∃ ρ' θ', ValidVal (Ψ ++ Ψ') ρ' ∧ (∀ i ∈ Ψ.dom, ρ' i = ρ i) ∧ TEnvOK W (Θ ++ Θ') θ' ∧
    (∀ X ∈ Θ.map Prod.fst, θ' X = θ X) ∧ SemCtx W ρ' θ' Γ σm

theorem pat_sound {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat}
    {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : TyCtx} (hp : PatTy Ψ Θ p A Γ Ψ' Θ') :
    ∀ (ρ : SizeVal) (θ : TEnv) (v : Tm) (σm : TmSubst), ValidVal Ψ ρ → CtxBoundsWf Ψ →
      TEnvOK W Θ θ → KindingC Ψ Θ.toK A .star →
      v ∈ interpT W ρ θ A SzEnv.zero Env.empty →
      matchPat p v = .yes σm → PatOK W Ψ Ψ' Θ Θ' ρ θ Γ σm := by
  induction hp with
  | var Ψ Θ x A =>
    intro ρ θ v σm hv _ hθ hA hmem hm
    simp [matchPat] at hm; subst hm
    refine ⟨ρ, θ, by simpa using hv, fun _ _ => rfl, by simpa using hθ, fun _ _ => rfl, ?_, ?_⟩
    · intro y B hy
      rw [lookup_cons_ty] at hy
      by_cases hyx : y = x
      · simp [hyx] at hy; subst hy; subst hyx
        exact ⟨v, by simp, hmem⟩
      · simp [hyx] at hy
    · intro y w hy
      rw [lookup_cons_eq] at hy
      by_cases hyx : y = x
      · simp [hyx] at hy; subst hy; exact (interp_closed_mem hW hA ρ hθ hmem).1
      · simp [hyx] at hy
  | unit Ψ Θ =>
    intro ρ θ v σm hv _ hθ _ _ hm
    cases v <;> simp [matchPat] at hm
    subst hm
    exact ⟨ρ, θ, by simpa using hv, fun _ _ => rfl, by simpa using hθ, fun _ _ => rfl,
      SemCtx.nil W ρ θ⟩
  | @pair Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p q A B Γ₁ Γ₂ hp₁ hp₂ ih₁ ih₂ =>
    intro ρ θ v σm hv hb hθ hAB hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i t u
    obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
    obtain ⟨_, hA, hB⟩ := Kinding.inv_prod hAB
    unfold interpT at hmem
    rw [interp_prod_star] at hmem
    obtain ⟨t', u', heq, ht, hu⟩ := introSet_of_intro hmem (by simp [IsIntro])
    cases heq
    obtain ⟨ρ₁, θ₁, hv₁, hag₁, hθ₁, hagθ₁, hs₁⟩ := ih₁ ρ θ t σ₁ hv hb hθ hA ht hm₁
    have hb₁ := (patTy_ctx hp₁ hA hb).2
    have hB₁ : KindingC (Ψ ++ Ψ₁) (Θ ++ Θ₁).toK B .star := by
      rw [TyCtx.toK_append]; exact KindingC.mono_append hB
    have hBw : TyWf Ψ (Θ.map Prod.fst) 0 0 B := by simpa using hB.tyWf
    have hu₁ : u ∈ interpT W ρ₁ θ₁ B SzEnv.zero Env.empty := by
      unfold interpT
      rwa [interp_agree hBw ρ₁ ρ θ₁ θ _ _ _ _ hag₁ hagθ₁
        (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))]
    obtain ⟨ρ₂, θ₂, hv₂, hag₂, hθ₂, hagθ₂, hs₂⟩ := ih₂ ρ₁ θ₁ u σ₂ hv₁ hb₁ hθ₁ hB₁ hu₁ hm₂
    refine ⟨ρ₂, θ₂, by simpa using hv₂, ?_, by simpa using hθ₂, ?_, ?_⟩
    · intro i hi
      rw [hag₂ i (dom_append_left i hi), hag₁ i hi]
    · intro X hX
      rw [hagθ₂ X (by simp only [List.map_append]; exact mem_append_left' X hX), hagθ₁ X hX]
    · have hΓ₁ := (patTy_ctx hp₁ hA hb).1
      have hs₁' := hs₁.agree hΓ₁ (fun i hi => (hag₂ i hi).symm)
        (fun X hX => (hagθ₂ X hX).symm)
      apply hs₁'.append hs₂
      rw [(matchPat_facts p t σ₁ hm₁).1, patTy_dom hp₁]
  | @cons Ψ Ψ' Θ Θ' c j p a S Sc Γ hc hj hp' ih =>
    intro ρ θ v σm hv hb hθ hA hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i c' t
    by_cases hcc : c = c'
    · simp [hcc] at hm
      subst hcc
      obtain ⟨_, _, _, ha, _⟩ := Kinding.inv_mu hA
      unfold interpT at hmem
      rw [interp_mu_star, MuSet_eq] at hmem
      obtain ⟨c₀, t₀, β, hβ, heq, ht⟩ := introSet_of_intro hmem (by simp [IsIntro])
      cases heq
      have hv₁ := hv.extend hb hj ha hβ
      have hb₁ := hb.extend (j := j) ha
      have hA' : KindingC (Ψ ++ [(j, a)]) Θ.toK (.mu a S) .star := hA.mono_append_sz
      have hunf := hA'.unfold_mu (TyCtx.toK_allMix Θ) (b := .var j 0) hc
        (sizeWf_fresh_var _ _ _)
      have hAw : TyWf Ψ (Θ.map Prod.fst) 0 0 (.mu a S) := by simpa using hA.tyWf
      have ht' : t ∈ interpT W (SizeVal.update ρ j β) θ (Sc.substTy 0 (.mu (.var j 0) S))
          SzEnv.zero Env.empty := by
        rw [interp_unfold_mu_fresh hAw hj hc β]; exact ht
      obtain ⟨ρ', θ', hv', hag', hθ', hagθ', hs'⟩ := ih _ θ t σm hv₁ hb₁ hθ hunf ht' hm
      refine ⟨ρ', θ', by simpa using hv', ?_, hθ', hagθ', hs'⟩
      intro i hi
      rw [hag' i (dom_append_left i hi), SizeVal.update_agree hj i hi]
    · simp [hcc] at hm
  | @packT Ψ Ψ' Θ Θ' X κ p B Γ hX hp' ih =>
    intro ρ θ v σm hv hb hθ hA hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i t
    have hB := (Kinding.inv_exT hA).2
    have hBw : TyWf Ψ (Θ.map Prod.fst) 1 0 B := by simpa using hB.tyWf
    unfold interpT at hmem
    rw [interp_exT_star] at hmem
    obtain ⟨t₀, Y, heq, hY, ht⟩ := introSet_of_intro hmem (by simp [IsIntro])
    cases heq
    have hθ₁ := hθ.extend hX hY
    have ht' : t ∈ interpT W ρ (TEnv.update θ X (PSem.ofSem κ.erase Y)) (B.substTy 0 (.fvar X))
        SzEnv.zero Env.empty := by
      unfold interpT
      rw [interp_open_fresh_ty hBw hX]; exact ht
    obtain ⟨ρ', θ', hv', hag', hθ', hagθ', hs'⟩ :=
      ih ρ _ t σm hv hb hθ₁ (KindingC.open_fresh_ty hB hX) ht' hm
    refine ⟨ρ', θ', by simpa using hv', hag', by simpa using hθ', ?_, hs'⟩
    intro Y' hY'
    rw [hagθ' Y' (by simp only [List.map_append]; exact mem_append_left' Y' hY'),
      TEnv.update_agree hX Y' hY']
  | @packS Ψ Ψ' Θ Θ' j p a B Γ hj hp' ih =>
    intro ρ θ v σm hv hb hθ hA hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i t
    obtain ⟨_, ha, hB⟩ := Kinding.inv_exS hA
    have hBw : TyWf Ψ (Θ.map Prod.fst) 0 1 B := by simpa using hB.tyWf
    unfold interpT at hmem
    rw [interp_exS_star] at hmem
    obtain ⟨t₀, β, heq, hβ, ht⟩ := introSet_of_intro hmem (by simp [IsIntro])
    cases heq
    have hv₁ := hv.extend hb hj ha hβ
    have hb₁ := hb.extend (j := j) ha
    have ht' : t ∈ interpT W (SizeVal.update ρ j β) θ (B.openSz 0 (.var j 0)) SzEnv.zero
        Env.empty := by
      unfold interpT
      rw [interp_open_fresh_sz hBw hj]; exact ht
    obtain ⟨ρ', θ', hv', hag', hθ', hagθ', hs'⟩ :=
      ih _ θ t σm hv₁ hb₁ hθ (KindingC.open_fresh_sz hB j a) ht' hm
    refine ⟨ρ', θ', by simpa using hv', ?_, hθ', hagθ', hs'⟩
    intro i hi
    rw [hag' i (dom_append_left i hi), SizeVal.update_agree hj i hi]

end NishtAbel2024V5
