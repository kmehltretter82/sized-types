import Solutions.V5.InfSound

/-! # V5 inference: signature encoding (Theorem 7 and Lemma 3) -/

namespace NishtAbel2024V5

/-! ## Theorem 7: Kinding of encoded types -/

mutual

theorem Unsized.eraseSz_eq : ∀ {A : Ty}, Unsized A → A.eraseSz = A
  | _, .unit => rfl
  | _, .prod hA hB => by simp [Ty.eraseSz, hA.eraseSz_eq, hB.eraseSz_eq]
  | _, .arr hA hB => by simp [Ty.eraseSz, hA.eraseSz_eq, hB.eraseSz_eq]
  | _, .var _ => rfl
  | _, .fvar _ => rfl
  | _, .lam hF => by simp [Ty.eraseSz, hF.eraseSz_eq]
  | _, .app hF hG => by simp [Ty.eraseSz, hF.eraseSz_eq, hG.eraseSz_eq]
  | _, .mu hS => by simp [Ty.eraseSz, hS.eraseSzList_eq]
  | _, .nu hR => by simp [Ty.eraseSz, hR.eraseSzList_eq]
  | _, .allT hB => by simp [Ty.eraseSz, hB.eraseSz_eq]
  | _, .exT hB => by simp [Ty.eraseSz, hB.eraseSz_eq]

theorem UnsizedList.eraseSzList_eq : ∀ {S : List Ty}, UnsizedList S → Ty.eraseSzList S = S
  | _, .nil => rfl
  | _, .cons hT hS => by simp [Ty.eraseSzList, hT.eraseSz_eq, hS.eraseSzList_eq]

end

theorem Unsized.ekinding {Δ : KCtx} {Δb : BCtx} {A : Ty} {κ : Kind}
    (h : Unsized A) (hk : Kinding [] Δ Δb 0 A κ) : EKinding Δ Δb A κ := by
  unfold EKinding
  rwa [h.eraseSz_eq]

theorem encode_dom_nodup {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx}
    {G G' : Ty} {Ψ : SizeCtx} (h : Encode πs ok π Δ Δb G Ψ G') : Ψ.dom.Nodup := by
  refine Encode.rec
    (motive_1 := fun _ _ _ _ Ψ _ _ => Ψ.dom.Nodup)
    (motive_2 := fun _ _ _ _ Ψ _ _ => Ψ.dom.Nodup)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · simp [SizeCtx.dom]
  · intro _ _ _ _ _ _ _ Ψ₁ Ψ₂ _ _ hdisj ih₁ ih₂
    simp only [SizeCtx.dom, List.map_append]
    exact List.nodup_append.mpr ⟨ih₁, ih₂, fun x hx y hy hxy => hdisj x hx (hxy ▸ hy)⟩
  · intro _ _ _ _ _ _ _ Ψ₁ Ψ₂ _ _ hdisj ih₁ ih₂
    simp only [SizeCtx.dom, List.map_append]
    exact List.nodup_append.mpr ⟨ih₁, ih₂, fun x hx y hy hxy => hdisj x hx (hxy ▸ hy)⟩
  · intro _ _ _ _; simp [SizeCtx.dom]
  · intro _ _ _ _; simp [SizeCtx.dom]
  · intro _ _ _ _ _ _ _ _ ih; exact ih
  · intro _ _ _ _ _ _ _ _ _ _ _ Ψ₁ Ψ₂ _ _ _ hdisj ih₁ ih₂
    simp only [SizeCtx.dom, List.map_append]
    exact List.nodup_append.mpr ⟨ih₁, ih₂, fun x hx y hy hxy => hdisj x hx (hxy ▸ hy)⟩
  · intro _ _ _ _ _ Ψ i _ _ hi _ ih
    simp only [SizeCtx.dom, List.map_cons]
    exact List.nodup_cons.mpr ⟨hi, ih⟩
  · intro _ _ _ _ _ _ _ _ ih; exact ih
  · intro _ _ _ _ _ Ψ i _ _ hi _ ih
    simp only [SizeCtx.dom, List.map_cons]
    exact List.nodup_cons.mpr ⟨hi, ih⟩
  · intro _ _ _ _ _ _ _ _ ih; exact ih
  · intro _ _ _ _ _ _ _ _ ih; exact ih
  · intro _ _ _ _ _ _ _ _ ih; exact ih
  · simp [SizeCtx.dom]
  · intro _ _ _ _ _ _ _ Ψ₁ Ψ₂ _ _ hdisj ih₁ ih₂
    simp only [SizeCtx.dom, List.map_append]
    exact List.nodup_append.mpr ⟨ih₁, ih₂, fun x hx y hy hxy => hdisj x hx (hxy ▸ hy)⟩

theorem sizeCtxWf_of_nodup_inf {Ψ : SizeCtx} (hn : Ψ.dom.Nodup) (hb : ∀ p ∈ Ψ, p.2 = .inf 0) :
    SizeCtxWf Ψ := by
  induction Ψ using List.reverseRecOn with
  | nil => exact .nil
  | append_singleton Ψ p ih =>
    rcases p with ⟨i, a⟩
    simp only [SizeCtx.dom, List.map_append, List.map_cons, List.map_nil] at hn
    obtain ⟨hnΨ, _, hdisj⟩ := List.nodup_append.mp hn
    have hi : i ∉ SizeCtx.dom Ψ := fun hmem => hdisj i hmem i (by simp) rfl
    have ha : a = .inf 0 := hb (i, a) (by simp)
    subst ha
    exact .snoc (ih hnΨ (fun q hq => hb q (List.mem_append_left _ hq))) hi trivial

theorem encode_sizeCtxWf {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx}
    {G G' : Ty} {Ψ : SizeCtx} (h : Encode πs ok π Δ Δb G Ψ G') : SizeCtxWf Ψ :=
  sizeCtxWf_of_nodup_inf (encode_dom_nodup h) (encode_facts h).2.2.2

/-- **Theorem 7** (Encoding of function signatures, Section 6.1): if `A` has size-erased kind `κ`
and `π; Δ ⊢_SCT^{πs} A ⇒ Ψ; A'`, then `⊢ Ψ` and `Ψ; Δ ⊢ A' : κ`. -/
theorem theorem_7 {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx} {A A' : Ty}
    {Ψ : SizeCtx} {κ : Kind} (hk : EKinding Δ Δb A κ) (henc : Encode πs ok π Δ Δb A Ψ A') :
    SizeCtxWf Ψ ∧ Kinding Ψ Δ Δb 0 A' κ := by
  obtain ⟨herase, hswf, _, _⟩ := encode_facts henc
  exact ⟨encode_sizeCtxWf henc, kinding_of_erase hk herase hswf⟩

theorem EncodedDecl.wf {d d' : FunDecl} (h : EncodedDecl d d') :
    SizeCtxWf d'.sizeParams ∧ KindingC d'.sizeParams [] d'.ty .star :=
  theorem_7 h.2.2.2.2.1 h.2.2.2.2.2

/-! ## Lemma 3: Polarities of encoded size variables -/

def FixKind.other : FixKind → FixKind
  | .mu => .nu
  | .nu => .mu

def FixKind.encPol (πs : Pol) : FixKind → Pol
  | .mu => πs
  | .nu => πs.negate

theorem SizeWfAt.fvars_sub {Ψ : SizeCtx} {m : Nat} :
    ∀ {a : Size}, SizeWfAt Ψ m a → ∀ i ∈ a.fvars, i ∈ Ψ.dom
  | .inf _, _, _, hi => by simp [Size.fvars] at hi
  | .var j _, h, i, hi => by
    simp only [Size.fvars, List.mem_singleton] at hi
    subst hi; exact h
  | .bvar _ _, _, _, hi => by simp [Size.fvars] at hi
  | .meet a b, ⟨ha, hb⟩, i, hi => by
    simp only [Size.fvars, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ha.fvars_sub i hi
    · exact hb.fvars_sub i hi

theorem SizesWf.sizeVars_sub {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A) :
    ∀ i ∈ A.sizeVars, i ∈ Ψ.dom := by
  induction h with
  | unit | var | fvar => intro i hi; simp [Ty.sizeVars] at hi
  | prod _ _ ihA ihB | arr _ _ ihA ihB | app _ _ ihA ihB =>
    intro i hi
    simp only [Ty.sizeVars, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ihA i hi
    · exact ihB i hi
  | lam _ ih | allT _ ih | exT _ ih =>
    intro i hi; exact ih i hi
  | allS ha _ ih | exS ha _ ih =>
    intro i hi
    simp only [Ty.sizeVars, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ha.fvars_sub i hi
    · exact ih i hi
  | @mu _ a S ha hS ih =>
    intro i hi
    simp only [Ty.sizeVars, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ha.fvars_sub i hi
    · clear ha hS
      induction S with
      | nil => simp [Ty.sizeVarsList] at hi
      | cons T S ihS =>
        simp only [Ty.sizeVarsList, List.mem_append] at hi
        rcases hi with hi | hi
        · exact ih T (by simp) i hi
        · exact ihS (fun U hU => ih U (by simp [hU])) hi
  | @nu _ a R ha hR ih =>
    intro i hi
    simp only [Ty.sizeVars, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ha.fvars_sub i hi
    · clear ha hR
      induction R with
      | nil => simp [Ty.sizeVarsList] at hi
      | cons T R ihR =>
        simp only [Ty.sizeVarsList, List.mem_append] at hi
        rcases hi with hi | hi
        · exact ih T (by simp) i hi
        · exact ihR (fun U hU => ih U (by simp [hU])) hi

theorem encode_sizeVars_sub {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx}
    {G G' : Ty} {Ψ : SizeCtx} (h : Encode πs ok π Δ Δb G Ψ G') :
    ∀ i ∈ G'.sizeVars, i ∈ Ψ.dom :=
  (encode_facts h).2.1.sizeVars_sub

theorem encodeList_sizeVars_sub {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx}
    {S S' : List Ty} {Ψ : SizeCtx} (h : EncodeList πs ok π Δ Δb S Ψ S') :
    ∀ i ∈ Ty.sizeVarsList S', i ∈ Ψ.dom := by
  induction S' generalizing S Ψ with
  | nil => intro i hi; simp [Ty.sizeVarsList] at hi
  | cons T' S' ih =>
    cases h with
    | cons hT hS _ =>
      intro i hi
      simp only [Ty.sizeVarsList, List.mem_append, SizeCtx.dom, List.map_append] at hi ⊢
      rcases hi with hi | hi
      · exact Or.inl (encode_sizeVars_sub hT i hi)
      · exact Or.inr (ih hS i hi)

theorem mem_sizeVarsList_of_mem {S : List Ty} {T : Ty} (hT : T ∈ S) {i : Nat}
    (hi : i ∈ T.sizeVars) : i ∈ Ty.sizeVarsList S := by
  induction S with
  | nil => simp at hT
  | cons A S ih =>
    simp only [Ty.sizeVarsList, List.mem_append]
    rcases List.mem_cons.mp hT with rfl | hT
    · exact Or.inl hi
    · exact Or.inr (ih hT)

theorem SizeOcc.mem_sizeVars {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol} {A : Ty}
    (h : SizeOcc fk i Δ Δb π A) : i ∈ A.sizeVars := by
  induction h with
  | prodL _ ih | arrL _ ih | appF _ ih =>
    simp only [Ty.sizeVars, List.mem_append]; exact Or.inl ih
  | prodR _ ih | arrR _ ih | appG _ _ ih =>
    simp only [Ty.sizeVars, List.mem_append]; exact Or.inr ih
  | lam _ ih | allT _ ih | exT _ ih => exact ih
  | allS _ ih | exS _ ih =>
    simp only [Ty.sizeVars, List.mem_append]; exact Or.inr ih
  | mu_here _ hi | nu_here _ hi =>
    simp only [Ty.sizeVars, List.mem_append]; exact Or.inl hi
  | mu_body hT _ ih | nu_body hT _ ih =>
    simp only [Ty.sizeVars, List.mem_append]
    exact Or.inr (mem_sizeVarsList_of_mem hT ih)

mutual

theorem Ty.indexes_mem_sizeVars {fk : FixKind} {i : Nat} :
    ∀ (A : Ty), A.indexes fk i = true → i ∈ A.sizeVars
  | .unit, h => by simp [Ty.indexes] at h
  | .var _, h => by simp [Ty.indexes] at h
  | .fvar _, h => by simp [Ty.indexes] at h
  | .prod A B, h => by
    simp only [Ty.indexes, Bool.or_eq_true] at h
    simp only [Ty.sizeVars, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Ty.indexes_mem_sizeVars A h)
    · exact Or.inr (Ty.indexes_mem_sizeVars B h)
  | .arr A B, h => by
    simp only [Ty.indexes, Bool.or_eq_true] at h
    simp only [Ty.sizeVars, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Ty.indexes_mem_sizeVars A h)
    · exact Or.inr (Ty.indexes_mem_sizeVars B h)
  | .app A B _, h => by
    simp only [Ty.indexes, Bool.or_eq_true] at h
    simp only [Ty.sizeVars, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Ty.indexes_mem_sizeVars A h)
    · exact Or.inr (Ty.indexes_mem_sizeVars B h)
  | .lam _ F, h => Ty.indexes_mem_sizeVars F h
  | .allT _ F, h => Ty.indexes_mem_sizeVars F h
  | .exT _ F, h => Ty.indexes_mem_sizeVars F h
  | .allS _ B, h => by
    simp only [Ty.sizeVars, List.mem_append]
    exact Or.inr (Ty.indexes_mem_sizeVars B h)
  | .exS _ B, h => by
    simp only [Ty.sizeVars, List.mem_append]
    exact Or.inr (Ty.indexes_mem_sizeVars B h)
  | .mu _ S, h => by
    simp only [Ty.indexes, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h
    simp only [Ty.sizeVars, List.mem_append]
    rcases h with ⟨_, hi⟩ | h
    · exact Or.inl hi
    · exact Or.inr (Ty.indexesList_mem_sizeVarsList S h)
  | .nu _ S, h => by
    simp only [Ty.indexes, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h
    simp only [Ty.sizeVars, List.mem_append]
    rcases h with ⟨_, hi⟩ | h
    · exact Or.inl hi
    · exact Or.inr (Ty.indexesList_mem_sizeVarsList S h)

theorem Ty.indexesList_mem_sizeVarsList {fk : FixKind} {i : Nat} :
    ∀ (S : List Ty), Ty.indexesList fk i S = true → i ∈ Ty.sizeVarsList S
  | [], h => by simp [Ty.indexesList] at h
  | A :: S, h => by
    simp only [Ty.indexesList, Bool.or_eq_true] at h
    simp only [Ty.sizeVarsList, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Ty.indexes_mem_sizeVars A h)
    · exact Or.inr (Ty.indexesList_mem_sizeVarsList S h)

end

theorem Ty.indexes_eq_false_of_not_mem {fk : FixKind} {i : Nat} {A : Ty}
    (h : i ∉ A.sizeVars) : A.indexes fk i = false := by
  cases hidx : A.indexes fk i with
  | false => rfl
  | true => exact False.elim (h (Ty.indexes_mem_sizeVars A hidx))

theorem Ty.indexesList_eq_false_of_not_mem {fk : FixKind} {i : Nat} {S : List Ty}
    (h : i ∉ Ty.sizeVarsList S) : Ty.indexesList fk i S = false := by
  cases hidx : Ty.indexesList fk i S with
  | false => rfl
  | true => exact False.elim (h (Ty.indexesList_mem_sizeVarsList S hidx))

def EncodeOccInv (πs π : Pol) (Δ : KCtx) (Δb : BCtx) (Ψ : SizeCtx) (A' : Ty) : Prop :=
  ∀ i ∈ Ψ.dom, ∃ fk q,
    (q = .pos ∨ q = .neg) ∧
    Pol.comp π q = fk.encPol πs ∧
    SizeOcc fk i Δ Δb q A' ∧
    A'.indexes fk i = true ∧
    A'.indexes fk.other i = false ∧
    (∀ Δ' Δb' q', ¬ SizeOcc fk.other i Δ' Δb' q' A')

def EncodeListOccInv (πs π : Pol) (Δ : KCtx) (Δb : BCtx) (Ψ : SizeCtx) (S' : List Ty) : Prop :=
  ∀ i ∈ Ψ.dom, ∃ fk q,
    (q = .pos ∨ q = .neg) ∧
    Pol.comp π q = fk.encPol πs ∧
    (∃ T' ∈ S', SizeOcc fk i Δ Δb q T') ∧
    Ty.indexesList fk i S' = true ∧
    Ty.indexesList fk.other i S' = false ∧
    (∀ T' ∈ S', ∀ Δ' Δb' q', ¬ SizeOcc fk.other i Δ' Δb' q' T')

theorem encode_occ_inv {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx}
    {A A' : Ty} {Ψ : SizeCtx} (h : Encode πs ok π Δ Δb A Ψ A') (hπs : πs = .pos ∨ πs = .neg) :
    EncodeOccInv πs π Δ Δb Ψ A' := by
  refine Encode.rec
    (motive_1 := fun π Δ Δb _ Ψ A' _ => EncodeOccInv πs π Δ Δb Ψ A')
    (motive_2 := fun π Δ Δb _ Ψ S' _ => EncodeListOccInv πs π Δ Δb Ψ S')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro _ _ _ i hi; simp [SizeCtx.dom] at hi
  · intro π Δ Δb A B A' B' Ψ₁ Ψ₂ hA hB hdisj ihA ihB i hi
    simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
    rcases hi with hi | hi
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihA i hi
      have hnotB : i ∉ B'.sizeVars := fun hm => hdisj i hi (encode_sizeVars_sub hB i hm)
      refine ⟨fk, q, hq, hcomp, .prodL hocc, ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, hno_idx, Ty.indexes_eq_false_of_not_mem hnotB]
      · intro Δ' Δb' q' ho
        cases ho with
        | prodL ho => exact hno_occ Δ' Δb' q' ho
        | prodR ho => exact hnotB ho.mem_sizeVars
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihB i hi
      have hnotA : i ∉ A'.sizeVars :=
        fun hm => hdisj i (encode_sizeVars_sub hA i hm) hi
      refine ⟨fk, q, hq, hcomp, .prodR hocc, ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, hno_idx, Ty.indexes_eq_false_of_not_mem hnotA]
      · intro Δ' Δb' q' ho
        cases ho with
        | prodL ho => exact hnotA ho.mem_sizeVars
        | prodR ho => exact hno_occ Δ' Δb' q' ho
  · intro π Δ Δb A B A' B' Ψ₁ Ψ₂ hA hB hdisj ihA ihB i hi
    simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
    rcases hi with hi | hi
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihA i hi
      have hnotB : i ∉ B'.sizeVars := fun hm => hdisj i hi (encode_sizeVars_sub hB i hm)
      have hq' : q.negate = .pos ∨ q.negate = .neg := by cases q <;> simp_all [Pol.negate]
      have hq_neg : q.negate.negate = q := by rcases hq with rfl | rfl <;> rfl
      have hcomp' : Pol.comp π q.negate = fk.encPol πs := by
        rcases hq with rfl | rfl <;> cases π <;> simpa [Pol.comp, Pol.negate] using hcomp
      refine ⟨fk, q.negate, hq', hcomp', .arrL (hq_neg.symm ▸ hocc), ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, hno_idx, Ty.indexes_eq_false_of_not_mem hnotB]
      · intro Δ' Δb' q' ho
        cases ho with
        | arrL ho => exact hno_occ Δ' Δb' q'.negate ho
        | arrR ho => exact hnotB ho.mem_sizeVars
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihB i hi
      have hnotA : i ∉ A'.sizeVars :=
        fun hm => hdisj i (encode_sizeVars_sub hA i hm) hi
      refine ⟨fk, q, hq, hcomp, .arrR hocc, ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, hno_idx, Ty.indexes_eq_false_of_not_mem hnotA]
      · intro Δ' Δb' q' ho
        cases ho with
        | arrL ho => exact hnotA ho.mem_sizeVars
        | arrR ho => exact hno_occ Δ' Δb' q' ho
  · intro _ _ _ _ i hi; simp [SizeCtx.dom] at hi
  · intro _ _ _ _ i hi; simp [SizeCtx.dom] at hi
  · intro π Δ Δb ι F F' Ψ _ ih i hi
    obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ih i hi
    refine ⟨fk, q, hq, hcomp, .lam hocc, hidx, hno_idx, ?_⟩
    intro Δ' Δb' q' ho
    cases ho with
    | lam ho => exact hno_occ _ _ _ ho
  · intro π π' Δ Δb F G F' G' ι κ₁ κ₂ Ψ₁ Ψ₂ hkF hF hG hdisj ihF ihG i hi
    simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
    rcases hi with hi | hi
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihF i hi
      have hnotG : i ∉ G'.sizeVars := fun hm => hdisj i hi (encode_sizeVars_sub hG i hm)
      refine ⟨fk, q, hq, hcomp, .appF hocc, ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, hno_idx, Ty.indexes_eq_false_of_not_mem hnotG]
      · intro Δ' Δb' q' ho
        cases ho with
        | appF ho => exact hno_occ _ _ _ ho
        | appG _ ho => exact hnotG ho.mem_sizeVars
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihG i hi
      have hnotF : i ∉ F'.sizeVars :=
        fun hm => hdisj i (encode_sizeVars_sub hF i hm) hi
      have hekF' : EKinding Δ Δb F' (.arr π' κ₁ κ₂) := by
        unfold EKinding
        rw [(encode_facts hF).1]
        exact hkF.erase
      have htarget : fk.encPol πs = .pos ∨ fk.encPol πs = .neg := by
        cases fk <;> rcases hπs with rfl | rfl <;> simp [FixKind.encPol, Pol.negate]
      have hπ' : π' = .pos ∨ π' = .neg := by
        cases π' <;> cases π <;> rcases hq with rfl | rfl <;>
          rcases htarget with ht | ht <;> simp_all [Pol.comp]
      have hq' : Pol.comp π' q = .pos ∨ Pol.comp π' q = .neg := by
        rcases hπ' with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [Pol.comp, Pol.negate]
      have hcomp' : Pol.comp π (Pol.comp π' q) = fk.encPol πs := by
        rcases hπ' with rfl | rfl <;> rcases hq with rfl | rfl <;> cases π <;>
          simpa [Pol.comp, Pol.negate] using hcomp
      have hinv : Pol.comp π' (Pol.comp π' q) = q := by
        rcases hπ' with rfl | rfl <;> rcases hq with rfl | rfl <;> rfl
      refine ⟨fk, Pol.comp π' q, hq', hcomp', .appG hekF' (hinv.symm ▸ hocc), ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, hno_idx, Ty.indexes_eq_false_of_not_mem hnotF]
      · intro Δ' Δb' q' ho
        cases ho with
        | appF ho => exact hnotF ho.mem_sizeVars
        | appG _ ho => exact hno_occ _ _ _ ho
  · intro π Δ Δb S S' Ψ j hπ _ hj hS ih i hi
    simp only [SizeCtx.dom, List.map_cons, List.mem_cons] at hi
    rcases hi with rfl | hi
    · have hnotS : i ∉ Ty.sizeVarsList S' := fun hm => hj (encodeList_sizeVars_sub hS i hm)
      have hcomp : Pol.comp π .pos = FixKind.encPol πs .mu := by
        subst hπ; rcases hπs with rfl | rfl <;> rfl
      refine ⟨.mu, .pos, Or.inl rfl, hcomp, .mu_here rfl (by simp [Size.fvars]), ?_, ?_, ?_⟩
      · simp [Ty.indexes, Size.fvars]
      · simp [FixKind.other, Ty.indexes, Ty.indexesList_eq_false_of_not_mem hnotS]
      · intro Δ' Δb' q' ho
        cases ho with
        | mu_here hfk => cases hfk
        | mu_body hT ho => exact hnotS (mem_sizeVarsList_of_mem hT ho.mem_sizeVars)
    · obtain ⟨fk, q, hq, hcomp, ⟨T', hT', hocc⟩, hidx, hno_idx, hno_occ⟩ := ih i hi
      have hij : i ≠ j := fun heq => hj (heq ▸ hi)
      refine ⟨fk, q, hq, hcomp, .mu_body hT' hocc, ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, Size.fvars, hij, hno_idx]
      · intro Δ' Δb' q' ho
        cases ho with
        | mu_here _ hmem =>
          simp [Size.fvars] at hmem
          exact hij hmem
        | mu_body hT ho => exact hno_occ _ hT _ _ _ ho
  · intro π Δ Δb S S' Ψ _ _ ih i hi
    obtain ⟨fk, q, hq, hcomp, ⟨T', hT', hocc⟩, hidx, hno_idx, hno_occ⟩ := ih i hi
    refine ⟨fk, q, hq, hcomp, .mu_body hT' hocc, ?_, ?_, ?_⟩
    · simp [Ty.indexes, hidx]
    · simp [Ty.indexes, Size.fvars, hno_idx]
    · intro Δ' Δb' q' ho
      cases ho with
      | mu_here _ hmem => simp [Size.fvars] at hmem
      | mu_body hT ho => exact hno_occ _ hT _ _ _ ho
  · intro π Δ Δb R R' Ψ j hπ _ hj hR ih i hi
    simp only [SizeCtx.dom, List.map_cons, List.mem_cons] at hi
    rcases hi with rfl | hi
    · have hnotR : i ∉ Ty.sizeVarsList R' := fun hm => hj (encodeList_sizeVars_sub hR i hm)
      have hcomp : Pol.comp π .pos = FixKind.encPol πs .nu := by
        subst hπ; rcases hπs with rfl | rfl <;> rfl
      refine ⟨.nu, .pos, Or.inl rfl, hcomp, .nu_here rfl (by simp [Size.fvars]), ?_, ?_, ?_⟩
      · simp [Ty.indexes, Size.fvars]
      · simp [FixKind.other, Ty.indexes, Ty.indexesList_eq_false_of_not_mem hnotR]
      · intro Δ' Δb' q' ho
        cases ho with
        | nu_here hfk => cases hfk
        | nu_body hT ho => exact hnotR (mem_sizeVarsList_of_mem hT ho.mem_sizeVars)
    · obtain ⟨fk, q, hq, hcomp, ⟨T', hT', hocc⟩, hidx, hno_idx, hno_occ⟩ := ih i hi
      have hij : i ≠ j := fun heq => hj (heq ▸ hi)
      refine ⟨fk, q, hq, hcomp, .nu_body hT' hocc, ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, Size.fvars, hij, hno_idx]
      · intro Δ' Δb' q' ho
        cases ho with
        | nu_here _ hmem =>
          simp [Size.fvars] at hmem
          exact hij hmem
        | nu_body hT ho => exact hno_occ _ hT _ _ _ ho
  · intro π Δ Δb R R' Ψ _ _ ih i hi
    obtain ⟨fk, q, hq, hcomp, ⟨T', hT', hocc⟩, hidx, hno_idx, hno_occ⟩ := ih i hi
    refine ⟨fk, q, hq, hcomp, .nu_body hT' hocc, ?_, ?_, ?_⟩
    · simp [Ty.indexes, hidx]
    · simp [Ty.indexes, Size.fvars, hno_idx]
    · intro Δ' Δb' q' ho
      cases ho with
      | nu_here _ hmem => simp [Size.fvars] at hmem
      | nu_body hT ho => exact hno_occ _ hT _ _ _ ho
  · intro π Δ Δb κ B B' Ψ _ ih i hi
    obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ih i hi
    refine ⟨fk, q, hq, hcomp, .allT hocc, hidx, hno_idx, ?_⟩
    intro Δ' Δb' q' ho
    cases ho with
    | allT ho => exact hno_occ _ _ _ ho
  · intro π Δ Δb κ B B' Ψ _ ih i hi
    obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ih i hi
    refine ⟨fk, q, hq, hcomp, .exT hocc, hidx, hno_idx, ?_⟩
    intro Δ' Δb' q' ho
    cases ho with
    | exT ho => exact hno_occ _ _ _ ho
  · intro _ _ _ i hi; simp [SizeCtx.dom] at hi
  · intro π Δ Δb T T' S S' Ψ₁ Ψ₂ hT hS hdisj ihT ihS i hi
    simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
    rcases hi with hi | hi
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihT i hi
      have hnotS : i ∉ Ty.sizeVarsList S' := fun hm => hdisj i hi (encodeList_sizeVars_sub hS i hm)
      refine ⟨fk, q, hq, hcomp, ⟨T', by simp, hocc⟩, ?_, ?_, ?_⟩
      · simp [Ty.indexesList, hidx]
      · simp [Ty.indexesList, hno_idx, Ty.indexesList_eq_false_of_not_mem hnotS]
      · intro U hU Δ' Δb' q' ho
        rcases List.mem_cons.mp hU with rfl | hU
        · exact hno_occ _ _ _ ho
        · exact hnotS (mem_sizeVarsList_of_mem hU ho.mem_sizeVars)
    · obtain ⟨fk, q, hq, hcomp, ⟨U, hU, hocc⟩, hidx, hno_idx, hno_occ⟩ := ihS i hi
      have hnotT : i ∉ T'.sizeVars :=
        fun hm => hdisj i (encode_sizeVars_sub hT i hm) hi
      refine ⟨fk, q, hq, hcomp, ⟨U, by simp [hU], hocc⟩, ?_, ?_, ?_⟩
      · simp [Ty.indexesList, hidx]
      · simp [Ty.indexesList, hno_idx, Ty.indexes_eq_false_of_not_mem hnotT]
      · intro U' hU' Δ' Δb' q' ho
        rcases List.mem_cons.mp hU' with rfl | hU'
        · exact hnotT ho.mem_sizeVars
        · exact hno_occ U' hU' _ _ _ ho

/-- **Lemma 3** (Polarities of encoded size variables, Section 6.1, p. 43): if
`+; Δ ⊢_SCT^− A ⇒ Ψ; A'`, then every `i ∈ Ψ.dom` either occurs negatively as a `μ`-index in `A'`
(with `paramPol A' i = .pos` and no `ν`-occurrence) or occurs positively as a `ν`-index in `A'`
(with `paramPol A' i = .neg` and no `μ`-occurrence). -/
theorem lemma_3 {ok : Nat → Prop} {Δ : KCtx} {Δb : BCtx} {A A' : Ty} {Ψ : SizeCtx}
    (henc : Encode .neg ok .pos Δ Δb A Ψ A') :
    ∀ i ∈ Ψ.dom,
      (SizeOcc .mu i Δ Δb .neg A' ∧ paramPol A' i = .pos ∧
        (∀ Δ' Δb' q, ¬ SizeOcc .nu i Δ' Δb' q A')) ∨
      (SizeOcc .nu i Δ Δb .pos A' ∧ paramPol A' i = .neg ∧
        (∀ Δ' Δb' q, ¬ SizeOcc .mu i Δ' Δb' q A')) := by
  intro i hi
  obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := encode_occ_inv henc (Or.inr rfl) i hi
  cases fk with
  | mu =>
    have hq_eq : q = .neg := by rcases hq with rfl | rfl <;> simp_all [Pol.comp, FixKind.encPol]
    subst hq_eq
    exact Or.inl ⟨hocc, by simp [paramPol, hidx], hno_occ⟩
  | nu =>
    have hq_eq : q = .pos := by
      rcases hq with rfl | rfl <;> simp_all [Pol.comp, FixKind.encPol, Pol.negate]
    subst hq_eq
    have hmu_false : A'.indexes .mu i = false := hno_idx
    exact Or.inr ⟨hocc, by simp [paramPol, hmu_false, hidx], hno_occ⟩

end NishtAbel2024V5
