import Solutions.V5.Match

/-! # V5: semantic elimination spines and their alignment with copattern typing -/

namespace NishtAbel2024V5

/-- A semantic context: free sizes and type variables with their valuations. -/
structure SCtx where
  Ψ : SizeCtx
  Θ : TyCtx
  ρ : SizeVal
  θ : TEnv

def SCtx.extSz (c : SCtx) (j : Nat) (a : Size) (β : Ordinal.{0}) : SCtx :=
  ⟨c.Ψ ++ [(j, a)], c.Θ, SizeVal.update c.ρ j β, c.θ⟩

def SCtx.extTy (c : SCtx) (X : Nat) (κ : Kind) (Y : Sem κ.erase) : SCtx :=
  ⟨c.Ψ, c.Θ ++ [(X, κ)], c.ρ, TEnv.update c.θ X (PSem.ofSem κ.erase Y)⟩

/-- `⟦T⟧` in a semantic context. -/
noncomputable def SCtx.den (W : World) (c : SCtx) (T : Ty) : Set Tm :=
  interpT W c.ρ c.θ T SzEnv.zero Env.empty

/-- Semantic spines: eliminations valid for a locally closed type. Projections and size
instantiations pick an ordinal below the bound and name it by a fresh size variable; type
instantiations pick a candidate and name it by a fresh type variable. -/
inductive SemSpine (W : World) : SCtx → Ty → List Elim → SCtx → Ty → Prop where
  | nil (c : SCtx) (T : Ty) : SemSpine W c T [] c T
  | term {c c' : SCtx} {T₁ T₂ C : Ty} {s : Tm} {es : List Elim} :
      s ∈ c.den W T₁ → SemSpine W c T₂ es c' C → SemSpine W c (.arr T₁ T₂) (.term s :: es) c' C
  | proj {c c' : SCtx} {a : Size} {R : List Ty} {d j : Nat} {Rd C : Ty} {β : Ordinal.{0}}
      {es : List Elim} :
      R[d]? = some Rd → j ∉ c.Ψ.dom → β < sizeVal c.ρ SzEnv.zero a →
      SemSpine W (c.extSz j a β) (Rd.substTy 0 (.nu (.var j 0) R)) es c' C →
      SemSpine W c (.nu a R) (.proj d :: es) c' C
  | instT {c c' : SCtx} {κ : Kind} {B C : Ty} {X : Nat} {Y : Sem κ.erase} {es : List Elim} :
      X ∉ c.Θ.map Prod.fst → Good W κ Y →
      SemSpine W (c.extTy X κ Y) (B.substTy 0 (.fvar X)) es c' C →
      SemSpine W c (.allT κ B) (.inst :: es) c' C
  | instS {c c' : SCtx} {a : Size} {B C : Ty} {j : Nat} {β : Ordinal.{0}} {es : List Elim} :
      j ∉ c.Ψ.dom → β < sizeVal c.ρ SzEnv.zero a →
      SemSpine W (c.extSz j a β) (B.openSz 0 (.var j 0)) es c' C →
      SemSpine W c (.allS a B) (.inst :: es) c' C

/-- Positions reached by semantic spines satisfy the invariants. -/
def PosOK (W : World) (c : SCtx) (T : Ty) : Prop :=
  ValidVal c.Ψ c.ρ ∧ CtxBoundsWf c.Ψ ∧ TEnvOK W c.Θ c.θ ∧ KindingC c.Ψ c.Θ.toK T .star

theorem PosOK.tyWf {W : World} {c : SCtx} {T : Ty} (h : PosOK W c T) :
    TyWf c.Ψ (c.Θ.map Prod.fst) 0 0 T := by
  simpa using h.2.2.2.tyWf

theorem PosOK.term {W : World} {c : SCtx} {T₁ T₂ : Ty} (h : PosOK W c (.arr T₁ T₂)) :
    PosOK W c T₂ := by
  obtain ⟨hv, hb, hθ, hwf⟩ := h
  exact ⟨hv, hb, hθ, (Kinding.inv_arr hwf).2.2⟩

theorem PosOK.dom {W : World} {c : SCtx} {T₁ T₂ : Ty} (h : PosOK W c (.arr T₁ T₂)) :
    KindingC c.Ψ c.Θ.toK T₁ .star := by
  have := (Kinding.inv_arr h.2.2.2).2.1
  rw [(TyCtx.toK_allMix c.Θ).inv] at this
  simpa using this

theorem PosOK.proj {W : World} {c : SCtx} {a : Size} {R : List Ty} {d j : Nat} {Rd : Ty}
    {β : Ordinal.{0}} (h : PosOK W c (.nu a R)) (hd : R[d]? = some Rd) (hj : j ∉ c.Ψ.dom)
    (hβ : β < sizeVal c.ρ SzEnv.zero a) :
    PosOK W (c.extSz j a β) (Rd.substTy 0 (.nu (.var j 0) R)) := by
  obtain ⟨hv, hb, hθ, hwf⟩ := h
  obtain ⟨_, _, _, ha, _⟩ := Kinding.inv_nu hwf
  refine ⟨hv.extend hb hj ha hβ, hb.extend ha, hθ, ?_⟩
  exact (KindingC.mono_append_sz hwf).unfold_nu (TyCtx.toK_allMix _) hd (sizeWf_fresh_var _ _ _)

theorem PosOK.instT {W : World} {c : SCtx} {κ : Kind} {B : Ty} {X : Nat} {Y : Sem κ.erase}
    (h : PosOK W c (.allT κ B)) (hX : X ∉ c.Θ.map Prod.fst) (hY : Good W κ Y) :
    PosOK W (c.extTy X κ Y) (B.substTy 0 (.fvar X)) := by
  obtain ⟨hv, hb, hθ, hwf⟩ := h
  exact ⟨hv, hb, hθ.extend hX hY, KindingC.open_fresh_ty (Kinding.inv_allT hwf).2 hX⟩

theorem PosOK.instS {W : World} {c : SCtx} {a : Size} {B : Ty} {j : Nat} {β : Ordinal.{0}}
    (h : PosOK W c (.allS a B)) (hj : j ∉ c.Ψ.dom) (hβ : β < sizeVal c.ρ SzEnv.zero a) :
    PosOK W (c.extSz j a β) (B.openSz 0 (.var j 0)) := by
  obtain ⟨hv, hb, hθ, hwf⟩ := h
  obtain ⟨_, ha, hB⟩ := Kinding.inv_allS hwf
  exact ⟨hv.extend hb hj ha hβ, hb.extend ha, hθ, KindingC.open_fresh_sz hB j a⟩

/-- Applying a member of a type to a semantic spine for that type. -/
theorem semSpine_app {W : World} {c c' : SCtx} {T C : Ty} {es : List Elim}
    (hs : SemSpine W c T es c' C) :
    PosOK W c T → ∀ r, r ∈ c.den W T → Tm.appSpine r es ∈ c'.den W C := by
  induction hs with
  | nil => intro _ r hr; exact hr
  | term hsT _ ih =>
    intro hok r hr
    exact ih hok.term _ (hr.2 _ hsT)
  | @proj c c' a R d j Rd C β es hd hj hβ _ ih =>
    intro hok r hr
    apply ih (hok.proj hd hj hβ)
    have hdl : d < R.length := (List.getElem?_eq_some_iff.mp hd).1
    simp only [SCtx.den, SCtx.extSz]
    rw [interp_unfold_nu_fresh hok.tyWf hj hd β]
    simp only [SCtx.den, interpT] at hr
    rw [interp_nu_star, NuSet_eq] at hr
    exact hr.2 β hβ d hdl
  | @instT c c' κ B C X Y es hX hY _ ih =>
    intro hok r hr
    apply ih (hok.instT hX hY)
    have hB : TyWf c.Ψ (c.Θ.map Prod.fst) 1 0 B := by
      simpa using (Kinding.inv_allT hok.2.2.2).2.tyWf
    simp only [SCtx.den, SCtx.extTy, interpT]
    rw [interp_open_fresh_ty hB hX]
    simp only [SCtx.den, interpT] at hr
    rw [interp_allT_star] at hr
    exact hr.2 Y hY
  | @instS c c' a B C j β es hj hβ _ ih =>
    intro hok r hr
    apply ih (hok.instS hj hβ)
    have hB : TyWf c.Ψ (c.Θ.map Prod.fst) 0 1 B := by
      simpa using (Kinding.inv_allS hok.2.2.2).2.2.tyWf
    simp only [SCtx.den, SCtx.extSz, interpT]
    rw [interp_open_fresh_sz hB hj]
    simp only [SCtx.den, interpT] at hr
    rw [interp_allS_star] at hr
    exact hr.2 β hβ

theorem semSpine_split {W : World} :
    ∀ {es₁ es₂ : List Elim} {c c' : SCtx} {T C : Ty},
      SemSpine W c T (es₁ ++ es₂) c' C →
      ∃ cm Tm', SemSpine W c T es₁ cm Tm' ∧ SemSpine W cm Tm' es₂ c' C
  | [], es₂, c, c', T, C, h => ⟨c, T, .nil _ _, h⟩
  | e :: es₁, es₂, c, c', T, C, h => by
    cases h with
    | term hs h' =>
      obtain ⟨cm, Tm', h₁, h₂⟩ := semSpine_split h'
      exact ⟨cm, Tm', .term hs h₁, h₂⟩
    | proj hd hj hβ h' =>
      obtain ⟨cm, Tm', h₁, h₂⟩ := semSpine_split h'
      exact ⟨cm, Tm', .proj hd hj hβ h₁, h₂⟩
    | instT hX hY h' =>
      obtain ⟨cm, Tm', h₁, h₂⟩ := semSpine_split h'
      exact ⟨cm, Tm', .instT hX hY h₁, h₂⟩
    | instS hj hβ h' =>
      obtain ⟨cm, Tm', h₁, h₂⟩ := semSpine_split h'
      exact ⟨cm, Tm', .instS hj hβ h₁, h₂⟩

theorem semSpine_snoc {W : World} {c c' c'' : SCtx} {T C D : Ty} {es es' : List Elim}
    (h₁ : SemSpine W c T es c' C) (h₂ : SemSpine W c' C es' c'' D) :
    SemSpine W c T (es ++ es') c'' D := by
  induction h₁ with
  | nil => exact h₂
  | term hs _ ih => exact .term hs (ih h₂)
  | proj hd hj hβ _ ih => exact .proj hd hj hβ (ih h₂)
  | instT hX hY _ ih => exact .instT hX hY (ih h₂)
  | instS hj hβ _ ih => exact .instS hj hβ (ih h₂)

theorem semSpine_posOK {W : World} {c c' : SCtx} {T C : Ty} {es : List Elim}
    (hs : SemSpine W c T es c' C) : PosOK W c T → PosOK W c' C := by
  induction hs with
  | nil => intro h; exact h
  | term _ _ ih => intro h; exact ih h.term
  | proj hd hj hβ _ ih => intro h; exact ih (h.proj hd hj hβ)
  | instT hX hY _ ih => intro h; exact ih (h.instT hX hY)
  | instS hj hβ _ ih => intro h; exact ih (h.instS hj hβ)

/-- Elimination spines of a semantic spine are closed. -/
theorem semSpine_closed {W : World} (hW : WorldClosed W) {c c' : SCtx} {T C : Ty}
    {es : List Elim} (hs : SemSpine W c T es c' C) : PosOK W c T → ElimsClosed es := by
  induction hs with
  | nil => intro _; rfl
  | @term c c' T₁ T₂ C s es hsT _ ih =>
    intro hok
    have hc := (interp_closed_mem hW hok.dom c.ρ hok.2.2.1 hsT).1
    unfold ElimsClosed at ih ⊢
    simp only [List.flatMap_cons, Elim.fv]
    rw [ih hok.term]
    simpa [Tm.Closed] using hc
  | proj hd hj hβ _ ih =>
    intro hok
    unfold ElimsClosed at ih ⊢
    simp only [List.flatMap_cons, Elim.fv]
    rw [ih (hok.proj hd hj hβ)]
    rfl
  | instT hX hY _ ih =>
    intro hok
    unfold ElimsClosed at ih ⊢
    simp only [List.flatMap_cons, Elim.fv]
    rw [ih (hok.instT hX hY)]
    rfl
  | instS hj hβ _ ih =>
    intro hok
    unfold ElimsClosed at ih ⊢
    simp only [List.flatMap_cons, Elim.fv]
    rw [ih (hok.instS hj hβ)]
    rfl

/-! ## Identity substitutions and commutation -/

theorem Size.subst_nil : ∀ a : Size, a.subst [] = a
  | .inf _ => rfl
  | .var _ _ => rfl
  | .bvar _ _ => rfl
  | .meet a b => by simp only [Size.subst, Size.subst_nil a, Size.subst_nil b]

mutual
theorem Ty.substSize_nil : ∀ A : Ty, A.substSize [] = A
  | .unit => rfl
  | .prod A B => by simp only [Ty.substSize]; rw [Ty.substSize_nil A, Ty.substSize_nil B]
  | .arr A B => by simp only [Ty.substSize]; rw [Ty.substSize_nil A, Ty.substSize_nil B]
  | .var _ => rfl
  | .fvar _ => rfl
  | .lam ι F => by simp only [Ty.substSize]; rw [Ty.substSize_nil F]
  | .app F G ι => by simp only [Ty.substSize]; rw [Ty.substSize_nil F, Ty.substSize_nil G]
  | .mu a S => by simp only [Ty.substSize]; rw [Size.subst_nil, Ty.substSizeList_nil S]
  | .nu a R => by simp only [Ty.substSize]; rw [Size.subst_nil, Ty.substSizeList_nil R]
  | .allT κ B => by simp only [Ty.substSize]; rw [Ty.substSize_nil B]
  | .exT κ B => by simp only [Ty.substSize]; rw [Ty.substSize_nil B]
  | .allS a B => by simp only [Ty.substSize]; rw [Size.subst_nil, Ty.substSize_nil B]
  | .exS a B => by simp only [Ty.substSize]; rw [Size.subst_nil, Ty.substSize_nil B]
theorem Ty.substSizeList_nil : ∀ S : List Ty, Ty.substSizeList [] S = S
  | [] => rfl
  | A :: S => by simp only [Ty.substSizeList]; rw [Ty.substSize_nil A, Ty.substSizeList_nil S]
end

mutual
theorem Ty.substFTy_nil : ∀ A : Ty, A.substFTy [] = A
  | .unit => rfl
  | .prod A B => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil A, Ty.substFTy_nil B]
  | .arr A B => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil A, Ty.substFTy_nil B]
  | .var _ => rfl
  | .fvar _ => rfl
  | .lam ι F => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil F]
  | .app F G ι => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil F, Ty.substFTy_nil G]
  | .mu a S => by simp only [Ty.substFTy]; rw [Ty.substFTyList_nil S]
  | .nu a R => by simp only [Ty.substFTy]; rw [Ty.substFTyList_nil R]
  | .allT κ B => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil B]
  | .exT κ B => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil B]
  | .allS a B => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil B]
  | .exS a B => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil B]
theorem Ty.substFTyList_nil : ∀ S : List Ty, Ty.substFTyList [] S = S
  | [] => rfl
  | A :: S => by simp only [Ty.substFTyList]; rw [Ty.substFTy_nil A, Ty.substFTyList_nil S]
end

/-- Renamings of free type variables: every value is a free type variable. -/
def FVarSubst (τ : List (Nat × Ty)) : Prop := ∀ X T, τ.lookup X = some T → ∃ Y, T = .fvar Y

theorem FVarSubst.closed {τ : List (Nat × Ty)} (h : FVarSubst τ) : ClosedTSubst τ := by
  intro X T hT
  obtain ⟨Y, rfl⟩ := h X T hT
  exact ⟨[], [Y], .fvar (by simp)⟩

/-- Size substitutions whose values are free size variables with offsets. -/
def VarSubst (σ : List (Nat × Size)) : Prop :=
  ∀ i b, σ.lookup i = some b → ∃ j m, b = .var j m

theorem VarSubst.lc {σ : List (Nat × Size)} (h : VarSubst σ) : LCSubst σ := by
  intro i b hb
  obtain ⟨j, m, rfl⟩ := h i b hb
  trivial

mutual
theorem Ty.substSize_substFTy {τ : List (Nat × Ty)} (hτ : FVarSubst τ) (σ : List (Nat × Size)) :
    ∀ A : Ty, (A.substSize σ).substFTy τ = (A.substFTy τ).substSize σ
  | .unit => rfl
  | .prod A B => by
    simp only [Ty.substSize, Ty.substFTy]
    rw [Ty.substSize_substFTy hτ σ A, Ty.substSize_substFTy hτ σ B]
  | .arr A B => by
    simp only [Ty.substSize, Ty.substFTy]
    rw [Ty.substSize_substFTy hτ σ A, Ty.substSize_substFTy hτ σ B]
  | .var _ => rfl
  | .fvar X => by
    simp only [Ty.substSize, Ty.substFTy]
    cases h : τ.lookup X with
    | none => rfl
    | some T => obtain ⟨Y, rfl⟩ := hτ X T h; rfl
  | .lam ι F => by
    simp only [Ty.substSize, Ty.substFTy]
    rw [Ty.substSize_substFTy hτ σ F]
  | .app F G ι => by
    simp only [Ty.substSize, Ty.substFTy]
    rw [Ty.substSize_substFTy hτ σ F, Ty.substSize_substFTy hτ σ G]
  | .mu a S => by
    simp only [Ty.substSize, Ty.substFTy]
    rw [Ty.substSizeList_substFTyList hτ σ S]
  | .nu a R => by
    simp only [Ty.substSize, Ty.substFTy]
    rw [Ty.substSizeList_substFTyList hτ σ R]
  | .allT κ B => by simp only [Ty.substSize, Ty.substFTy]; rw [Ty.substSize_substFTy hτ σ B]
  | .exT κ B => by simp only [Ty.substSize, Ty.substFTy]; rw [Ty.substSize_substFTy hτ σ B]
  | .allS a B => by simp only [Ty.substSize, Ty.substFTy]; rw [Ty.substSize_substFTy hτ σ B]
  | .exS a B => by simp only [Ty.substSize, Ty.substFTy]; rw [Ty.substSize_substFTy hτ σ B]
theorem Ty.substSizeList_substFTyList {τ : List (Nat × Ty)} (hτ : FVarSubst τ)
    (σ : List (Nat × Size)) :
    ∀ S : List Ty, Ty.substFTyList τ (Ty.substSizeList σ S) =
      Ty.substSizeList σ (Ty.substFTyList τ S)
  | [] => rfl
  | A :: S => by
    simp only [Ty.substSizeList, Ty.substFTyList]
    rw [Ty.substSize_substFTy hτ σ A, Ty.substSizeList_substFTyList hτ σ S]
end

/-! ## The renaming invariant -/

/-- A clause-side context `cc` and a spine-side context `cs` related by renamings of sizes and
of type variables that preserve their valuations. -/
structure Renaming (W : World) (cc cs : SCtx) (πS : List (Nat × Size)) (πT : List (Nat × Ty)) :
    Prop where
  varS : VarSubst πS
  targetS : ∀ i b, πS.lookup i = some b → SizeWf cc.Ψ b
  untouchedS : ∀ i ∈ cs.Ψ.dom, πS.lookup i = none → i ∈ cc.Ψ.dom
  valS : ∀ i ∈ cs.Ψ.dom, substVal cc.ρ πS i = cs.ρ i
  varT : ∀ X T, πT.lookup X = some T → ∃ Y, T = .fvar Y ∧ Y ∈ cc.Θ.map Prod.fst
  untouchedT : ∀ X ∈ cs.Θ.map Prod.fst, πT.lookup X = none → X ∈ cc.Θ.map Prod.fst
  valT : ∀ X ∈ cs.Θ.map Prod.fst, substTVal W cc.ρ cc.θ πT X = cs.θ X

theorem Renaming.fvar {W : World} {cc cs : SCtx} {πS : List (Nat × Size)} {πT : List (Nat × Ty)}
    (h : Renaming W cc cs πS πT) : FVarSubst πT := by
  intro X T hT
  obtain ⟨Y, rfl, _⟩ := h.varT X T hT
  exact ⟨Y, rfl⟩

theorem tyVal_fvar (W : World) (ρ : SizeVal) (θ : TEnv) (Y : Nat) (ζ : SzEnv) (η : Env) :
    tyVal W ρ θ (.fvar Y) ζ η = θ Y := rfl

/-- The renamed type denotes the same set. -/
theorem Renaming.den_eq {W : World} {cc cs : SCtx} {πS : List (Nat × Size)}
    {πT : List (Nat × Ty)} (h : Renaming W cc cs πS πT) {T : Ty}
    (hT : TyWf cs.Ψ (cs.Θ.map Prod.fst) 0 0 T) :
    cc.den W ((T.substSize πS).substFTy πT) = cs.den W T := by
  simp only [SCtx.den, interpT]
  have hτ : ∀ X U, πT.lookup X = some U → EnvFree W cc.ρ cc.θ U := by
    intro X U hU
    obtain ⟨Y, rfl, _⟩ := h.varT X U hU
    intro ι ζ ζ' η η'; rfl
  rw [interp_substFTy W cc.ρ cc.θ hτ, interp_substSize W cc.ρ _ h.varS.lc]
  exact interp_agree hT _ _ _ _ _ _ _ _ h.valS h.valT (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _)) _

/-- Enlarging the clause side, with valuations agreeing on the old domains. -/
theorem Renaming.extend_clause {W : World} {cc cs cc' : SCtx} {πS : List (Nat × Size)}
    {πT : List (Nat × Ty)} (h : Renaming W cc cs πS πT) (hdom : ∀ i ∈ cc.Ψ.dom, i ∈ cc'.Ψ.dom)
    (hΘ : ∀ X ∈ cc.Θ.map Prod.fst, X ∈ cc'.Θ.map Prod.fst)
    (hag : ∀ i ∈ cc.Ψ.dom, cc'.ρ i = cc.ρ i)
    (hagθ : ∀ X ∈ cc.Θ.map Prod.fst, cc'.θ X = cc.θ X) : Renaming W cc' cs πS πT := by
  refine ⟨h.varS, fun i b hb => (h.targetS i b hb).weaken hdom le_rfl,
    fun i hi hn => hdom i (h.untouchedS i hi hn), ?_, ?_,
    fun X hX hn => hΘ X (h.untouchedT X hX hn), ?_⟩
  · intro i hi
    rw [← h.valS i hi]
    simp only [substVal]
    cases hl : πS.lookup i with
    | some b =>
      exact sizeVal_agree (fun x hx => hag x hx) (fun _ h => absurd h (Nat.not_lt_zero _))
        (h.targetS i b hl)
    | none => exact hag i (h.untouchedS i hi hl)
  · intro X T hT
    obtain ⟨Y, rfl, hY⟩ := h.varT X T hT
    exact ⟨Y, rfl, hΘ Y hY⟩
  · intro X hX
    rw [← h.valT X hX]
    simp only [substTVal]
    cases hl : πT.lookup X with
    | some T =>
      obtain ⟨Y, rfl, hY⟩ := h.varT X T hl
      simp only [tyVal_fvar]
      exact hagθ Y hY
    | none => exact hagθ X (h.untouchedT X hX hl)

theorem Renaming.refl (W : World) (c : SCtx) : Renaming W c c [] [] :=
  ⟨by intro i b h; simp at h, by intro i b h; simp at h, fun i hi _ => hi,
    fun i _ => by simp [substVal], by intro X T h; simp at h, fun X hX _ => hX,
    fun X _ => by simp [substTVal]⟩

theorem lookup_size_cons (k x : Nat) (b : Size) (l : List (Nat × Size)) :
    ((k, b) :: l).lookup x = if x = k then some b else l.lookup x := by
  rw [List.lookup_cons]
  by_cases h : x = k
  · subst h; simp
  · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]

theorem lookup_ty_cons (k x : Nat) (b : Ty) (l : List (Nat × Ty)) :
    ((k, b) :: l).lookup x = if x = k then some b else l.lookup x := by
  rw [List.lookup_cons]
  by_cases h : x = k
  · subst h; simp
  · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]

theorem mem_dom_extSz {c : SCtx} {j : Nat} {a : Size} {β : Ordinal.{0}} {i : Nat}
    (hi : i ∈ (c.extSz j a β).Ψ.dom) (hij : i ≠ j) : i ∈ c.Ψ.dom := by
  simp only [SCtx.extSz, SizeCtx.dom, List.map_append, List.mem_append, List.map_cons,
    List.map_nil, List.mem_singleton] at hi
  rcases hi with hi | hi
  · exact hi
  · exact absurd hi hij

/-- A fresh size on both sides extends the renaming. -/
theorem Renaming.extSz {W : World} {cc cs : SCtx} {πS : List (Nat × Size)} {πT : List (Nat × Ty)}
    (h : Renaming W cc cs πS πT) {j js : Nat} (hj : j ∉ cc.Ψ.dom) {a as : Size}
    {β : Ordinal.{0}} :
    Renaming W (cc.extSz j a β) (cs.extSz js as β) ((js, .var j 0) :: πS) πT := by
  have hag : ∀ i ∈ cc.Ψ.dom, (cc.extSz j a β).ρ i = cc.ρ i := SizeVal.update_agree hj
  have h' := h.extend_clause (cc' := cc.extSz j a β) dom_append_left (fun _ h => h) hag
    (fun _ _ => rfl)
  refine ⟨?_, ?_, ?_, ?_, h'.varT, ?_, ?_⟩
  · intro i b hb
    rw [lookup_size_cons] at hb
    by_cases hi : i = js
    · simp [hi] at hb; exact ⟨j, 0, hb.symm⟩
    · simp [hi] at hb; exact h.varS i b hb
  · intro i b hb
    rw [lookup_size_cons] at hb
    by_cases hi : i = js
    · simp [hi] at hb; subst hb; exact sizeWf_fresh_var _ _ _
    · simp [hi] at hb; exact h'.targetS i b hb
  · intro i hi hn
    rw [lookup_size_cons] at hn
    by_cases hij : i = js
    · simp [hij] at hn
    · simp only [hij, if_false] at hn
      exact h'.untouchedS i (mem_dom_extSz hi hij) hn
  · intro i hi
    simp only [substVal]
    rw [lookup_size_cons]
    by_cases hij : i = js
    · subst hij; simp [sizeVal, SCtx.extSz, SizeVal.update]
    · simp only [hij, if_false]
      have := h'.valS i (mem_dom_extSz hi hij)
      simp only [substVal] at this
      rw [this]
      simp [SCtx.extSz, SizeVal.update, hij]
  · intro X hX hn; exact h'.untouchedT X hX hn
  · intro X hX
    have := h'.valT X hX
    rw [this]; rfl

theorem mem_dom_extTy {c : SCtx} {X : Nat} {κ : Kind} {Y : Sem κ.erase} {Z : Nat}
    (hZ : Z ∈ (c.extTy X κ Y).Θ.map Prod.fst) (hZX : Z ≠ X) : Z ∈ c.Θ.map Prod.fst := by
  simp only [SCtx.extTy, List.map_append, List.mem_append, List.map_cons, List.map_nil,
    List.mem_singleton] at hZ
  rcases hZ with hZ | hZ
  · exact hZ
  · exact absurd hZ hZX

/-- A fresh type variable on both sides extends the renaming. -/
theorem Renaming.extTy {W : World} {cc cs : SCtx} {πS : List (Nat × Size)} {πT : List (Nat × Ty)}
    (h : Renaming W cc cs πS πT) {X Xs : Nat} (hX : X ∉ cc.Θ.map Prod.fst) {κ : Kind}
    {Y : Sem κ.erase} :
    Renaming W (cc.extTy X κ Y) (cs.extTy Xs κ Y) πS ((Xs, .fvar X) :: πT) := by
  have hagθ : ∀ Z ∈ cc.Θ.map Prod.fst, (cc.extTy X κ Y).θ Z = cc.θ Z :=
    TEnv.update_agree hX
  have h' := h.extend_clause (cc' := cc.extTy X κ Y) (fun _ h => h)
    (fun Z hZ => by simp only [SCtx.extTy, List.map_append]; exact mem_append_left' Z hZ)
    (fun _ _ => rfl) hagθ
  refine ⟨h'.varS, h'.targetS, h'.untouchedS, ?_, ?_, ?_, ?_⟩
  · intro i hi; exact h'.valS i hi
  · intro Z T hT
    rw [lookup_ty_cons] at hT
    by_cases hZ : Z = Xs
    · simp [hZ] at hT; subst hT; exact ⟨X, rfl, by simp [SCtx.extTy]⟩
    · simp [hZ] at hT; exact h'.varT Z T hT
  · intro Z hZ hn
    rw [lookup_ty_cons] at hn
    by_cases hZX : Z = Xs
    · simp [hZX] at hn
    · simp only [hZX, if_false] at hn
      exact h'.untouchedT Z (mem_dom_extTy hZ hZX) hn
  · intro Z hZ
    simp only [substTVal]
    rw [lookup_ty_cons]
    by_cases hZX : Z = Xs
    · subst hZX
      simp only [if_true, tyVal_fvar]
      simp [SCtx.extTy, TEnv.update]
    · simp only [hZX, if_false]
      have := h'.valT Z (mem_dom_extTy hZ hZX)
      simp only [substTVal] at this
      rw [this]
      simp [SCtx.extTy, TEnv.update, hZX]

/-! ## Alignment of copattern typing with semantic spines -/

/-- The conclusion of spine alignment. -/
def AlignOK (W : World) (Ψc : SizeCtx) (Θc : TyCtx) (ρc : SizeVal) (θc : TEnv)
    (Ψ'c : SizeCtx) (Θ'c : TyCtx) (Γ' : TermCtx) (σm : TmSubst) (C : Ty) (cs' : SCtx)
    (Bs : Ty) : Prop :=
  ∃ ρc' θc' πS' πT', ValidVal (Ψc ++ Ψ'c) ρc' ∧ CtxBoundsWf (Ψc ++ Ψ'c) ∧
    TEnvOK W (Θc ++ Θ'c) θc' ∧ (∀ i ∈ Ψc.dom, ρc' i = ρc i) ∧
    (∀ X ∈ Θc.map Prod.fst, θc' X = θc X) ∧
    SemCtx W ρc' θc' Γ' σm ∧ TermCtxWf (Ψc ++ Ψ'c) (Θc ++ Θ'c) Γ' ∧
    C = (Bs.substSize πS').substFTy πT' ∧ Renaming W ⟨Ψc ++ Ψ'c, Θc ++ Θ'c, ρc', θc'⟩ cs' πS' πT'

theorem TermCtxWf.merge {Ψ Ψ₁ Ψ₂ : SizeCtx} {Θ Θ₁ Θ₂ : TyCtx} {Γ₁ Γ₂ : TermCtx}
    (h₁ : TermCtxWf (Ψ ++ Ψ₁) (Θ ++ Θ₁) Γ₁) (h₂ : TermCtxWf (Ψ ++ Ψ₁ ++ Ψ₂) (Θ ++ Θ₁ ++ Θ₂) Γ₂) :
    TermCtxWf (Ψ ++ (Ψ₁ ++ Ψ₂)) (Θ ++ (Θ₁ ++ Θ₂)) (Γ₁ ++ Γ₂) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · have h' := h₁ q hq
    rw [TyCtx.toK_append] at h'
    have h'' : KindingC (Ψ ++ Ψ₁ ++ Ψ₂) ((Θ.toK ++ Θ₁.toK) ++ Θ₂.toK) q.2 .star :=
      KindingC.mono_append h'
    simpa using h''
  · simpa using h₂ q hq

/-- Spine matching soundness, aligned with a semantic spine up to renaming. -/
theorem spine_align {W : World} (hW : WorldClosed W) {Ψc : SizeCtx} {Θc : TyCtx}
    {qs : List Copat} {Tc : Ty} {Γ' : TermCtx} {Ψ'c : SizeCtx} {Θ'c : TyCtx} {C : Ty}
    (hsp : SpineTy Ψc Θc qs Tc Γ' Ψ'c Θ'c C) :
    ∀ (ρc : SizeVal) (θc : TEnv) (cs : SCtx) (Ts : Ty) (es : List Elim) (cs' : SCtx) (Bs : Ty)
      (σm : TmSubst) (πS : List (Nat × Size)) (πT : List (Nat × Ty)),
      PosOK W ⟨Ψc, Θc, ρc, θc⟩ Tc → PosOK W cs Ts → Tc = (Ts.substSize πS).substFTy πT →
      Renaming W ⟨Ψc, Θc, ρc, θc⟩ cs πS πT →
      SemSpine W cs Ts es cs' Bs → matchSpine qs es = .yes σm → es.length = qs.length →
      AlignOK W Ψc Θc ρc θc Ψ'c Θ'c Γ' σm C cs' Bs := by
  induction hsp with
  | nil Ψ Θ A =>
    intro ρc θc cs Ts es cs' Bs σm πS πT hokc _ hT hren hs hm hlen
    cases es with
    | cons _ _ => simp at hlen
    | nil =>
      cases hs
      simp [matchSpine] at hm; subst hm
      refine ⟨ρc, θc, πS, πT, by simpa using hokc.1, by simpa using hokc.2.1,
        by simpa using hokc.2.2.1, fun _ _ => rfl, fun _ _ => rfl, SemCtx.nil W ρc θc,
        by simp [TermCtxWf], hT, ?_⟩
      simpa using hren
  | @pat Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p qs A B C Γ₁ Γ₂ hp _ ih =>
    intro ρc θc cs Ts es cs' Bs σm πS πT hokc hoks hT hren hs hm hlen
    cases es with
    | nil => simp at hlen
    | cons e es =>
      cases hs with
      | proj _ _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | instT _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | instS _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | @term _ _ T₁ T₂ _ s _ hsT hs' =>
        simp only [matchSpine, matchCopat] at hm
        obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
        simp only [Ty.substSize, Ty.substFTy] at hT
        injection hT with hA hB
        have hwfA : KindingC Ψ Θ.toK A .star := PosOK.dom (c := ⟨Ψ, Θ, ρc, θc⟩) hokc
        have hwfB : KindingC Ψ Θ.toK B .star := (PosOK.term (c := ⟨Ψ, Θ, ρc, θc⟩) hokc).2.2.2
        have hwfT₁ : TyWf cs.Ψ (cs.Θ.map Prod.fst) 0 0 T₁ := by simpa using hoks.dom.tyWf
        have hsA : s ∈ interpT W ρc θc A SzEnv.zero Env.empty := by
          have := hren.den_eq hwfT₁
          simp only [SCtx.den] at this
          rw [hA, this]; exact hsT
        obtain ⟨ρ₁, θ₁, hv₁, hag₁, hθ₁, hagθ₁, hctx₁⟩ :=
          pat_sound hW hp ρc θc s σ₁ hokc.1 hokc.2.1 hokc.2.2.1 hwfA hsA hm₁
        obtain ⟨hΓ₁, hb₁⟩ := patTy_ctx hp hwfA hokc.2.1
        have hren₁ := hren.extend_clause (cc' := ⟨Ψ ++ Ψ₁, Θ ++ Θ₁, ρ₁, θ₁⟩) dom_append_left
          (fun X hX => by simp only [List.map_append]; exact mem_append_left' X hX) hag₁ hagθ₁
        have hwfB₁ : KindingC (Ψ ++ Ψ₁) (Θ ++ Θ₁).toK B .star := by
          rw [TyCtx.toK_append]; exact KindingC.mono_append hwfB
        obtain ⟨ρc', θc', πS', πT', hv', hb', hθ', hag', hagθ', hctx₂, hΓ₂, hC, hren'⟩ :=
          ih ρ₁ θ₁ cs T₂ es cs' Bs σ₂ πS πT ⟨hv₁, hb₁, hθ₁, hwfB₁⟩ hoks.term hB hren₁ hs'
            hm₂ (by simpa using hlen)
        refine ⟨ρc', θc', πS', πT', by simpa using hv', by simpa using hb', by simpa using hθ',
          ?_, ?_, ?_, TermCtxWf.merge hΓ₁ hΓ₂, hC, by simpa using hren'⟩
        · intro i hi; rw [hag' i (dom_append_left i hi), hag₁ i hi]
        · intro X hX
          rw [hagθ' X (by simp only [List.map_append]; exact mem_append_left' X hX), hagθ₁ X hX]
        · apply (hctx₁.agree hΓ₁ (fun i hi => (hag' i hi).symm)
            (fun X hX => (hagθ' X hX).symm)).append hctx₂
          rw [(matchPat_facts p s σ₁ hm₁).1, patTy_dom hp]
  | @proj Ψ Ψ' Θ Θ' d j qs a R Rd C Γ hd hj _ ih =>
    intro ρc θc cs Ts es cs' Bs σm πS πT hokc hoks hT hren hs hm hlen
    cases es with
    | nil => simp at hlen
    | cons e es =>
      cases hs with
      | term _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | instT _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | instS _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | @proj _ _ as Rs d' js Rds _ β _ hds hjs hβ hs' =>
        simp only [matchSpine, matchCopat] at hm
        by_cases hdd : d = d'
        · subst hdd
          simp only [if_true] at hm
          obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
          cases hm₁
          simp only [Ty.substSize, Ty.substFTy] at hT
          injection hT with ha hR
          obtain ⟨_, πs, _, has, hRsk⟩ := Kinding.inv_nu hoks.2.2.2
          have hRs : ∀ T ∈ Rs, TyWf cs.Ψ (cs.Θ.map Prod.fst) 1 0 T :=
            fun T hT => by simpa using (hRsk T hT).tyWf
          have hRd : Rd = (Rds.substSize πS).substFTy πT := by
            have h1 := Ty.substSizeList_getElem? πS Rs d
            have h2 := Ty.substFTyList_getElem? πT (Ty.substSizeList πS Rs) d
            rw [h1, hds] at h2
            rw [← hR, hd] at h2
            simpa using h2
          have hβc : β < sizeVal ρc SzEnv.zero a := by
            rw [ha, sizeVal_subst hren.varS.lc]
            rw [sizeVal_agree (Ψ := cs.Ψ) (m := 0) (fun i hi => hren.valS i hi)
              (fun _ h => absurd h (Nat.not_lt_zero _)) has]
            exact hβ
          have hokc₁ := PosOK.proj (c := ⟨Ψ, Θ, ρc, θc⟩) hokc hd hj hβc
          have hoks₁ := hoks.proj hds hjs hβ
          have hren₁ := hren.extSz (j := j) (js := js) (a := a) (as := as) (β := β) hj
          have hRds_wf : TyWf cs.Ψ (cs.Θ.map Prod.fst) 1 0 Rds := hRs Rds (List.mem_of_getElem? hds)
          have hT' : Rd.substTy 0 (.nu (.var j 0) R) =
              ((Rds.substTy 0 (.nu (.var js 0) Rs)).substSize ((js, .var j 0) :: πS)).substFTy
                πT := by
            rw [Ty.substSize_substTy, Ty.substFTy_substTy hren.fvar.closed]
            have h1 : Rds.substSize ((js, .var j 0) :: πS) = Rds.substSize πS :=
              hRds_wf.substSize_cons_fresh hjs _ _
            have h2 : Ty.substSizeList ((js, .var j 0) :: πS) Rs = Ty.substSizeList πS Rs := by
              have := hoks.tyWf.substSize_cons_fresh hjs (.var j 0) πS
              simp only [Ty.substSize] at this
              injection this
            have h3 : (Size.var js 0).subst ((js, .var j 0) :: πS) = .var j 0 := by
              simp [Size.subst, lookup_size_cons, Size.shift]
            simp only [Ty.substSize, Ty.substFTy, h1, h2, h3, ← hR, ← hRd]
          obtain ⟨ρc', θc', πS', πT', hv', hb', hθ', hag', hagθ', hctx, hΓ, hC, hren'⟩ :=
            ih _ θc _ _ es cs' Bs σ₂ _ πT hokc₁ hoks₁ hT' hren₁ hs' hm₂ (by simpa using hlen)
          refine ⟨ρc', θc', πS', πT', by simpa using hv', by simpa using hb', hθ', ?_, hagθ',
            by simpa using hctx, by simpa using hΓ, hC, by simpa using hren'⟩
          intro i hi
          rw [hag' i (dom_append_left i hi)]
          exact SizeVal.update_agree hj i hi
        · simp [hdd, MatchRes.and_no_left] at hm
  | @instT Ψ Ψ' Θ Θ' X κ qs B C Γ hX _ ih =>
    intro ρc θc cs Ts es cs' Bs σm πS πT hokc hoks hT hren hs hm hlen
    cases es with
    | nil => simp at hlen
    | cons e es =>
      cases hs with
      | term _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | proj _ _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | instS _ _ _ =>
        simp only [Ty.substSize, Ty.substFTy] at hT
        cases hT
      | @instT _ _ κs Bs' _ Xs Y _ hXs hY hs' =>
        simp only [matchSpine, matchCopat] at hm
        obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
        cases hm₁
        simp only [Ty.substSize, Ty.substFTy] at hT
        injection hT with hκ hB
        subst hκ
        have hBs : TyWf cs.Ψ (cs.Θ.map Prod.fst) 1 0 Bs' := by
          simpa using (Kinding.inv_allT hoks.2.2.2).2.tyWf
        have hokc₁ := PosOK.instT (c := ⟨Ψ, Θ, ρc, θc⟩) hokc hX hY
        have hoks₁ := hoks.instT hXs hY
        have hren₁ := hren.extTy (X := X) (Xs := Xs) (κ := κ) (Y := Y) hX
        have hT' : B.substTy 0 (.fvar X) =
            ((Bs'.substTy 0 (.fvar Xs)).substSize πS).substFTy ((Xs, .fvar X) :: πT) := by
          have hfv : FVarSubst ((Xs, Ty.fvar X) :: πT) := by
            intro Z T hT
            rw [lookup_ty_cons] at hT
            by_cases hZ : Z = Xs
            · simp [hZ] at hT; exact ⟨X, hT.symm⟩
            · simp [hZ] at hT; exact hren.fvar Z T hT
          rw [Ty.substSize_substFTy hfv, Ty.substFTy_substTy hfv.closed, Ty.substSize_substTy]
          have h1 : Bs'.substFTy ((Xs, .fvar X) :: πT) = Bs'.substFTy πT :=
            hBs.substFTy_cons_fresh hXs _ _
          have h2 : (Ty.fvar Xs).substFTy ((Xs, .fvar X) :: πT) = .fvar X := by
            simp [Ty.substFTy, lookup_ty_cons]
          rw [h1, h2, ← Ty.substSize_substFTy hren.fvar, ← hB]
          rfl
        obtain ⟨ρc', θc', πS', πT', hv', hb', hθ', hag', hagθ', hctx, hΓ, hC, hren'⟩ :=
          ih ρc _ _ _ es cs' Bs σ₂ πS _ hokc₁ hoks₁ hT' hren₁ hs' hm₂ (by simpa using hlen)
        refine ⟨ρc', θc', πS', πT', hv', hb', by simpa using hθ', hag', ?_, by simpa using hctx,
          by simpa using hΓ, hC, by simpa using hren'⟩
        intro Z hZ
        rw [hagθ' Z (by simp only [List.map_append]; exact mem_append_left' Z hZ)]
        exact TEnv.update_agree hX Z hZ
  | @instS Ψ Ψ' Θ Θ' j qs a B C Γ hj _ ih =>
    intro ρc θc cs Ts es cs' Bs σm πS πT hokc hoks hT hren hs hm hlen
    cases es with
    | nil => simp at hlen
    | cons e es =>
      cases hs with
      | term _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | proj _ _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | instT _ _ _ =>
        simp only [Ty.substSize, Ty.substFTy] at hT
        cases hT
      | @instS _ _ as Bs' _ js β _ hjs hβ hs' =>
        simp only [matchSpine, matchCopat] at hm
        obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
        cases hm₁
        simp only [Ty.substSize, Ty.substFTy] at hT
        injection hT with ha hB
        obtain ⟨_, has, hBsk⟩ := Kinding.inv_allS hoks.2.2.2
        have hBs : TyWf cs.Ψ (cs.Θ.map Prod.fst) 0 1 Bs' := by simpa using hBsk.tyWf
        have hβc : β < sizeVal ρc SzEnv.zero a := by
          rw [ha, sizeVal_subst hren.varS.lc]
          rw [sizeVal_agree (Ψ := cs.Ψ) (m := 0) (fun i hi => hren.valS i hi)
            (fun _ h => absurd h (Nat.not_lt_zero _)) has]
          exact hβ
        have hokc₁ := PosOK.instS (c := ⟨Ψ, Θ, ρc, θc⟩) hokc hj hβc
        have hoks₁ := hoks.instS hjs hβ
        have hren₁ := hren.extSz (j := j) (js := js) (a := a) (as := as) (β := β) hj
        have hvar : VarSubst ((js, Size.var j 0) :: πS) := by
          intro i b hb
          rw [lookup_size_cons] at hb
          by_cases hi : i = js
          · simp [hi] at hb; exact ⟨j, 0, hb.symm⟩
          · simp [hi] at hb; exact hren.varS i b hb
        have hT' : B.openSz 0 (.var j 0) =
            ((Bs'.openSz 0 (.var js 0)).substSize ((js, .var j 0) :: πS)).substFTy πT := by
          rw [Ty.substSize_openSz hvar.lc, Ty.substFTy_openSz hren.fvar.closed]
          have h1 : Bs'.substSize ((js, .var j 0) :: πS) = Bs'.substSize πS :=
            hBs.substSize_cons_fresh hjs _ _
          have h3 : (Size.var js 0).subst ((js, .var j 0) :: πS) = .var j 0 := by
            simp [Size.subst, lookup_size_cons, Size.shift]
          rw [h1, h3, ← hB]
        obtain ⟨ρc', θc', πS', πT', hv', hb', hθ', hag', hagθ', hctx, hΓ, hC, hren'⟩ :=
          ih _ θc _ _ es cs' Bs σ₂ _ πT hokc₁ hoks₁ hT' hren₁ hs' hm₂ (by simpa using hlen)
        refine ⟨ρc', θc', πS', πT', by simpa using hv', by simpa using hb', hθ', ?_, hagθ',
          by simpa using hctx, by simpa using hΓ, hC, by simpa using hren'⟩
        intro i hi
        rw [hag' i (dom_append_left i hi)]
        exact SizeVal.update_agree hj i hi

end NishtAbel2024V5
