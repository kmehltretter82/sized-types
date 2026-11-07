import Solutions.V5.FinalCore
import Solutions.V5.InfMain
import Solutions.V5.InfGraph
import Solutions.V5.Theorem6
import Solutions.V5.Example

/-! # V5: all milestone theorem bundles and Theorem 15, proved with standard axioms only -/

namespace NishtAbel2024V5

/-- **Theorems 2 and 3** (`NishtAbel2024V5.theorems_2_and_3`). -/
theorem theorems_2_and_3 :
    (∀ (Ψ : SizeCtx) (ρ ρ' : SizeVal),
      ValidVal Ψ ρ →
      ValidVal Ψ ρ' →
      (∀ i ∈ Ψ.dom, ρ i ≤ ρ' i) →
      (∀ a : Size, SizeWf Ψ a → sizeVal ρ SzEnv.zero a ≤ sizeVal ρ' SzEnv.zero a) ∧
      (∀ a b : Size, SizeLe Ψ a b → sizeVal ρ SzEnv.zero a ≤ sizeVal ρ' SzEnv.zero b) ∧
      (∀ a b : Size, SizeLt Ψ a b → sizeVal ρ SzEnv.zero a < sizeVal ρ' SzEnv.zero b)) ∧
    (∀ (W : World) (Ψ : SizeCtx) (ρ : SizeVal),
      (∀ d ∈ W, (Tm.lam d.clauses).Closed) →
      SizeCtxWf Ψ →
      ValidVal Ψ ρ →
      (∀ (F : Ty) (κ : Kind),
        KindingC Ψ [] F κ →
        Good W κ (interp W ρ TEnv.empty F κ.erase SzEnv.zero Env.empty)) ∧
      (∀ (A B : Ty) (κ : Kind),
        SubTy Ψ [] A B κ →
        SemLe W κ (interp W ρ TEnv.empty A κ.erase SzEnv.zero Env.empty)
          (interp W ρ TEnv.empty B κ.erase SzEnv.zero Env.empty))) ∧
    (∀ (W : World) (Ω : TypingEnv) (Ψ : SizeCtx) (ρ : SizeVal),
      (∀ d ∈ W, (Tm.lam d.clauses).Closed) →
      SemValid W Ω.sig →
      (∀ (Ψ' : SizeCtx) (ρ' : SizeVal) (g : FunDecl) (as : List Size),
        g ∈ Ω.block → Ω.localOK Ψ' g.name as → ValidVal Ψ' ρ' →
        ∀ ρg : SizeVal, ValidVal g.sizeParams ρg →
          g.sizeParams.map (fun p => ρg p.1) = as.map (sizeVal ρ' SzEnv.zero) →
          Tm.fn g.name ∈ interpT W ρg TEnv.empty g.ty SzEnv.zero Env.empty) →
      SizeCtxWf Ψ →
      ValidVal Ψ ρ →
      (∀ (t : Tm) (A : Ty),
        ExprTy Ω Ψ [] [] t A →
        KindingC Ψ [] A .star ∧ t ∈ interpT W ρ TEnv.empty A SzEnv.zero Env.empty) ∧
      (∀ (D : List Clause) (A : Ty),
        KindingC Ψ [] A .star →
        (∀ cl ∈ D, ClauseTy Ω Ψ [] [] cl A) →
        Tm.lam D ∈ interpT W ρ TEnv.empty A SzEnv.zero Env.empty)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Ψ ρ ρ' hv hv' hle
    exact ⟨fun _ ha => sizeWf_sound hle SzEnv.zero ha,
      fun _ _ h => sizeLe_sound2 h hv hv' hle,
      fun _ _ h => sizeLt_sound2 h hv hv' hle⟩
  · intro W Ψ ρ hW hΨ hv
    have hθ : TRel W [] TEnv.empty TEnv.empty := fun _ _ _ hX => by simp at hX
    refine ⟨fun F κ hk => (kinding_sound hW hk ρ TEnv.empty TEnv.empty SzEnv.zero
        Env.empty Env.empty hθ (BRel.nil W _ _)).1,
      fun A B κ hsub => (subTy_sound hW hsub ρ TEnv.empty hv hΨ.bounds hθ).2.2⟩
  · intro W Ω Ψ ρ hW hsig hguard hΨ hv
    have E : FundEnv W Ω (fun _ _ => True) :=
      ⟨hW, hsig, fun Ψ' ρ' g as hg hloc hv' _ => hguard Ψ' ρ' g as hg hloc hv',
        fun _ _ _ _ _ _ _ => trivial⟩
    have hθ : TEnvOK W [] TEnv.empty := by intro X π κ hX; simp [TyCtx.toK] at hX
    have hok : CtxOK W (fun _ _ => True) Ψ [] [] ρ TEnv.empty [] :=
      ⟨hv, hΨ.bounds, hθ, by simp [TermCtxWf], SemCtx.nil W ρ TEnv.empty, trivial⟩
    refine ⟨fun t A ht => ?_, fun D A hA hD => ?_⟩
    · have h := fundamental E ht ρ TEnv.empty [] hok
      rwa [Tm.subst_nil] at h
    · have h := (fundamental E (ExprTy.lam hA hD) ρ TEnv.empty [] hok).2
      rwa [Tm.subst_nil] at h

/-- **Theorem 4, Lemma 2, Theorem 5, and Theorem 6** (`NishtAbel2024V5.theorems_4_5_and_6`). -/
theorem theorems_4_5_and_6 :
    (∀ (W sig Ξ : List FunDecl),
      (∀ d ∈ sig ++ Ξ, d ∈ W) →
      (W.map FunDecl.name).Nodup →
      (∀ d ∈ W, (Tm.lam d.clauses).Closed) →
      BlockTy sig Ξ →
      SemValid W sig →
      SemValid W Ξ) ∧
    (∀ (W : List FunDecl) (blocks : List (List FunDecl)),
      (∀ d ∈ blocks.flatten, d ∈ W) →
      (W.map FunDecl.name).Nodup →
      (∀ d ∈ W, (Tm.lam d.clauses).Closed) →
      BlocksTy blocks →
      SemValid W blocks.flatten) ∧
    (∀ (blocks : List (List FunDecl)) (main : Tm) (A : Ty),
      ProgramTy blocks main A →
      SN blocks.flatten main) ∧
    (∀ (sig Ξ : List FunDecl),
      LexBlockTy sig Ξ →
      BlockTy sig Ξ) :=
  ⟨theorem_4_core,
   fun _ _ hsub hnames hwc hbt => blocks_valid ramseyPairs hnames hwc hbt hsub,
   theorem_5_core,
   fun _ _ h => theorem_6_proof h⟩

/-- **Theorems 7, 8, 9 and Lemmas 3, 4, 5** (`NishtAbel2024V5.theorems_7_8_9_and_lemmas_3_4_5`). -/
theorem theorems_7_8_9_and_lemmas_3_4_5 :
    (∀ {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx} {A A' : Ty} {Ψ : SizeCtx}
       {κ : Kind},
      EKinding Δ Δb A κ →
      Encode πs ok π Δ Δb A Ψ A' →
      SizeCtxWf Ψ ∧ Kinding Ψ Δ Δb 0 A' κ) ∧
    (∀ {ok : Nat → Prop} {Δ : KCtx} {Δb : BCtx} {A A' : Ty} {Ψ : SizeCtx},
      Encode .neg ok .pos Δ Δb A Ψ A' →
      ∀ i ∈ Ψ.dom,
        (SizeOcc .mu i Δ Δb .neg A' ∧ paramPol A' i = .pos ∧
          (∀ Δ' Δb' q, ¬ SizeOcc .nu i Δ' Δb' q A')) ∨
        (SizeOcc .nu i Δ Δb .pos A' ∧ paramPol A' i = .neg ∧
          (∀ Δ' Δb' q, ¬ SizeOcc .mu i Δ' Δb' q A'))) ∧
    (∀ {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : TyCtx},
      InferPat Ψ Θ p A Γ Ψ' Θ' →
      PatTy Ψ Θ p A Γ Ψ' Θ') ∧
    (∀ {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
       {Θ' : TyCtx} {C : Ty},
      InferSpine Ψ Θ qs A Γ Ψ' Θ' C →
      SpineTy Ψ Θ qs A Γ Ψ' Θ' C) ∧
    (∀ {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : TyCtx},
      InferPat Ψ Θ p A Γ Ψ' Θ' →
      (∀ q ∈ Ψ', RigidName q.1) ∧
      (∀ {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol} {xB : Nat × Ty},
        xB ∈ Γ → SizeOcc fk i Δ Δb π xB.2 → A.indexes fk i = true ∨ (fk = .mu ∧ i ∈ Ψ'.dom)) ∧
      (∀ j ∈ Ψ'.dom, A.indexes .nu j = false →
        ∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .nu j Δ Δb π xB.2)) ∧
    (∀ {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
       {Θ' : TyCtx} {C : Ty},
      InferSpine Ψ Θ qs A Γ Ψ' Θ' C →
      (∀ i ∈ Ψ'.dom, RigidName i) ∧
      (∀ {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol},
        ((∃ xB ∈ Γ, SizeOcc fk i Δ Δb π xB.2) ∨ SizeOcc fk i Δ Δb π C) →
        A.indexes fk i = true ∨ i ∈ Ψ'.dom) ∧
      (∀ {ok : Nat → Prop} {Δ₀ : KCtx} {Δb₀ : BCtx} {A₀ : Ty},
        Encode .neg ok .pos Δ₀ Δb₀ A₀ Ψ A →
        NamesDisjoint Ψ.dom Ψ'.dom →
        ∀ i ∈ Ψ.dom,
          (paramPol A i = .pos ∧
            (∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .nu i Δ Δb π xB.2) ∧
            (∀ Δ Δb π, ¬ SizeOcc .nu i Δ Δb π C)) ∨
          (paramPol A i = .neg ∧
            (∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .mu i Δ Δb π xB.2) ∧
            (∀ Δ Δb π, ¬ SizeOcc .mu i Δ Δb π C)))) :=
  ⟨theorem_7, lemma_3, inferPat_sound, inferSpine_sound, lemma_4, lemma_5⟩

/-- **Theorems 10, 11, and 12** (`NishtAbel2024V5.theorems_10_11_and_12`). -/
theorem theorems_10_11_and_12 :
    (∀ {Ψ : SizeCtx} {Δ : KCtx} {A B : Ty} {κ : Kind} {C : List SConstr},
      Compare Ψ Δ A B κ C →
      ∀ c ∈ C,
        c.ctx = Ψ ∧ c.strict = false ∧ c.up = true ∧
        ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars, A.indexes .mu i = true ∨ B.indexes .mu i = true) ∨
         (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars, A.indexes .nu i = true ∨ B.indexes .nu i = true))) ∧
    (∀ {Ω : InfEnv},
      (∀ {Ψ Θ Γ r A Φ C T K},
        InferTm Ω Ψ Θ Γ r A Φ C T K →
        ∀ c ∈ C,
          (∃ j π, FlexName j ∧ ⟨j, π, c.ctx⟩ ∈ Φ ∧ (π = .pos ∨ π = .neg) ∧
            c.lhs = .var j 0 ∧ c.strict = true ∧ c.up = true) ∨
          (∃ k, FlexName k ∧ c.lhs = .var k 0 ∧ c.strict = true ∧ c.up = false) ∨
          (∃ A₁ B₁ : Ty, c.strict = false ∧ c.up = true ∧
            ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .mu i = true ∨ B₁.indexes .mu i = true) ∨
             (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .nu i = true ∨ B₁.indexes .nu i = true)))) ∧
      (∀ {Ψ Θ Γ A t Φ C T K},
        CheckTm Ω Ψ Θ Γ A t Φ C T K →
        ∀ c ∈ C,
          (∃ j π, FlexName j ∧ ⟨j, π, c.ctx⟩ ∈ Φ ∧ (π = .pos ∨ π = .neg) ∧
            c.lhs = .var j 0 ∧ c.strict = true ∧ c.up = true) ∨
          (∃ k, FlexName k ∧ c.lhs = .var k 0 ∧ c.strict = true ∧ c.up = false) ∨
          (∃ A₁ B₁ : Ty, c.strict = false ∧ c.up = true ∧
            ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .mu i = true ∨ B₁.indexes .mu i = true) ∨
             (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .nu i = true ∨ B₁.indexes .nu i = true)))) ∧
      (∀ {Ψ Θ Γ A cl Φ C T K},
        CheckClause Ω Ψ Θ Γ A cl Φ C T K →
        ∀ c ∈ C,
          (∃ j π, FlexName j ∧ ⟨j, π, c.ctx⟩ ∈ Φ ∧ (π = .pos ∨ π = .neg) ∧
            c.lhs = .var j 0 ∧ c.strict = true ∧ c.up = true) ∨
          (∃ k, FlexName k ∧ c.lhs = .var k 0 ∧ c.strict = true ∧ c.up = false) ∨
          (∃ A₁ B₁ : Ty, c.strict = false ∧ c.up = true ∧
            ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .mu i = true ∨ B₁.indexes .mu i = true) ∨
             (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .nu i = true ∨ B₁.indexes .nu i = true))))) := by
  refine ⟨theorem_10, fun {Ω} => ?_⟩
  obtain ⟨hI, hC, hCl⟩ := theorems_11_and_12 (Ω := Ω)
  have unpack : ∀ {Φ : List FlexVar} {c : SConstr}, InfConstrOrigin Φ c →
      (∃ j π, FlexName j ∧ ⟨j, π, c.ctx⟩ ∈ Φ ∧ (π = .pos ∨ π = .neg) ∧
        c.lhs = .var j 0 ∧ c.strict = true ∧ c.up = true) ∨
      (∃ k, FlexName k ∧ c.lhs = .var k 0 ∧ c.strict = true ∧ c.up = false) ∨
      (∃ A₁ B₁ : Ty, c.strict = false ∧ c.up = true ∧
        ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
            A₁.indexes .mu i = true ∨ B₁.indexes .mu i = true) ∨
         (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
            A₁.indexes .nu i = true ∨ B₁.indexes .nu i = true))) := by
    intro Φ c h
    rcases h with h1 | h2 | ⟨A₁, B₁, _, hstr, hup, hvars⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨A₁, B₁, hstr, hup, hvars⟩)
  exact ⟨fun h c hc => unpack (hI h c hc),
    fun h c hc => unpack (hC h c hc),
    fun h c hc => unpack (hCl h c hc)⟩

/-- **Theorems 13 and 14, and Corollary** (`NishtAbel2024V5.theorems_13_and_14`). -/
theorem theorems_13_and_14 :
    (∀ {Ω : InfEnv} {Ωd : TypingEnv} {φ : FlexSubst}
       {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {A : Ty} {cl : Clause}
       {Φ : List FlexVar} {C : List SConstr} {T : List Nat} {K : List CallRec},
      Ω.sig = Ωd.sig →
      Ω.block = Ωd.block →
      (∀ g ∈ Ω.sig, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star) →
      (∀ g ∈ Ω.block, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star) →
      (∀ p ∈ φ, FlexName p.1) →
      CheckClause Ω Ψ Θ Γ A cl Φ C T K →
      Coherent φ C →
      ScopeOK φ Φ →
      (∀ k ∈ K, Ωd.localOK (k.ctx.substBounds φ) k.callee (k.args.map (Size.subst φ))) →
      (∀ p ∈ Γ, KindingC (Ψ.substBounds φ) Θ.toK (p.2.substSize φ) .star) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star →
      ClauseTy Ωd (Ψ.substBounds φ) Θ (Γ.map fun p => (p.1, p.2.substSize φ)) cl
        (A.substSize φ)) ∧
    (∀ (fuel : Nat) (Φ : List FlexVar) (C : List SConstr) (T : List Nat),
      (∀ v ∈ Φ, FlexName v.name) →
      checkScope (solve fuel Φ C T) Φ = true →
      checkCoherent fuel (solve fuel Φ C T) C = true →
      (∀ p ∈ solve fuel Φ C T, FlexName p.1) ∧
        ScopeOK (solve fuel Φ C T) Φ ∧
        Coherent (solve fuel Φ C T) C) ∧
    (∀ {sig Ξ Ξannot : List FunDecl},
      (∀ g ∈ sig, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star) →
      Algorithm2Accepts sig Ξ Ξannot →
      BlockTy sig Ξannot) :=
  ⟨fun hsig hblk hsigwf hblkwf hφ hcl hcoh hsc hK hΓ hA =>
     (inference_sound hsig.symm hblk.symm hsigwf hblkwf hφ).2.2 hcl hcoh hsc hK
       (fun q hq => by
         obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
         exact hΓ p hp)
       hA,
   theorem_14,
   fun hsigwf hacc => algorithm2_typing hsigwf hacc⟩

/-- **Theorem 15** (`NishtAbel2024V5.theorem_15`). -/
theorem theorem_15 (W sig Ξ Ξannot : List FunDecl)
    (hsigwf : ∀ g ∈ sig, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star)
    (hacc : Algorithm2Accepts sig Ξ Ξannot)
    (hW : ∀ d ∈ sig ++ Ξannot, d ∈ W)
    (hnames : (W.map FunDecl.name).Nodup)
    (hclosed : ∀ d ∈ W, (Tm.lam d.clauses).Closed)
    (hsig : SemValid W sig) :
    BlockTy sig Ξannot ∧ SemValid W Ξannot :=
  theorem_15_proof ramseyPairs W sig Ξ Ξannot hsigwf hacc hW hnames hclosed hsig

/-- The V5 worked example block is semantically valid using only Lean's standard axioms. -/
theorem example_block_valid : SemValid Example.block Example.block :=
  Example.block_valid ramseyPairs

end NishtAbel2024V5

#print axioms NishtAbel2024V5.theorems_2_and_3
#print axioms NishtAbel2024V5.theorems_4_5_and_6
#print axioms NishtAbel2024V5.theorems_7_8_9_and_lemmas_3_4_5
#print axioms NishtAbel2024V5.theorems_10_11_and_12
#print axioms NishtAbel2024V5.theorems_13_and_14
#print axioms NishtAbel2024V5.theorem_15
#print axioms NishtAbel2024V5.example_block_valid
