import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Logic.Relation
import Definitions.Def_NishtAbel2024V4_Syntax

/-!
# Nisht & Abel (2024), V4: operational semantics and type interpretation

As in V3: deterministic first-match clause selection, weak reduction of closed terms, and semantic
types as sets of closed strongly normalizing terms, with `∞` interpreted as `Ω = (succ #Tm).ord`.
New in V4: `∀X` ranges over all reducibility candidates (so candidates are defined here),
`∀(j < a)` over all ordinals below the bound, and packs are introduction forms.
-/

namespace NishtAbel2024V4

open NishtAbel2024V2 (FunName)

/-! ## Matching and head reduction -/

/-- Outcome of matching: success with a substitution, a definite mismatch, or undecided. -/
inductive MatchRes where
  | yes : TmSubst → MatchRes
  | no : MatchRes
  | stuck : MatchRes

/-- Combine the outcomes of two independent matches. -/
def MatchRes.and : MatchRes → MatchRes → MatchRes
  | .no, _ => .no
  | _, .no => .no
  | .yes σ₁, .yes σ₂ => .yes (σ₁ ++ σ₂)
  | _, _ => .stuck

/-- Match a pattern against a term. A mismatch is definite only between distinct
introduction forms. -/
def matchPat : Pat → Tm → MatchRes
  | .var x, t => .yes [(x, t)]
  | .unit, .unit => .yes []
  | .unit, .pair _ _ => .no
  | .unit, .cons _ _ => .no
  | .unit, .pack _ => .no
  | .unit, _ => .stuck
  | .pair p q, .pair t u => (matchPat p t).and (matchPat q u)
  | .pair _ _, .unit => .no
  | .pair _ _, .cons _ _ => .no
  | .pair _ _, .pack _ => .no
  | .pair _ _, _ => .stuck
  | .cons c p, .cons c' t => if c = c' then matchPat p t else .no
  | .cons _ _, .unit => .no
  | .cons _ _, .pair _ _ => .no
  | .cons _ _, .pack _ => .no
  | .cons _ _, _ => .stuck
  | .pack p, .pack t => matchPat p t
  | .pack _, .unit => .no
  | .pack _, .pair _ _ => .no
  | .pack _, .cons _ _ => .no
  | .pack _, _ => .stuck

def matchCopat : Copat → Elim → MatchRes
  | .pat p, .term t => matchPat p t
  | .pat _, .proj _ => .no
  | .pat _, .inst => .no
  | .proj d, .proj d' => if d = d' then .yes [] else .no
  | .proj _, .term _ => .no
  | .proj _, .inst => .no
  | .inst, .inst => .yes []
  | .inst, .term _ => .no
  | .inst, .proj _ => .no

/-- Match a copattern spine against a prefix of an elimination spine. -/
def matchSpine : List Copat → List Elim → MatchRes
  | [], _ => .yes []
  | _ :: _, [] => .stuck
  | q :: qs, e :: es => (matchCopat q e).and (matchSpine qs es)

/-- First-match clause selection; returns the contractum. -/
def selectClause : List Clause → List Elim → Option Tm
  | [], _ => none
  | .mk qs t :: D, es =>
      match matchSpine qs es with
      | .yes σ => some (Tm.appSpine (t.subst σ) (es.drop qs.length))
      | .no => selectClause D es
      | .stuck => none

/-- Split a term into its head and its elimination spine. -/
def Tm.headSpine : Tm → Tm × List Elim
  | .app r e => ((r.headSpine).1, (r.headSpine).2 ++ [e])
  | t => (t, [])

/-- A world: all function declarations in scope at run time. -/
abbrev World := List FunDecl

def World.lookup (W : World) (f : FunName) : Option FunDecl :=
  W.find? (fun d => d.name == f)

/-- Deterministic weak-head step. -/
def headStep (W : World) (t : Tm) : Option Tm :=
  match t.headSpine.1 with
  | .lam D => selectClause D t.headSpine.2
  | .fn f =>
      match W.lookup f with
      | some d => selectClause d.clauses t.headSpine.2
      | none => none
  | _ => none

/-- Weak reduction: head steps and congruences, never under `λ{D⃗}`. -/
inductive Step (W : World) : Tm → Tm → Prop where
  | head {t u : Tm} : headStep W t = some u → Step W t u
  | appFun {r r' : Tm} {e : Elim} : Step W r r' → Step W (.app r e) (.app r' e)
  | appArg {r s s' : Tm} : Step W s s' → Step W (.app r (.term s)) (.app r (.term s'))
  | pairL {t t' u : Tm} : Step W t t' → Step W (.pair t u) (.pair t' u)
  | pairR {t u u' : Tm} : Step W u u' → Step W (.pair t u) (.pair t u')
  | cons {c : Nat} {t t' : Tm} : Step W t t' → Step W (.cons c t) (.cons c t')
  | pack {t t' : Tm} : Step W t t' → Step W (.pack t) (.pack t')

/-- Reflexive-transitive closure of `Step`. -/
def Steps (W : World) : Tm → Tm → Prop := Relation.ReflTransGen (Step W)

/-- Strong normalization: every reduction sequence from `t` is finite. -/
def SN (W : World) (t : Tm) : Prop := Acc (fun u t => Step W t u) t

/-- Closed and strongly normalizing. -/
def SNc (W : World) (t : Tm) : Prop := t.Closed ∧ SN W t

/-- Introduction forms. -/
def IsIntro : Tm → Prop
  | .unit => True
  | .pair _ _ => True
  | .cons _ _ => True
  | .pack _ => True
  | _ => False

/-- Neutral terms: not an introduction, and every head step of an extension `t e⃗` comes from a
head step of `t` itself. -/
def IsNeutral (W : World) (t : Tm) : Prop :=
  ¬ IsIntro t ∧
  ∀ (es : List Elim) (u : Tm), headStep W (Tm.appSpine t es) = some u →
    ∃ t', headStep W t = some t' ∧ u = Tm.appSpine t' es

/-- Reducibility candidates over closed strongly normalizing terms. -/
structure Cand (W : World) (𝒜 : Set Tm) : Prop where
  sn : ∀ t ∈ 𝒜, SNc W t
  red : ∀ t ∈ 𝒜, ∀ t', Step W t t' → t' ∈ 𝒜
  neutral : ∀ t, t.Closed → IsNeutral W t → (∀ t', Step W t t' → t' ∈ 𝒜) → t ∈ 𝒜

/-! ## Sizes -/

/-- The interpretation of `∞`: the initial ordinal of the successor cardinal of `#Tm`. -/
noncomputable def Omega : Ordinal.{0} := (Order.succ (Cardinal.mk Tm)).ord

/-- Valuation of free size variables. -/
abbrev SizeVal := Nat → Ordinal.{0}

/-- Valuation of bound size variables. -/
abbrev SzEnv := Nat → Ordinal.{0}

def SzEnv.cons (β : Ordinal.{0}) (ζ : SzEnv) : SzEnv
  | 0 => β
  | n + 1 => ζ n

def SzEnv.zero : SzEnv := fun _ => 0

/-- `⟦a⟧ρζ`. -/
noncomputable def sizeVal (ρ : SizeVal) (ζ : SzEnv) : Size → Ordinal.{0}
  | .inf => Omega
  | .var i n => ρ i + n
  | .bvar k n => ζ k + n

/-- `ρ ∈ ⟦Ψ⟧`: every declared variable is below its bound and below `Ω`. -/
def ValidVal (Ψ : SizeCtx) (ρ : SizeVal) : Prop :=
  ∀ p ∈ Ψ, ρ p.1 < sizeVal ρ SzEnv.zero p.2 ∧ ρ p.1 < Omega

/-! ## Semantic types -/

/-- Closed strongly normalizing terms all of whose introduction-form reducts satisfy `P`. -/
def IntroSet (W : World) (P : Tm → Prop) : Set Tm :=
  {t | SNc W t ∧ ∀ v, Steps W t v → IsIntro v → P v}

def UnitSet (W : World) : Set Tm := IntroSet W (fun v => v = .unit)

def ProdSet (W : World) (𝒜 ℬ : Set Tm) : Set Tm :=
  IntroSet W (fun v => ∃ t u, v = .pair t u ∧ t ∈ 𝒜 ∧ u ∈ ℬ)

def ArrSet (W : World) (𝒜 ℬ : Set Tm) : Set Tm :=
  {t | SNc W t ∧ ∀ s ∈ 𝒜, Tm.app t (.term s) ∈ ℬ}

/-- `∀X. F X`: instantiations land in `F 𝒳` for every candidate `𝒳`. -/
def AllTSet (W : World) (F : Set Tm → Set Tm) : Set Tm :=
  {t | SNc W t ∧ ∀ 𝒳, Cand W 𝒳 → Tm.app t .inst ∈ F 𝒳}

/-- `∃X. F X`: packs of a member of `F 𝒳` for some candidate `𝒳`. -/
def ExTSet (W : World) (F : Set Tm → Set Tm) : Set Tm :=
  IntroSet W (fun v => ∃ t 𝒳, v = .pack t ∧ Cand W 𝒳 ∧ t ∈ F 𝒳)

/-- `∀(j < α). F j`: instantiations land in `F β` for every `β < α`. -/
def AllSSet (W : World) (α : Ordinal.{0}) (F : Ordinal.{0} → Set Tm) : Set Tm :=
  {t | SNc W t ∧ ∀ β < α, Tm.app t .inst ∈ F β}

/-- `∃(j < α). F j`: packs of a member of `F β` for some `β < α`. -/
def ExSSet (W : World) (α : Ordinal.{0}) (F : Ordinal.{0} → Set Tm) : Set Tm :=
  IntroSet W (fun v => ∃ t β, v = .pack t ∧ β < α ∧ t ∈ F β)

/-- Stage `α` of an inductive type with branch interpretation `F`. -/
noncomputable def MuSet (W : World) (F : Nat → Set Tm → Set Tm) : Ordinal.{0} → Set Tm :=
  WellFounded.fix Ordinal.lt_wf (C := fun _ => Set Tm) fun α ih =>
    IntroSet W (fun v => ∃ c t β, ∃ h : β < α, v = .cons c t ∧ t ∈ F c (ih β h))

/-- Stage `α` of a coinductive type with `n` projections interpreted by `G`. -/
noncomputable def NuSet (W : World) (n : Nat) (G : Nat → Set Tm → Set Tm) :
    Ordinal.{0} → Set Tm :=
  WellFounded.fix Ordinal.lt_wf (C := fun _ => Set Tm) fun α ih =>
    {t | SNc W t ∧ ∀ β (h : β < α), ∀ d < n, Tm.app t (.proj d) ∈ G d (ih β h)}

/-- Environment for bound type variables. -/
abbrev Env := Nat → Set Tm

def Env.cons (𝒳 : Set Tm) (η : Env) : Env
  | 0 => 𝒳
  | n + 1 => η n

def Env.empty : Env := fun _ => ∅

/-- Valuation of free type variables. -/
abbrev TEnv := Nat → Set Tm

def TEnv.empty : TEnv := fun _ => ∅

mutual

/-- `⟦A⟧ρθζη`: `ρ` and `θ` interpret free size and type variables, `ζ` and `η` bound ones. -/
noncomputable def interp (W : World) (ρ : SizeVal) (θ : TEnv) : Ty → SzEnv → Env → Set Tm
  | .unit, _, _ => UnitSet W
  | .prod A B, ζ, η => ProdSet W (interp W ρ θ A ζ η) (interp W ρ θ B ζ η)
  | .arr A B, ζ, η => ArrSet W (interp W ρ θ A ζ η) (interp W ρ θ B ζ η)
  | .var X, _, η => η X
  | .fvar X, _, _ => θ X
  | .mu a S, ζ, η =>
      MuSet W (fun c 𝒳 => interpAt W ρ θ S c ζ (Env.cons 𝒳 η)) (sizeVal ρ ζ a)
  | .nu a R, ζ, η =>
      NuSet W R.length (fun d 𝒳 => interpAt W ρ θ R d ζ (Env.cons 𝒳 η)) (sizeVal ρ ζ a)
  | .allT B, ζ, η => AllTSet W (fun 𝒳 => interp W ρ θ B ζ (Env.cons 𝒳 η))
  | .exT B, ζ, η => ExTSet W (fun 𝒳 => interp W ρ θ B ζ (Env.cons 𝒳 η))
  | .allS a B, ζ, η => AllSSet W (sizeVal ρ ζ a) (fun β => interp W ρ θ B (SzEnv.cons β ζ) η)
  | .exS a B, ζ, η => ExSSet W (sizeVal ρ ζ a) (fun β => interp W ρ θ B (SzEnv.cons β ζ) η)

/-- `⟦S[c]⟧`, empty when `c` is out of range. -/
noncomputable def interpAt (W : World) (ρ : SizeVal) (θ : TEnv) :
    List Ty → Nat → SzEnv → Env → Set Tm
  | [], _, _, _ => ∅
  | A :: _, 0, ζ, η => interp W ρ θ A ζ η
  | _ :: S, c + 1, ζ, η => interpAt W ρ θ S c ζ η

end

/-- `W ⊨ D`: every declaration in `D`, at every valid size instance, is in its type. -/
def SemValid (W : World) (D : List FunDecl) : Prop :=
  ∀ d ∈ D, ∀ ρ : SizeVal, ValidVal d.sizeParams ρ →
    Tm.fn d.name ∈ interp W ρ TEnv.empty d.ty SzEnv.zero Env.empty

end NishtAbel2024V4
