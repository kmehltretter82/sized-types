import Definitions.Def_NishtAbel2024V2_Syntax

/-!
# Nisht & Abel (2024), V4: syntax and typing

V4 extends the V3 calculus with type polymorphism and bounded size quantification inside types:

* `∀X. B` and `∃X. B` over types (impredicative), and `∀(j < a). B` and `∃(j < a). B` over sizes.
  Universal types are eliminated by an explicit instantiation `r ·` and introduced by the
  copattern `·`. Existential types are introduced by `pack t` and eliminated by the pattern
  `pack p`, as in the thesis (with the type or size witness erased at run time).
* Binding is locally nameless. Bound type and size variables are de Bruijn indices. Free type and
  size variables, introduced by copatterns and patterns, are names. Substituting for a name never
  captures, and opening a binder substitutes a locally closed type or size.

Everything else is as in V3: no type operators, positive functors, sizes `∞ | i + n`, Curry-style
sizes in typing derivations, named term variables with closed-term semantics, first-match clauses.
The invocation graphs and `SCTValid` are reused unchanged from `NishtAbel2024V2`.
-/

namespace NishtAbel2024V4

open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid ConformsToGraph FunName)

/-! ## Sizes -/

/-- Size expressions `∞`, `i + n` for a free size variable `i`, and `k + n` for a bound size
variable with de Bruijn index `k`. -/
inductive Size where
  | inf : Size
  | var (i : Nat) (n : Nat) : Size
  | bvar (k : Nat) (n : Nat) : Size
  deriving DecidableEq, Repr

namespace Size

/-- `a ⊕ n`, with `∞ ⊕ n = ∞`. -/
def shift : Size → Nat → Size
  | inf, _ => inf
  | var i m, n => var i (m + n)
  | bvar k m, n => bvar k (m + n)

/-- Simultaneous substitution of sizes for free size variables. -/
def subst (σ : List (Nat × Size)) : Size → Size
  | inf => inf
  | var i n =>
      match σ.lookup i with
      | some b => b.shift n
      | none => var i n
  | bvar k n => bvar k n

/-- `a.openAt k b`: replace the bound size variable `k` in `a` by the locally closed size `b`,
lowering the bound variables above `k`. -/
def openAt : Size → Nat → Size → Size
  | inf, _, _ => inf
  | var i n, _, _ => var i n
  | bvar k' n, k, b => if k' = k then b.shift n else if k < k' then bvar (k' - 1) n else bvar k' n

end Size

/-- Size context `Ψ`: an entry `(i, a)` declares the free size variable `i` with `i < a`. -/
abbrev SizeCtx := List (Nat × Size)

def SizeCtx.dom (Ψ : SizeCtx) : List Nat := Ψ.map Prod.fst

/-- `Ψ; m ⊢ a`: free size variables declared in `Ψ`, bound size variables below `m`. -/
def SizeWfAt (Ψ : SizeCtx) (m : Nat) : Size → Prop
  | .inf => True
  | .var i _ => i ∈ Ψ.dom
  | .bvar k _ => k < m

/-- `Ψ ⊢ a` for locally closed sizes. -/
abbrev SizeWf (Ψ : SizeCtx) : Size → Prop := SizeWfAt Ψ 0

/-- `⊢ Ψ`: distinct variables, each bound only by earlier variables or `∞`. -/
inductive SizeCtxWf : SizeCtx → Prop where
  | nil : SizeCtxWf []
  | snoc {Ψ : SizeCtx} {i : Nat} {a : Size} :
      SizeCtxWf Ψ → i ∉ Ψ.dom → SizeWf Ψ a → SizeCtxWf (Ψ ++ [(i, a)])

/-- Strict size comparison `Ψ ⊢ a < b` on locally closed sizes. -/
inductive SizeLt (Ψ : SizeCtx) : Size → Size → Prop where
  | var_var {i n m : Nat} : i ∈ Ψ.dom → n < m → SizeLt Ψ (.var i n) (.var i m)
  | var_inf {i n : Nat} : i ∈ Ψ.dom → SizeLt Ψ (.var i n) .inf
  | bound {i n : Nat} {a : Size} : (i, a) ∈ Ψ → SizeLt Ψ (.var i n) (a.shift n)
  | trans {a b c : Size} : SizeLt Ψ a b → SizeLt Ψ b c → SizeLt Ψ a c

/-- Non-strict size comparison `Ψ ⊢ a ≤ b`. -/
def SizeLe (Ψ : SizeCtx) (a b : Size) : Prop :=
  (a = b ∧ SizeWf Ψ a) ∨ (b = .inf ∧ SizeWf Ψ a) ∨ SizeLt Ψ a b ∨
  (∃ i n m, a = .var i n ∧ b = .var i m ∧ n ≤ m ∧ i ∈ Ψ.dom)

/-- `Ψ ⊢ b < a^↑`: `b < a`, or `a = b = ∞`. -/
def SizeBelow (Ψ : SizeCtx) (b a : Size) : Prop :=
  SizeLt Ψ b a ∨ (b = .inf ∧ a = .inf)

/-- `Ψ ⊢ a⃗ ⇐ Ψ'`: well-formed instantiation of the size parameters `Ψ'` of a callee. -/
def SizeSubstWf (Ψ : SizeCtx) (as : List Size) (Ψ' : SizeCtx) : Prop :=
  as.length = Ψ'.length ∧
  ∀ (k : Nat) (hk : k < Ψ'.length) (ha : k < as.length),
    SizeLt Ψ (as[k]'ha) ((Ψ'[k]'hk).2.subst (Ψ'.dom.zip as))

/-! ## Types -/

/-- Types. `var k` is a bound type variable (bound by `μ`, `ν`, `∀X`, `∃X`), `fvar X` a free one.
`allS a B` is `∀(j < a). B` and `exS a B` is `∃(j < a). B`, binding the size index `0` in `B`;
the bound `a` lies outside the binder. -/
inductive Ty where
  | unit : Ty
  | prod : Ty → Ty → Ty
  | arr : Ty → Ty → Ty
  | var : Nat → Ty
  | fvar : Nat → Ty
  | mu : Size → List Ty → Ty
  | nu : Size → List Ty → Ty
  | allT : Ty → Ty
  | exT : Ty → Ty
  | allS : Size → Ty → Ty
  | exS : Size → Ty → Ty
  deriving Repr

mutual

/-- Substitute sizes for free size variables. -/
def Ty.substSize (σ : List (Nat × Size)) : Ty → Ty
  | .unit => .unit
  | .prod A B => .prod (A.substSize σ) (B.substSize σ)
  | .arr A B => .arr (A.substSize σ) (B.substSize σ)
  | .var X => .var X
  | .fvar X => .fvar X
  | .mu a S => .mu (a.subst σ) (Ty.substSizeList σ S)
  | .nu a R => .nu (a.subst σ) (Ty.substSizeList σ R)
  | .allT B => .allT (B.substSize σ)
  | .exT B => .exT (B.substSize σ)
  | .allS a B => .allS (a.subst σ) (B.substSize σ)
  | .exS a B => .exS (a.subst σ) (B.substSize σ)

def Ty.substSizeList (σ : List (Nat × Size)) : List Ty → List Ty
  | [] => []
  | A :: S => A.substSize σ :: Ty.substSizeList σ S

end

mutual

/-- `A.substTy k T`: replace the bound type variable `k` by the locally closed type `T`,
lowering the bound type variables above `k`. -/
def Ty.substTy : Ty → Nat → Ty → Ty
  | .unit, _, _ => .unit
  | .prod A B, k, T => .prod (A.substTy k T) (B.substTy k T)
  | .arr A B, k, T => .arr (A.substTy k T) (B.substTy k T)
  | .var X, k, T => if X = k then T else if k < X then .var (X - 1) else .var X
  | .fvar X, _, _ => .fvar X
  | .mu a S, k, T => .mu a (Ty.substTyList S (k + 1) T)
  | .nu a R, k, T => .nu a (Ty.substTyList R (k + 1) T)
  | .allT B, k, T => .allT (B.substTy (k + 1) T)
  | .exT B, k, T => .exT (B.substTy (k + 1) T)
  | .allS a B, k, T => .allS a (B.substTy k T)
  | .exS a B, k, T => .exS a (B.substTy k T)

def Ty.substTyList : List Ty → Nat → Ty → List Ty
  | [], _, _ => []
  | A :: S, k, T => A.substTy k T :: Ty.substTyList S k T

end

mutual

/-- `A.openSz k b`: replace the bound size variable `k` by the locally closed size `b`. -/
def Ty.openSz : Ty → Nat → Size → Ty
  | .unit, _, _ => .unit
  | .prod A B, k, b => .prod (A.openSz k b) (B.openSz k b)
  | .arr A B, k, b => .arr (A.openSz k b) (B.openSz k b)
  | .var X, _, _ => .var X
  | .fvar X, _, _ => .fvar X
  | .mu a S, k, b => .mu (a.openAt k b) (Ty.openSzList S k b)
  | .nu a R, k, b => .nu (a.openAt k b) (Ty.openSzList R k b)
  | .allT B, k, b => .allT (B.openSz k b)
  | .exT B, k, b => .exT (B.openSz k b)
  | .allS a B, k, b => .allS (a.openAt k b) (B.openSz (k + 1) b)
  | .exS a B, k, b => .exS (a.openAt k b) (B.openSz (k + 1) b)

def Ty.openSzList : List Ty → Nat → Size → List Ty
  | [], _, _ => []
  | A :: S, k, b => A.openSz k b :: Ty.openSzList S k b

end

mutual

/-- Substitute locally closed types for free type variables. -/
def Ty.substFTy (τ : List (Nat × Ty)) : Ty → Ty
  | .unit => .unit
  | .prod A B => .prod (A.substFTy τ) (B.substFTy τ)
  | .arr A B => .arr (A.substFTy τ) (B.substFTy τ)
  | .var X => .var X
  | .fvar X => (τ.lookup X).getD (.fvar X)
  | .mu a S => .mu a (Ty.substFTyList τ S)
  | .nu a R => .nu a (Ty.substFTyList τ R)
  | .allT B => .allT (B.substFTy τ)
  | .exT B => .exT (B.substFTy τ)
  | .allS a B => .allS a (B.substFTy τ)
  | .exS a B => .exS a (B.substFTy τ)

def Ty.substFTyList (τ : List (Nat × Ty)) : List Ty → List Ty
  | [] => []
  | A :: S => A.substFTy τ :: Ty.substFTyList τ S

end

/-- `PolIn b k A`: the bound type variable `k` occurs in `A` only positively (`b = true`) or only
negatively (`b = false`). -/
inductive PolIn : Bool → Nat → Ty → Prop where
  | unit (b : Bool) (k : Nat) : PolIn b k .unit
  | prod {b : Bool} {k : Nat} {A B : Ty} : PolIn b k A → PolIn b k B → PolIn b k (.prod A B)
  | arr {b : Bool} {k : Nat} {A B : Ty} : PolIn (!b) k A → PolIn b k B → PolIn b k (.arr A B)
  | var_self (k : Nat) : PolIn true k (.var k)
  | var_other {b : Bool} {k X : Nat} : X ≠ k → PolIn b k (.var X)
  | fvar (b : Bool) (k X : Nat) : PolIn b k (.fvar X)
  | mu {b : Bool} {k : Nat} {a : Size} {S : List Ty} :
      (∀ T ∈ S, PolIn b (k + 1) T) → PolIn b k (.mu a S)
  | nu {b : Bool} {k : Nat} {a : Size} {R : List Ty} :
      (∀ T ∈ R, PolIn b (k + 1) T) → PolIn b k (.nu a R)
  | allT {b : Bool} {k : Nat} {B : Ty} : PolIn b (k + 1) B → PolIn b k (.allT B)
  | exT {b : Bool} {k : Nat} {B : Ty} : PolIn b (k + 1) B → PolIn b k (.exT B)
  | allS {b : Bool} {k : Nat} {a : Size} {B : Ty} : PolIn b k B → PolIn b k (.allS a B)
  | exS {b : Bool} {k : Nat} {a : Size} {B : Ty} : PolIn b k B → PolIn b k (.exS a B)

/-- `Ψ; Θ; k; m ⊢ A`: free sizes in `Ψ`, free type variables in `Θ`, bound type variables
below `k`, bound size variables below `m`, and every `μ`/`ν` functor positive in its recursion
variable. Locally closed types are those with `k = m = 0`. -/
inductive TyWf (Ψ : SizeCtx) (Θ : List Nat) : Nat → Nat → Ty → Prop where
  | unit (k m : Nat) : TyWf Ψ Θ k m .unit
  | prod {k m : Nat} {A B : Ty} : TyWf Ψ Θ k m A → TyWf Ψ Θ k m B → TyWf Ψ Θ k m (.prod A B)
  | arr {k m : Nat} {A B : Ty} : TyWf Ψ Θ k m A → TyWf Ψ Θ k m B → TyWf Ψ Θ k m (.arr A B)
  | var {k m X : Nat} : X < k → TyWf Ψ Θ k m (.var X)
  | fvar {k m X : Nat} : X ∈ Θ → TyWf Ψ Θ k m (.fvar X)
  | mu {k m : Nat} {a : Size} {S : List Ty} :
      SizeWfAt Ψ m a → (∀ T ∈ S, TyWf Ψ Θ (k + 1) m T) → (∀ T ∈ S, PolIn true 0 T) →
      TyWf Ψ Θ k m (.mu a S)
  | nu {k m : Nat} {a : Size} {R : List Ty} :
      SizeWfAt Ψ m a → (∀ T ∈ R, TyWf Ψ Θ (k + 1) m T) → (∀ T ∈ R, PolIn true 0 T) →
      TyWf Ψ Θ k m (.nu a R)
  | allT {k m : Nat} {B : Ty} : TyWf Ψ Θ (k + 1) m B → TyWf Ψ Θ k m (.allT B)
  | exT {k m : Nat} {B : Ty} : TyWf Ψ Θ (k + 1) m B → TyWf Ψ Θ k m (.exT B)
  | allS {k m : Nat} {a : Size} {B : Ty} :
      SizeWfAt Ψ m a → TyWf Ψ Θ k (m + 1) B → TyWf Ψ Θ k m (.allS a B)
  | exS {k m : Nat} {a : Size} {B : Ty} :
      SizeWfAt Ψ m a → TyWf Ψ Θ k (m + 1) B → TyWf Ψ Θ k m (.exS a B)

/-- Subtyping: monotone in the sizes of `μ`, antitone in the sizes of `ν`. -/
inductive SubTy (Ψ : SizeCtx) : Ty → Ty → Prop where
  | refl (A : Ty) : SubTy Ψ A A
  | prod {A A' B B' : Ty} : SubTy Ψ A A' → SubTy Ψ B B' → SubTy Ψ (.prod A B) (.prod A' B')
  | arr {A A' B B' : Ty} : SubTy Ψ A' A → SubTy Ψ B B' → SubTy Ψ (.arr A B) (.arr A' B')
  | mu {a b : Size} {S : List Ty} : SizeLe Ψ a b → SubTy Ψ (.mu a S) (.mu b S)
  | nu {a b : Size} {R : List Ty} : SizeLe Ψ b a → SubTy Ψ (.nu a R) (.nu b R)
  | trans {A B C : Ty} : SubTy Ψ A B → SubTy Ψ B C → SubTy Ψ A C

/-! ## Terms -/

/-- Patterns `p ::= x | () | (p, p) | c p | pack p`. -/
inductive Pat where
  | var : Nat → Pat
  | unit : Pat
  | pair : Pat → Pat → Pat
  | cons : Nat → Pat → Pat
  | pack : Pat → Pat
  deriving DecidableEq, Repr

/-- Copatterns: a pattern for an argument, a projection `.d`, or `·` for an instantiation. -/
inductive Copat where
  | pat : Pat → Copat
  | proj : Nat → Copat
  | inst : Copat
  deriving DecidableEq, Repr

def Pat.vars : Pat → List Nat
  | .var x => [x]
  | .unit => []
  | .pair p q => p.vars ++ q.vars
  | .cons _ p => p.vars
  | .pack p => p.vars

def Copat.vars : Copat → List Nat
  | .pat p => p.vars
  | .proj _ => []
  | .inst => []

def spineVars (qs : List Copat) : List Nat := qs.flatMap Copat.vars

mutual

/-- Runtime terms. -/
inductive Tm where
  | var : Nat → Tm
  | fn : FunName → Tm
  | app : Tm → Elim → Tm
  | unit : Tm
  | pair : Tm → Tm → Tm
  | cons : Nat → Tm → Tm
  | pack : Tm → Tm
  | lam : List Clause → Tm

/-- Eliminations: an argument, a projection, or an instantiation `·`. -/
inductive Elim where
  | term : Tm → Elim
  | proj : Nat → Elim
  | inst : Elim

/-- A clause `{q⃗ → t}`. -/
inductive Clause where
  | mk : List Copat → Tm → Clause

end

namespace Tm

/-- `r e⃗`. -/
def appSpine (r : Tm) (es : List Elim) : Tm := es.foldl .app r

end Tm

/-- Term substitution: an association list, looked up from the front. -/
abbrev TmSubst := List (Nat × Tm)

mutual

/-- Free term variables. -/
def Tm.fv : Tm → List Nat
  | .var x => [x]
  | .fn _ => []
  | .app r e => r.fv ++ e.fv
  | .unit => []
  | .pair t u => t.fv ++ u.fv
  | .cons _ t => t.fv
  | .pack t => t.fv
  | .lam D => Clause.fvList D

def Elim.fv : Elim → List Nat
  | .term t => t.fv
  | .proj _ => []
  | .inst => []

def Clause.fvList : List Clause → List Nat
  | [] => []
  | .mk qs t :: D => t.fv.filter (fun x => x ∉ spineVars qs) ++ Clause.fvList D

end

/-- A closed term has no free term variables. -/
def Tm.Closed (t : Tm) : Prop := t.fv = []

mutual

/-- Substitution. Binders filter the substitution but are never renamed; the semantics only
substitutes closed terms. -/
def Tm.subst (σ : TmSubst) : Tm → Tm
  | .var x => (σ.lookup x).getD (.var x)
  | .fn f => .fn f
  | .app r e => .app (r.subst σ) (e.subst σ)
  | .unit => .unit
  | .pair t u => .pair (t.subst σ) (u.subst σ)
  | .cons c t => .cons c (t.subst σ)
  | .pack t => .pack (t.subst σ)
  | .lam D => .lam (Clause.substList σ D)

def Elim.subst (σ : TmSubst) : Elim → Elim
  | .term t => .term (t.subst σ)
  | .proj d => .proj d
  | .inst => .inst

def Clause.substList (σ : TmSubst) : List Clause → List Clause
  | [] => []
  | .mk qs t :: D =>
      .mk qs (t.subst (σ.filter (fun p => p.1 ∉ spineVars qs))) :: Clause.substList σ D

end

/-! ## Typing -/

/-- Term context: looked up from the front. -/
abbrev TermCtx := List (Nat × Ty)

/-- Function declaration `f : ∀Ψ. A = D⃗`; `A` is locally closed with no free type variables. -/
structure FunDecl where
  name : FunName
  sizeParams : SizeCtx
  ty : Ty
  clauses : List Clause

/-- Pattern typing `Ψ; Θ ⊢ p : A ⇒ Γ; Ψ'; Θ'`. Constructor patterns on `μ^a S` and pack patterns
on `∃(j < a)` bind a fresh size variable `j < a`; pack patterns on `∃X` bind a fresh type
variable. -/
inductive PatTy : SizeCtx → List Nat → Pat → Ty → TermCtx → SizeCtx → List Nat → Prop where
  | var (Ψ : SizeCtx) (Θ : List Nat) (x : Nat) (A : Ty) : PatTy Ψ Θ (.var x) A [(x, A)] [] []
  | unit (Ψ : SizeCtx) (Θ : List Nat) : PatTy Ψ Θ .unit .unit [] [] []
  | pair {Ψ Ψ₁ Ψ₂ : SizeCtx} {Θ Θ₁ Θ₂ : List Nat} {p q : Pat} {A B : Ty} {Γ₁ Γ₂ : TermCtx} :
      PatTy Ψ Θ p A Γ₁ Ψ₁ Θ₁ → PatTy (Ψ ++ Ψ₁) (Θ ++ Θ₁) q B Γ₂ Ψ₂ Θ₂ →
      PatTy Ψ Θ (.pair p q) (.prod A B) (Γ₁ ++ Γ₂) (Ψ₁ ++ Ψ₂) (Θ₁ ++ Θ₂)
  | cons {Ψ Ψ' : SizeCtx} {Θ Θ' : List Nat} {c j : Nat} {p : Pat} {a : Size} {S : List Ty}
      {Sc : Ty} {Γ : TermCtx} :
      S[c]? = some Sc → j ∉ Ψ.dom →
      PatTy (Ψ ++ [(j, a)]) Θ p (Sc.substTy 0 (.mu (.var j 0) S)) Γ Ψ' Θ' →
      PatTy Ψ Θ (.cons c p) (.mu a S) Γ ((j, a) :: Ψ') Θ'
  | packT {Ψ Ψ' : SizeCtx} {Θ Θ' : List Nat} {X : Nat} {p : Pat} {B : Ty} {Γ : TermCtx} :
      X ∉ Θ → PatTy Ψ (Θ ++ [X]) p (B.substTy 0 (.fvar X)) Γ Ψ' Θ' →
      PatTy Ψ Θ (.pack p) (.exT B) Γ Ψ' (X :: Θ')
  | packS {Ψ Ψ' : SizeCtx} {Θ Θ' : List Nat} {j : Nat} {p : Pat} {a : Size} {B : Ty}
      {Γ : TermCtx} :
      j ∉ Ψ.dom → PatTy (Ψ ++ [(j, a)]) Θ p (B.openSz 0 (.var j 0)) Γ Ψ' Θ' →
      PatTy Ψ Θ (.pack p) (.exS a B) Γ ((j, a) :: Ψ') Θ'

/-- Copattern spine typing `Ψ; Θ ⊢ q⃗ : A ⇒ Γ; Ψ'; Θ'; C`. -/
inductive SpineTy :
    SizeCtx → List Nat → List Copat → Ty → TermCtx → SizeCtx → List Nat → Ty → Prop where
  | nil (Ψ : SizeCtx) (Θ : List Nat) (A : Ty) : SpineTy Ψ Θ [] A [] [] [] A
  | pat {Ψ Ψ₁ Ψ₂ : SizeCtx} {Θ Θ₁ Θ₂ : List Nat} {p : Pat} {qs : List Copat} {A B C : Ty}
      {Γ₁ Γ₂ : TermCtx} :
      PatTy Ψ Θ p A Γ₁ Ψ₁ Θ₁ → SpineTy (Ψ ++ Ψ₁) (Θ ++ Θ₁) qs B Γ₂ Ψ₂ Θ₂ C →
      SpineTy Ψ Θ (.pat p :: qs) (.arr A B) (Γ₁ ++ Γ₂) (Ψ₁ ++ Ψ₂) (Θ₁ ++ Θ₂) C
  | proj {Ψ Ψ' : SizeCtx} {Θ Θ' : List Nat} {d j : Nat} {qs : List Copat} {a : Size}
      {R : List Ty} {Rd C : Ty} {Γ : TermCtx} :
      R[d]? = some Rd → j ∉ Ψ.dom →
      SpineTy (Ψ ++ [(j, a)]) Θ qs (Rd.substTy 0 (.nu (.var j 0) R)) Γ Ψ' Θ' C →
      SpineTy Ψ Θ (.proj d :: qs) (.nu a R) Γ ((j, a) :: Ψ') Θ' C
  | instT {Ψ Ψ' : SizeCtx} {Θ Θ' : List Nat} {X : Nat} {qs : List Copat} {B C : Ty}
      {Γ : TermCtx} :
      X ∉ Θ → SpineTy Ψ (Θ ++ [X]) qs (B.substTy 0 (.fvar X)) Γ Ψ' Θ' C →
      SpineTy Ψ Θ (.inst :: qs) (.allT B) Γ Ψ' (X :: Θ') C
  | instS {Ψ Ψ' : SizeCtx} {Θ Θ' : List Nat} {j : Nat} {qs : List Copat} {a : Size} {B C : Ty}
      {Γ : TermCtx} :
      j ∉ Ψ.dom → SpineTy (Ψ ++ [(j, a)]) Θ qs (B.openSz 0 (.var j 0)) Γ Ψ' Θ' C →
      SpineTy Ψ Θ (.inst :: qs) (.allS a B) Γ ((j, a) :: Ψ') Θ' C

/-- Typing environment: global signature, current block, invocation graphs, and the
enclosing top-level function with its size parameters. -/
structure TypingEnv where
  sig : List FunDecl
  block : List FunDecl
  graphs : InvGraphFamily
  caller : FunName
  callerParams : SizeCtx

mutual

/-- Curry-style expression typing `Ω; Ψ; Θ; Γ ⊢ t : A`. -/
inductive ExprTy (Ω : TypingEnv) : SizeCtx → List Nat → TermCtx → Tm → Ty → Prop where
  | var {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx} {x : Nat} {A : Ty} :
      Γ.lookup x = some A → ExprTy Ω Ψ Θ Γ (.var x) A
  | unit (Ψ : SizeCtx) (Θ : List Nat) (Γ : TermCtx) : ExprTy Ω Ψ Θ Γ .unit .unit
  | pair {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx} {t u : Tm} {A B : Ty} :
      ExprTy Ω Ψ Θ Γ t A → ExprTy Ω Ψ Θ Γ u B → ExprTy Ω Ψ Θ Γ (.pair t u) (.prod A B)
  | cons {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx} {c : Nat} {t : Tm} {a b : Size}
      {S : List Ty} {Sc : Ty} :
      S[c]? = some Sc → SizeBelow Ψ b a → TyWf Ψ Θ 0 0 (.mu a S) →
      ExprTy Ω Ψ Θ Γ t (Sc.substTy 0 (.mu b S)) → ExprTy Ω Ψ Θ Γ (.cons c t) (.mu a S)
  | app {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx} {r s : Tm} {A B : Ty} :
      ExprTy Ω Ψ Θ Γ r (.arr A B) → ExprTy Ω Ψ Θ Γ s A → ExprTy Ω Ψ Θ Γ (.app r (.term s)) B
  | proj {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx} {r : Tm} {a b : Size} {R : List Ty}
      {d : Nat} {Rd : Ty} :
      ExprTy Ω Ψ Θ Γ r (.nu a R) → R[d]? = some Rd → SizeBelow Ψ b a →
      ExprTy Ω Ψ Θ Γ (.app r (.proj d)) (Rd.substTy 0 (.nu b R))
  | instT {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx} {r : Tm} {B T : Ty} :
      ExprTy Ω Ψ Θ Γ r (.allT B) → TyWf Ψ Θ 0 0 T →
      ExprTy Ω Ψ Θ Γ (.app r .inst) (B.substTy 0 T)
  | instS {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx} {r : Tm} {a b : Size} {B : Ty} :
      ExprTy Ω Ψ Θ Γ r (.allS a B) → SizeLt Ψ b a →
      ExprTy Ω Ψ Θ Γ (.app r .inst) (B.openSz 0 b)
  | packT {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx} {t : Tm} {B T : Ty} :
      TyWf Ψ Θ 0 0 (.exT B) → TyWf Ψ Θ 0 0 T →
      ExprTy Ω Ψ Θ Γ t (B.substTy 0 T) → ExprTy Ω Ψ Θ Γ (.pack t) (.exT B)
  | packS {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx} {t : Tm} {a b : Size} {B : Ty} :
      TyWf Ψ Θ 0 0 (.exS a B) → SizeLt Ψ b a →
      ExprTy Ω Ψ Θ Γ t (B.openSz 0 b) → ExprTy Ω Ψ Θ Γ (.pack t) (.exS a B)
  | lam {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx} {D : List Clause} {A : Ty} :
      TyWf Ψ Θ 0 0 A → (∀ cl ∈ D, ClauseTy Ω Ψ Θ Γ cl A) → ExprTy Ω Ψ Θ Γ (.lam D) A
  | globalFun {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx} {g : FunDecl} {as : List Size} :
      g ∈ Ω.sig → SizeCtxWf g.sizeParams → TyWf g.sizeParams [] 0 0 g.ty →
      SizeSubstWf Ψ as g.sizeParams →
      TyWf Ψ Θ 0 0 (g.ty.substSize (g.sizeParams.dom.zip as)) →
      ExprTy Ω Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip as))
  | localFun {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx} {g : FunDecl} {as : List Size}
      {G : InvGraph} :
      g ∈ Ω.block → SizeCtxWf g.sizeParams → TyWf g.sizeParams [] 0 0 g.ty →
      SizeSubstWf Ψ as g.sizeParams →
      TyWf Ψ Θ 0 0 (g.ty.substSize (g.sizeParams.dom.zip as)) →
      G ∈ Ω.graphs.graphs Ω.caller g.name →
      ConformsToGraph (SizeLt Ψ) (SizeLe Ψ) G as
        (Ω.callerParams.map (fun p => Size.var p.1 0)) →
      ExprTy Ω Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip as))
  | sub {Ψ : SizeCtx} {Θ : List Nat} {Γ : TermCtx} {t : Tm} {A B : Ty} :
      ExprTy Ω Ψ Θ Γ t A → SubTy Ψ A B → TyWf Ψ Θ 0 0 B → ExprTy Ω Ψ Θ Γ t B

/-- Clause typing `Ω; Ψ; Θ; Γ ⊢ {q⃗ → t} : A`. Pattern variables shadow `Γ`. -/
inductive ClauseTy (Ω : TypingEnv) : SizeCtx → List Nat → TermCtx → Clause → Ty → Prop where
  | mk {Ψ Ψ' : SizeCtx} {Θ Θ' : List Nat} {Γ Γ' : TermCtx} {qs : List Copat} {t : Tm}
      {A C : Ty} :
      SpineTy Ψ Θ qs A Γ' Ψ' Θ' C → ExprTy Ω (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) t C →
      ClauseTy Ω Ψ Θ Γ (.mk qs t) A

end

/-- `Σ; Ξ; G ⊢ f : ∀Ψ. A = D⃗`. -/
def DeclTy (sig Ξ : List FunDecl) (𝒢 : InvGraphFamily) (d : FunDecl) : Prop :=
  SizeCtxWf d.sizeParams ∧ TyWf d.sizeParams [] 0 0 d.ty ∧
  ∀ cl ∈ d.clauses, ClauseTy ⟨sig, Ξ, 𝒢, d.name, d.sizeParams⟩ d.sizeParams [] [] cl d.ty

/-- `Σ ⊢ Ξ`: the block is typed with an invocation graph family satisfying SCT. -/
def BlockTy (sig Ξ : List FunDecl) : Prop :=
  ∃ 𝒢 : InvGraphFamily, SCTValid 𝒢 ∧
    (∀ d ∈ Ξ, 𝒢.arity d.name = d.sizeParams.length) ∧
    ∀ d ∈ Ξ, DeclTy sig Ξ 𝒢 d

/-- `⊢ Σ`: each block is typed against the blocks before it. -/
inductive BlocksTy : List (List FunDecl) → Prop where
  | nil : BlocksTy []
  | snoc {blocks : List (List FunDecl)} {Ξ : List FunDecl} :
      BlocksTy blocks → BlockTy blocks.flatten Ξ → BlocksTy (blocks ++ [Ξ])

/-- `⊢ (Σ; u) : A`: typed blocks with distinct names and a main term typed against all of them. -/
def ProgramTy (blocks : List (List FunDecl)) (main : Tm) (A : Ty) : Prop :=
  BlocksTy blocks ∧ (blocks.flatten.map FunDecl.name).Nodup ∧
  ExprTy ⟨blocks.flatten, [], ⟨fun _ => 0, fun _ _ => []⟩, 0, []⟩ [] [] [] main A

end NishtAbel2024V4
