import Definitions.Def_NishtAbel2024V2_Syntax

/-!
# Nisht & Abel (2024), V3: syntax and typing of the restricted calculus

V3 formalizes the soundness argument of Nisht's thesis for a restricted fragment of
System `F_ω^{cop, SCT}`. Compared with the V2 modules:

* There are no type operators, no type polymorphism and no kinds. Type variables are de Bruijn
  indices and occur only as the recursion variables of `μ`/`ν`. Every functor must be positive.
* Sizes are `∞` or `i + n`. The formal minimum and `∞ + n` are not used. Size variables occur only
  in types and contexts. Types contain no size binders, so size substitution cannot capture.
* Typing is Curry-style: runtime terms carry no sizes. Sized constructors `c^b t`, sized
  projections `r .d^b` and size arguments of calls are chosen in the typing derivation.
  Constructor and copattern spines bind size variables directly instead of through `∃`/`∀` types.
* Term variables are named. The semantics only ever substitutes closed terms, so substitution
  cannot capture.

The invocation graphs, their closure and the SCT criterion `SCTValid` are reused unchanged from
`NishtAbel2024V2`.
-/

namespace NishtAbel2024V3

open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid ConformsToGraph FunName)

/-! ## Sizes -/

/-- Size expressions `a ::= ∞ | i + n`. -/
inductive Size where
  | inf : Size
  | var (i : Nat) (n : Nat) : Size
  deriving DecidableEq, Repr

namespace Size

/-- `a ⊕ n`: add `n` to a size, with `∞ ⊕ n = ∞`. -/
def shift : Size → Nat → Size
  | inf, _ => inf
  | var i m, n => var i (m + n)

/-- Simultaneous substitution of sizes for size variables. -/
def subst (σ : List (Nat × Size)) : Size → Size
  | inf => inf
  | var i n =>
      match σ.lookup i with
      | some b => b.shift n
      | none => var i n

end Size

/-- Size context `Ψ`: an entry `(i, a)` declares the size variable `i` with `i < a`. -/
abbrev SizeCtx := List (Nat × Size)

def SizeCtx.dom (Ψ : SizeCtx) : List Nat := Ψ.map Prod.fst

/-- `Ψ ⊢ a`: every size variable of `a` is declared in `Ψ`. -/
def SizeWf (Ψ : SizeCtx) : Size → Prop
  | .inf => True
  | .var i _ => i ∈ Ψ.dom

/-- `⊢ Ψ`: distinct variables, each bound only by earlier variables or `∞`. -/
inductive SizeCtxWf : SizeCtx → Prop where
  | nil : SizeCtxWf []
  | snoc {Ψ : SizeCtx} {i : Nat} {a : Size} :
      SizeCtxWf Ψ → i ∉ Ψ.dom → SizeWf Ψ a → SizeCtxWf (Ψ ++ [(i, a)])

/-- Strict size comparison `Ψ ⊢ a < b`. -/
inductive SizeLt (Ψ : SizeCtx) : Size → Size → Prop where
  | var_var {i n m : Nat} : i ∈ Ψ.dom → n < m → SizeLt Ψ (.var i n) (.var i m)
  | var_inf {i n : Nat} : i ∈ Ψ.dom → SizeLt Ψ (.var i n) .inf
  | bound {i n : Nat} {a : Size} : (i, a) ∈ Ψ → SizeLt Ψ (.var i n) (a.shift n)
  | trans {a b c : Size} : SizeLt Ψ a b → SizeLt Ψ b c → SizeLt Ψ a c

/-- Non-strict size comparison `Ψ ⊢ a ≤ b`. -/
def SizeLe (Ψ : SizeCtx) (a b : Size) : Prop :=
  (a = b ∧ SizeWf Ψ a) ∨ (b = .inf ∧ SizeWf Ψ a) ∨ SizeLt Ψ a b ∨
  (∃ i n m, a = .var i n ∧ b = .var i m ∧ n ≤ m ∧ i ∈ Ψ.dom)

/-- `Ψ ⊢ b < a^↑`: the size `b` of a constructor or projection may annotate the fixpoint size `a`.
This means `b < a`, or `a = b = ∞` (since `μ^∞` and `ν^∞` are fixed points). -/
def SizeBelow (Ψ : SizeCtx) (b a : Size) : Prop :=
  SizeLt Ψ b a ∨ (b = .inf ∧ a = .inf)

/-- `Ψ ⊢ a⃗ ⇐ Ψ'`: well-formed instantiation of the size parameters `Ψ'` of a callee. -/
def SizeSubstWf (Ψ : SizeCtx) (as : List Size) (Ψ' : SizeCtx) : Prop :=
  as.length = Ψ'.length ∧
  ∀ (k : Nat) (hk : k < Ψ'.length) (ha : k < as.length),
    SizeLt Ψ (as[k]'ha) ((Ψ'[k]'hk).2.subst (Ψ'.dom.zip as))

/-! ## Types -/

/-- Types: unit, products, functions, de Bruijn type variables (recursion variables only),
sized inductive types `μ^a S` and sized coinductive types `ν^a R`. In `μ^a S` the `c`-th
constructor has payload type `S[c]`, in which variable `0` is the recursive occurrence; likewise
`R[d]` is the type of projection `d`. -/
inductive Ty where
  | unit : Ty
  | prod : Ty → Ty → Ty
  | arr : Ty → Ty → Ty
  | var : Nat → Ty
  | mu : Size → List Ty → Ty
  | nu : Size → List Ty → Ty
  deriving Repr

mutual

/-- Substitute sizes for size variables in a type. -/
def Ty.substSize (σ : List (Nat × Size)) : Ty → Ty
  | .unit => .unit
  | .prod A B => .prod (A.substSize σ) (B.substSize σ)
  | .arr A B => .arr (A.substSize σ) (B.substSize σ)
  | .var X => .var X
  | .mu a S => .mu (a.subst σ) (Ty.substSizeList σ S)
  | .nu a R => .nu (a.subst σ) (Ty.substSizeList σ R)

def Ty.substSizeList (σ : List (Nat × Size)) : List Ty → List Ty
  | [] => []
  | A :: S => A.substSize σ :: Ty.substSizeList σ S

end

mutual

/-- `A.substTy k T` is `A[T/k]` for a closed type `T`: replace variable `k` by `T` and lower the
variables above `k`. Since `T` is closed it needs no shifting under binders. -/
def Ty.substTy : Ty → Nat → Ty → Ty
  | .unit, _, _ => .unit
  | .prod A B, k, T => .prod (A.substTy k T) (B.substTy k T)
  | .arr A B, k, T => .arr (A.substTy k T) (B.substTy k T)
  | .var X, k, T => if X = k then T else if k < X then .var (X - 1) else .var X
  | .mu a S, k, T => .mu a (Ty.substTyList S (k + 1) T)
  | .nu a R, k, T => .nu a (Ty.substTyList R (k + 1) T)

def Ty.substTyList : List Ty → Nat → Ty → List Ty
  | [], _, _ => []
  | A :: S, k, T => A.substTy k T :: Ty.substTyList S k T

end

/-- `PolIn b k A`: type variable `k` occurs in `A` only positively (`b = true`) or only
negatively (`b = false`). -/
inductive PolIn : Bool → Nat → Ty → Prop where
  | unit (b : Bool) (k : Nat) : PolIn b k .unit
  | prod {b : Bool} {k : Nat} {A B : Ty} : PolIn b k A → PolIn b k B → PolIn b k (.prod A B)
  | arr {b : Bool} {k : Nat} {A B : Ty} : PolIn (!b) k A → PolIn b k B → PolIn b k (.arr A B)
  | var_self (k : Nat) : PolIn true k (.var k)
  | var_other {b : Bool} {k X : Nat} : X ≠ k → PolIn b k (.var X)
  | mu {b : Bool} {k : Nat} {a : Size} {S : List Ty} :
      (∀ T ∈ S, PolIn b (k + 1) T) → PolIn b k (.mu a S)
  | nu {b : Bool} {k : Nat} {a : Size} {R : List Ty} :
      (∀ T ∈ R, PolIn b (k + 1) T) → PolIn b k (.nu a R)

/-- `Ψ; k ⊢ A`: sizes declared in `Ψ`, type variables below `k`, and every `μ`/`ν` functor
positive in its recursion variable. -/
inductive TyWf (Ψ : SizeCtx) : Nat → Ty → Prop where
  | unit (k : Nat) : TyWf Ψ k .unit
  | prod {k : Nat} {A B : Ty} : TyWf Ψ k A → TyWf Ψ k B → TyWf Ψ k (.prod A B)
  | arr {k : Nat} {A B : Ty} : TyWf Ψ k A → TyWf Ψ k B → TyWf Ψ k (.arr A B)
  | var {k X : Nat} : X < k → TyWf Ψ k (.var X)
  | mu {k : Nat} {a : Size} {S : List Ty} :
      SizeWf Ψ a → (∀ T ∈ S, TyWf Ψ (k + 1) T) → (∀ T ∈ S, PolIn true 0 T) → TyWf Ψ k (.mu a S)
  | nu {k : Nat} {a : Size} {R : List Ty} :
      SizeWf Ψ a → (∀ T ∈ R, TyWf Ψ (k + 1) T) → (∀ T ∈ R, PolIn true 0 T) → TyWf Ψ k (.nu a R)

/-- Subtyping: monotone in the sizes of `μ`, antitone in the sizes of `ν`. -/
inductive SubTy (Ψ : SizeCtx) : Ty → Ty → Prop where
  | refl (A : Ty) : SubTy Ψ A A
  | prod {A A' B B' : Ty} : SubTy Ψ A A' → SubTy Ψ B B' → SubTy Ψ (.prod A B) (.prod A' B')
  | arr {A A' B B' : Ty} : SubTy Ψ A' A → SubTy Ψ B B' → SubTy Ψ (.arr A B) (.arr A' B')
  | mu {a b : Size} {S : List Ty} : SizeLe Ψ a b → SubTy Ψ (.mu a S) (.mu b S)
  | nu {a b : Size} {R : List Ty} : SizeLe Ψ b a → SubTy Ψ (.nu a R) (.nu b R)
  | trans {A B C : Ty} : SubTy Ψ A B → SubTy Ψ B C → SubTy Ψ A C

/-! ## Terms -/

/-- Patterns `p ::= x | () | (p, p) | c p`. -/
inductive Pat where
  | var : Nat → Pat
  | unit : Pat
  | pair : Pat → Pat → Pat
  | cons : Nat → Pat → Pat
  deriving DecidableEq, Repr

/-- Copatterns: a pattern for an argument, or a projection `.d`. -/
inductive Copat where
  | pat : Pat → Copat
  | proj : Nat → Copat
  deriving DecidableEq, Repr

def Pat.vars : Pat → List Nat
  | .var x => [x]
  | .unit => []
  | .pair p q => p.vars ++ q.vars
  | .cons _ p => p.vars

def Copat.vars : Copat → List Nat
  | .pat p => p.vars
  | .proj _ => []

def spineVars (qs : List Copat) : List Nat := qs.flatMap Copat.vars

mutual

/-- Runtime terms: variables, references to declared functions, application to an
elimination, unit, pairs, constructors, and copattern-matching abstractions `λ{D⃗}`. -/
inductive Tm where
  | var : Nat → Tm
  | fn : FunName → Tm
  | app : Tm → Elim → Tm
  | unit : Tm
  | pair : Tm → Tm → Tm
  | cons : Nat → Tm → Tm
  | lam : List Clause → Tm

/-- Eliminations: an argument or a projection. -/
inductive Elim where
  | term : Tm → Elim
  | proj : Nat → Elim

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
  | .lam D => Clause.fvList D

def Elim.fv : Elim → List Nat
  | .term t => t.fv
  | .proj _ => []

def Clause.fvList : List Clause → List Nat
  | [] => []
  | .mk qs t :: D => t.fv.filter (fun x => x ∉ spineVars qs) ++ Clause.fvList D

end

/-- A closed term has no free term variables. -/
def Tm.Closed (t : Tm) : Prop := t.fv = []

mutual

/-- Substitution. Binders filter the substitution but are never renamed. The semantics only
substitutes closed terms, for which this is capture-free. -/
def Tm.subst (σ : TmSubst) : Tm → Tm
  | .var x => (σ.lookup x).getD (.var x)
  | .fn f => .fn f
  | .app r e => .app (r.subst σ) (e.subst σ)
  | .unit => .unit
  | .pair t u => .pair (t.subst σ) (u.subst σ)
  | .cons c t => .cons c (t.subst σ)
  | .lam D => .lam (Clause.substList σ D)

def Elim.subst (σ : TmSubst) : Elim → Elim
  | .term t => .term (t.subst σ)
  | .proj d => .proj d

def Clause.substList (σ : TmSubst) : List Clause → List Clause
  | [] => []
  | .mk qs t :: D =>
      .mk qs (t.subst (σ.filter (fun p => p.1 ∉ spineVars qs))) :: Clause.substList σ D

end

/-! ## Typing -/

/-- Term context: looked up from the front, so later bindings are prepended. -/
abbrev TermCtx := List (Nat × Ty)

/-- Function declaration `f : ∀Ψ. A = D⃗`. -/
structure FunDecl where
  name : FunName
  sizeParams : SizeCtx
  ty : Ty
  clauses : List Clause

/-- Pattern typing `Ψ ⊢ p : A ⇒ Γ; Ψ'`. A constructor pattern on `μ^a S` binds a fresh size
variable `j < a`, appended to the size context. -/
inductive PatTy : SizeCtx → Pat → Ty → TermCtx → SizeCtx → Prop where
  | var (Ψ : SizeCtx) (x : Nat) (A : Ty) : PatTy Ψ (.var x) A [(x, A)] []
  | unit (Ψ : SizeCtx) : PatTy Ψ .unit .unit [] []
  | pair {Ψ Ψ₁ Ψ₂ : SizeCtx} {p q : Pat} {A B : Ty} {Γ₁ Γ₂ : TermCtx} :
      PatTy Ψ p A Γ₁ Ψ₁ → PatTy (Ψ ++ Ψ₁) q B Γ₂ Ψ₂ →
      PatTy Ψ (.pair p q) (.prod A B) (Γ₁ ++ Γ₂) (Ψ₁ ++ Ψ₂)
  | cons {Ψ Ψ' : SizeCtx} {c j : Nat} {p : Pat} {a : Size} {S : List Ty} {Sc : Ty} {Γ : TermCtx} :
      S[c]? = some Sc → j ∉ Ψ.dom →
      PatTy (Ψ ++ [(j, a)]) p (Sc.substTy 0 (.mu (.var j 0) S)) Γ Ψ' →
      PatTy Ψ (.cons c p) (.mu a S) Γ ((j, a) :: Ψ')

/-- Copattern spine typing `Ψ ⊢ q⃗ : A ⇒ Γ; Ψ'; C`. A projection copattern on `ν^a R` binds a
fresh size variable `j < a`. -/
inductive SpineTy : SizeCtx → List Copat → Ty → TermCtx → SizeCtx → Ty → Prop where
  | nil (Ψ : SizeCtx) (A : Ty) : SpineTy Ψ [] A [] [] A
  | pat {Ψ Ψ₁ Ψ₂ : SizeCtx} {p : Pat} {qs : List Copat} {A B C : Ty} {Γ₁ Γ₂ : TermCtx} :
      PatTy Ψ p A Γ₁ Ψ₁ → SpineTy (Ψ ++ Ψ₁) qs B Γ₂ Ψ₂ C →
      SpineTy Ψ (.pat p :: qs) (.arr A B) (Γ₁ ++ Γ₂) (Ψ₁ ++ Ψ₂) C
  | proj {Ψ Ψ' : SizeCtx} {d j : Nat} {qs : List Copat} {a : Size} {R : List Ty} {Rd C : Ty}
      {Γ : TermCtx} :
      R[d]? = some Rd → j ∉ Ψ.dom →
      SpineTy (Ψ ++ [(j, a)]) qs (Rd.substTy 0 (.nu (.var j 0) R)) Γ Ψ' C →
      SpineTy Ψ (.proj d :: qs) (.nu a R) Γ ((j, a) :: Ψ') C

/-- Typing environment: global signature, current block, invocation graphs, and the
enclosing top-level function with its size parameters. -/
structure TypingEnv where
  sig : List FunDecl
  block : List FunDecl
  graphs : InvGraphFamily
  caller : FunName
  callerParams : SizeCtx

mutual

/-- Curry-style expression typing `Ω; Ψ; Γ ⊢ t : A`. -/
inductive ExprTy (Ω : TypingEnv) : SizeCtx → TermCtx → Tm → Ty → Prop where
  | var {Ψ : SizeCtx} {Γ : TermCtx} {x : Nat} {A : Ty} :
      Γ.lookup x = some A → ExprTy Ω Ψ Γ (.var x) A
  | unit (Ψ : SizeCtx) (Γ : TermCtx) : ExprTy Ω Ψ Γ .unit .unit
  | pair {Ψ : SizeCtx} {Γ : TermCtx} {t u : Tm} {A B : Ty} :
      ExprTy Ω Ψ Γ t A → ExprTy Ω Ψ Γ u B → ExprTy Ω Ψ Γ (.pair t u) (.prod A B)
  | cons {Ψ : SizeCtx} {Γ : TermCtx} {c : Nat} {t : Tm} {a b : Size} {S : List Ty} {Sc : Ty} :
      S[c]? = some Sc → SizeBelow Ψ b a → TyWf Ψ 0 (.mu a S) →
      ExprTy Ω Ψ Γ t (Sc.substTy 0 (.mu b S)) → ExprTy Ω Ψ Γ (.cons c t) (.mu a S)
  | app {Ψ : SizeCtx} {Γ : TermCtx} {r s : Tm} {A B : Ty} :
      ExprTy Ω Ψ Γ r (.arr A B) → ExprTy Ω Ψ Γ s A → ExprTy Ω Ψ Γ (.app r (.term s)) B
  | proj {Ψ : SizeCtx} {Γ : TermCtx} {r : Tm} {a b : Size} {R : List Ty} {d : Nat} {Rd : Ty} :
      ExprTy Ω Ψ Γ r (.nu a R) → R[d]? = some Rd → SizeBelow Ψ b a →
      ExprTy Ω Ψ Γ (.app r (.proj d)) (Rd.substTy 0 (.nu b R))
  | lam {Ψ : SizeCtx} {Γ : TermCtx} {D : List Clause} {A : Ty} :
      TyWf Ψ 0 A → (∀ cl ∈ D, ClauseTy Ω Ψ Γ cl A) → ExprTy Ω Ψ Γ (.lam D) A
  | globalFun {Ψ : SizeCtx} {Γ : TermCtx} {g : FunDecl} {as : List Size} :
      g ∈ Ω.sig → SizeCtxWf g.sizeParams → SizeSubstWf Ψ as g.sizeParams →
      TyWf Ψ 0 (g.ty.substSize (g.sizeParams.dom.zip as)) →
      ExprTy Ω Ψ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip as))
  | localFun {Ψ : SizeCtx} {Γ : TermCtx} {g : FunDecl} {as : List Size} {G : InvGraph} :
      g ∈ Ω.block → SizeCtxWf g.sizeParams → SizeSubstWf Ψ as g.sizeParams →
      TyWf Ψ 0 (g.ty.substSize (g.sizeParams.dom.zip as)) →
      G ∈ Ω.graphs.graphs Ω.caller g.name →
      ConformsToGraph (SizeLt Ψ) (SizeLe Ψ) G as
        (Ω.callerParams.map (fun p => Size.var p.1 0)) →
      ExprTy Ω Ψ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip as))
  | sub {Ψ : SizeCtx} {Γ : TermCtx} {t : Tm} {A B : Ty} :
      ExprTy Ω Ψ Γ t A → SubTy Ψ A B → TyWf Ψ 0 B → ExprTy Ω Ψ Γ t B

/-- Clause typing `Ω; Ψ; Γ ⊢ {q⃗ → t} : A`. Pattern variables shadow `Γ`. -/
inductive ClauseTy (Ω : TypingEnv) : SizeCtx → TermCtx → Clause → Ty → Prop where
  | mk {Ψ Ψ' : SizeCtx} {Γ Γ' : TermCtx} {qs : List Copat} {t : Tm} {A C : Ty} :
      SpineTy Ψ qs A Γ' Ψ' C → ExprTy Ω (Ψ ++ Ψ') (Γ' ++ Γ) t C →
      ClauseTy Ω Ψ Γ (.mk qs t) A

end

/-- `Σ; Ξ; G ⊢ f : ∀Ψ. A = D⃗`. -/
def DeclTy (sig Ξ : List FunDecl) (𝒢 : InvGraphFamily) (d : FunDecl) : Prop :=
  SizeCtxWf d.sizeParams ∧ TyWf d.sizeParams 0 d.ty ∧
  ∀ cl ∈ d.clauses, ClauseTy ⟨sig, Ξ, 𝒢, d.name, d.sizeParams⟩ d.sizeParams [] cl d.ty

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
  ExprTy ⟨blocks.flatten, [], ⟨fun _ => 0, fun _ _ => []⟩, 0, []⟩ [] [] main A

end NishtAbel2024V3
