import Solutions.V3.Reduct

/-! # V3: reducibility candidates -/

namespace NishtAbel2024V3

/-- Reducibility candidates over closed strongly normalizing terms. -/
structure Cand (W : World) (𝒜 : Set Tm) : Prop where
  sn : ∀ t ∈ 𝒜, SNc W t
  red : ∀ t ∈ 𝒜, ∀ t', Step W t t' → t' ∈ 𝒜
  neutral : ∀ t, t.Closed → IsNeutral W t → (∀ t', Step W t t' → t' ∈ 𝒜) → t ∈ 𝒜

theorem SN.step {W : World} {t t' : Tm} (h : SN W t) (hs : Step W t t') : SN W t' :=
  Acc.inv h hs

theorem SN.of_reducts {W : World} {t : Tm} (h : ∀ t', Step W t t' → SN W t') : SN W t :=
  Acc.intro t h

theorem Cand.red_steps {W : World} {𝒜 : Set Tm} (h : Cand W 𝒜) {t u : Tm} (ht : t ∈ 𝒜)
    (hs : Steps W t u) : u ∈ 𝒜 := by
  induction hs with
  | refl => exact ht
  | tail _ hs ih => exact h.red _ ih _ hs

/-- Intro sets contain every closed non-introduction term whose reducts they contain. -/
theorem introSet_of_reducts {W : World} {P : Tm → Prop} {t : Tm} (hc : t.Closed)
    (hi : ¬ IsIntro t) (h : ∀ t', Step W t t' → t' ∈ IntroSet W P) : t ∈ IntroSet W P := by
  refine ⟨⟨hc, SN.of_reducts fun t' hs => (h t' hs).1.2⟩, ?_⟩
  intro v hv hvi
  rcases Relation.ReflTransGen.cases_head hv with rfl | ⟨t₁, hs, hrest⟩
  · exact absurd hvi hi
  · exact (h t₁ hs).2 v hrest hvi

theorem introSet_cand {W : World} (hW : WorldClosed W) (P : Tm → Prop) :
    Cand W (IntroSet W P) where
  sn _ h := h.1
  red t ht t' hs := by
    refine ⟨⟨step_closed hW hs ht.1.1, ht.1.2.step hs⟩, ?_⟩
    intro v hv hvi
    exact ht.2 v (Relation.ReflTransGen.head hs hv) hvi
  neutral t hc hn h := introSet_of_reducts hc hn.1 h

theorem introSet_of_intro {W : World} {P : Tm → Prop} {v : Tm} (h : v ∈ IntroSet W P)
    (hv : IsIntro v) : P v :=
  h.2 v Relation.ReflTransGen.refl hv

theorem arrSet_cand {W : World} (hW : WorldClosed W) {𝒜 ℬ : Set Tm} (hA : Cand W 𝒜)
    (hB : Cand W ℬ) : Cand W (ArrSet W 𝒜 ℬ) where
  sn _ h := h.1
  red t ht t' hs := by
    refine ⟨⟨step_closed hW hs ht.1.1, ht.1.2.step hs⟩, ?_⟩
    intro s hs'
    exact hB.red _ (ht.2 s hs') _ (Step.appFun hs)
  neutral t hc hn h := by
    refine ⟨⟨hc, SN.of_reducts fun t' hs => (h t' hs).1.2⟩, ?_⟩
    intro s hs
    have hsn : SN W s := (hA.sn s hs).2
    induction hsn with
    | intro s _ ih =>
      apply hB.neutral
      · simp [Tm.Closed, Tm.fv, Elim.fv] at hc ⊢
        exact ⟨hc, (hA.sn s hs).1⟩
      · exact neutral_app hn _
      · intro u hu
        cases hu with
        | head hh =>
          obtain ⟨t', ht', hu⟩ := hn.2 [.term s] _ hh
          subst hu
          exact (h t' (Step.head ht')).2 s hs
        | appFun hs' => exact (h _ hs').2 s hs
        | appArg hs' => exact ih _ hs' (hA.red s hs _ hs')

theorem MuSet_eq (W : World) (F : Nat → Set Tm → Set Tm) (α : Ordinal.{0}) :
    MuSet W F α = IntroSet W (fun v => ∃ c t β, ∃ _ : β < α, v = .cons c t ∧ t ∈ F c (MuSet W F β)) := by
  unfold MuSet
  rw [WellFounded.fix_eq]

theorem NuSet_eq (W : World) (n : Nat) (G : Nat → Set Tm → Set Tm) (α : Ordinal.{0}) :
    NuSet W n G α = {t | SNc W t ∧ ∀ β (_ : β < α), ∀ d < n,
      Tm.app t (.proj d) ∈ G d (NuSet W n G β)} := by
  unfold NuSet
  rw [WellFounded.fix_eq]

theorem nuSet_cand {W : World} (hW : WorldClosed W) (n : Nat) {G : Nat → Set Tm → Set Tm}
    (hG : ∀ d < n, ∀ 𝒳, Cand W 𝒳 → Cand W (G d 𝒳)) (α : Ordinal.{0}) :
    Cand W (NuSet W n G α) := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [NuSet_eq]
    refine ⟨fun _ h => h.1, ?_, ?_⟩
    · intro t ht t' hs
      refine ⟨⟨step_closed hW hs ht.1.1, ht.1.2.step hs⟩, ?_⟩
      intro β hβ d hd
      exact (hG d hd _ (ih β hβ)).red _ (ht.2 β hβ d hd) _ (Step.appFun hs)
    · intro t hc hn h
      refine ⟨⟨hc, SN.of_reducts fun t' hs => (h t' hs).1.2⟩, ?_⟩
      intro β hβ d hd
      apply (hG d hd _ (ih β hβ)).neutral
      · simpa [Tm.Closed, Tm.fv, Elim.fv] using hc
      · exact neutral_app hn _
      · intro u hu
        cases hu with
        | head hh =>
          obtain ⟨t', ht', hu⟩ := hn.2 [.proj d] _ hh
          subst hu
          exact (h t' (Step.head ht')).2 β hβ d hd
        | appFun hs' => exact (h _ hs').2 β hβ d hd

theorem interpAt_eq (W : World) (ρ : SizeVal) :
    ∀ (S : List Ty) (c : Nat) (η : Env) (h : c < S.length),
      interpAt W ρ S c η = interp W ρ (S[c]'h) η
  | [], c, η, h => by simp at h
  | A :: S, 0, η, _ => by simp [interpAt]
  | A :: S, c + 1, η, h => by
    simp only [interpAt]
    exact interpAt_eq W ρ S c η (by simpa using h)

theorem Env.cons_cand {W : World} {𝒳 : Set Tm} {η : Env} {k : Nat} (h𝒳 : Cand W 𝒳)
    (hη : ∀ X < k, Cand W (η X)) : ∀ X < k + 1, Cand W (Env.cons 𝒳 η X)
  | 0, _ => h𝒳
  | X + 1, h => hη X (by omega)

/-- Every well-formed type denotes a candidate. -/
theorem interp_cand {W : World} (hW : WorldClosed W) (ρ : SizeVal) {Ψ : SizeCtx} {k : Nat}
    {A : Ty} (hA : TyWf Ψ k A) : ∀ η : Env, (∀ X < k, Cand W (η X)) → Cand W (interp W ρ A η) := by
  induction hA with
  | unit k => intro η _; exact introSet_cand hW _
  | prod _ _ _ _ => intro η _; exact introSet_cand hW _
  | arr _ _ ihA ihB => intro η hη; exact arrSet_cand hW (ihA η hη) (ihB η hη)
  | var hX => intro η hη; exact hη _ hX
  | mu _ _ _ _ =>
    intro η _
    simp only [interp]
    rw [MuSet_eq]
    exact introSet_cand hW _
  | @nu k a R _ _ _ ih =>
    intro η hη
    simp only [interp]
    apply nuSet_cand hW
    intro d hd 𝒳 h𝒳
    rw [interpAt_eq W ρ R d _ hd]
    exact ih _ (List.getElem_mem hd) _ (Env.cons_cand h𝒳 hη)

end NishtAbel2024V3
