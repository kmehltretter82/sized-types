import Definitions.Def_NishtAbel2024V5_Inference
import Solutions.V5.Size

/-! # V5 inference: soundness of the executable size checks (Theorem 14, checked form) -/

namespace NishtAbel2024V5

theorem lookup_mem_gen {β : Type} {L : List (Nat × β)} {x : Nat} {v : β}
    (h : L.lookup x = some v) : (x, v) ∈ L := by
  induction L with
  | nil => simp [List.lookup] at h
  | cons p L ih =>
    obtain ⟨y, w⟩ := p
    by_cases hxy : x = y
    · subst hxy
      simp [List.lookup] at h
      subst h
      simp
    · have hb : (x == y) = false := by simpa using hxy
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem Size.wfB_sound {Ψ : SizeCtx} : ∀ {a : Size}, a.wfB Ψ = true → SizeWf Ψ a
  | .inf _, _ => trivial
  | .var i _, h => by
    show i ∈ Ψ.dom
    simpa [Size.wfB] using h
  | .bvar _ _, h => by simp [Size.wfB] at h
  | .meet _ _, h => by
    simp only [Size.wfB, Bool.and_eq_true] at h
    exact ⟨Size.wfB_sound h.1, Size.wfB_sound h.2⟩

theorem Size.wfB_complete {Ψ : SizeCtx} : ∀ {a : Size}, SizeWf Ψ a → a.wfB Ψ = true
  | .inf _, _ => rfl
  | .var i _, h => by
    have : i ∈ Ψ.dom := h
    simpa [Size.wfB] using this
  | .bvar _ _, h => absurd h (Nat.not_lt_zero _)
  | .meet _ _, h => by
    simp only [Size.wfB, Bool.and_eq_true]
    exact ⟨Size.wfB_complete h.1, Size.wfB_complete h.2⟩

/-- The executable strict comparison is sound. -/
theorem sizeLtB_sound : ∀ (fuel : Nat) (Ψ : SizeCtx) (a b : Size),
    sizeLtB fuel Ψ a b = true → SizeLt Ψ a b
  | 0, _, _, _, h => by simp [sizeLtB] at h
  | fuel + 1, Ψ, a, b, h => by
    unfold sizeLtB at h
    simp only [Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · split at h
      · exact .inf_inf (by simpa using h)
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, hnm⟩, hi⟩ := h
        exact .var_var (by simpa using hi) hnm
      · simp at h
    · split at h
      · rename_i i n
        split at h
        · rename_i bnd hl
          have hm := lookup_mem_gen hl
          simp only [Bool.or_eq_true] at h
          rcases h with h | h
          · exact .bound hm (sizeLtB_sound fuel Ψ _ _ h)
          · split at h
            · exact .var_inf hm (sizeLtB_sound fuel Ψ _ _ h)
            · simp at h
        · simp at h
      · rename_i a₁ a₂
        simp only [Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact .meet_l (sizeLtB_sound fuel Ψ _ _ h₁) (Size.wfB_sound h₂)
        · exact .meet_r (sizeLtB_sound fuel Ψ _ _ h₁) (Size.wfB_sound h₂)
      · simp at h
    · split at h
      · simp only [Bool.and_eq_true] at h
        exact .lt_meet (sizeLtB_sound fuel Ψ _ _ h.1) (sizeLtB_sound fuel Ψ _ _ h.2)
      · simp at h

theorem sizeLeB_sound {fuel : Nat} {Ψ : SizeCtx} {a b : Size} (h : sizeLeB fuel Ψ a b = true) :
    SizeLe Ψ a b :=
  sizeLtB_sound fuel Ψ a (b.shift 1) h

theorem SConstr.check_sound {fuel : Nat} {φ : FlexSubst} {c : SConstr}
    (h : c.check fuel φ = true) : c.Holds φ := by
  unfold SConstr.check at h
  unfold SConstr.Holds
  split
  · rename_i hs
    simp only [hs, if_true] at h
    exact sizeLtB_sound _ _ _ _ h
  · rename_i hs
    simp only [hs, if_false] at h
    exact sizeLeB_sound h

/-- The coherence post-check is sound. -/
theorem checkCoherent_sound {fuel : Nat} {φ : FlexSubst} {C : List SConstr}
    (h : checkCoherent fuel φ C = true) : Coherent φ C := by
  intro c hc
  exact SConstr.check_sound (List.all_eq_true.mp h c hc)

/-- The scoping post-check is sound. -/
theorem checkScope_sound {φ : FlexSubst} {Φ : List FlexVar} (h : checkScope φ Φ = true) :
    ScopeOK φ Φ := by
  intro v hv
  have := List.all_eq_true.mp h v hv
  split at this
  · rename_i b hb
    exact ⟨b, hb, Size.wfB_sound this⟩
  · simp at this

end NishtAbel2024V5
