import Solutions.V5.LexSCT
import Solutions.V5.Main

/-! # V5: Theorem 6 — System `F_ω^{cop}` (lexicographic measures) embeds into `F_ω^{cop,SCT}` -/

namespace NishtAbel2024V5

open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid ConformsToGraph FunName lexInvGraph
  lexInvGraphFamily)

/-! ## Typing is monotone in the admissibility of block calls -/

theorem exprTy_mono_local {sig Ξ : List FunDecl}
    {ok₁ ok₂ : SizeCtx → FunName → List Size → Prop}
    (hok : ∀ Ψ (g : FunDecl) as, g ∈ Ξ → ok₁ Ψ g.name as → ok₂ Ψ g.name as)
    {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {t : Tm} {A : Ty}
    (h : ExprTy ⟨sig, Ξ, ok₁⟩ Ψ Θ Γ t A) : ExprTy ⟨sig, Ξ, ok₂⟩ Ψ Θ Γ t A := by
  refine ExprTy.rec (motive_1 := fun Ψ Θ Γ t A _ => ExprTy ⟨sig, Ξ, ok₂⟩ Ψ Θ Γ t A)
    (motive_2 := fun Ψ Θ Γ cl A _ => ClauseTy ⟨sig, Ξ, ok₂⟩ Ψ Θ Γ cl A)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro Ψ Θ Γ x A hx; exact .var hx
  · intro Ψ Θ Γ; exact .unit Ψ Θ Γ
  · intro Ψ Θ Γ t u A B _ _ ih₁ ih₂; exact .pair ih₁ ih₂
  · intro Ψ Θ Γ c t a b S Sc hc hb hwf _ ih; exact .cons hc hb hwf ih
  · intro Ψ Θ Γ r s A B _ _ ih₁ ih₂; exact .app ih₁ ih₂
  · intro Ψ Θ Γ r a b R d Rd _ hd hb ih; exact .proj ih hd hb
  · intro Ψ Θ Γ r κ B T _ hT ih; exact .instT ih hT
  · intro Ψ Θ Γ r a b B _ hb ih; exact .instS ih hb
  · intro Ψ Θ Γ t κ B T hwf hT _ ih; exact .packT hwf hT ih
  · intro Ψ Θ Γ t a b B hwf hb _ ih; exact .packS hwf hb ih
  · intro Ψ Θ Γ D A hA _ ih; exact .lam hA ih
  · intro Ψ Θ Γ g as hg hwf hcl hsub hT; exact .globalFun hg hwf hcl hsub hT
  · intro Ψ Θ Γ g as hg hwf hcl hsub hT hloc
    exact .localFun hg hwf hcl hsub hT (hok Ψ g as hg hloc)
  · intro Ψ Θ Γ t A B _ hAB hB ih; exact .sub ih hAB hB
  · intro Ψ Ψ' Θ Θ' Γ Γ' qs t A C hsp _ ih; exact .mk hsp ih

theorem clauseTy_mono_local {sig Ξ : List FunDecl}
    {ok₁ ok₂ : SizeCtx → FunName → List Size → Prop}
    (hok : ∀ Ψ (g : FunDecl) as, g ∈ Ξ → ok₁ Ψ g.name as → ok₂ Ψ g.name as)
    {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {cl : Clause} {A : Ty}
    (h : ClauseTy ⟨sig, Ξ, ok₁⟩ Ψ Θ Γ cl A) : ClauseTy ⟨sig, Ξ, ok₂⟩ Ψ Θ Γ cl A := by
  cases h with
  | mk hsp ht => exact .mk hsp (exprTy_mono_local hok ht)

/-! ## Lexicographic calls conform to the lexicographic graphs -/

theorem idxOf?_getElem? {m : List Nat} {x pos : Nat} (h : m.idxOf? x = some pos) :
    m[pos]? = some x := by
  obtain ⟨hlt, heq, _⟩ := List.idxOf?_eq_some_iff.mp h
  rw [List.getElem?_eq_getElem hlt, heq]

theorem getElem?_idxOf? {m : List Nat} (hnd : m.Nodup) {x pos : Nat} (h : m[pos]? = some x) :
    m.idxOf? x = some pos := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h
  apply List.idxOf?_eq_some_iff.mpr
  refine ⟨hlt, heq, ?_⟩
  intro j hj he
  have hjlen : j < m.length := by omega
  have : j = pos := (List.getElem_inj (h₀ := hjlen) (h₁ := hlt) hnd).mp (he.trans heq.symm)
  omega

theorem lex_to_sct {Ξ : List FunDecl} {n : Nat} {m : List Nat} (hnd : m.Nodup)
    (hbound : ∀ i ∈ m, i < n) {d : FunDecl} (hd : d ∈ Ξ) (hdn : d.sizeParams.length = n) :
    ∀ Ψ (g : FunDecl) as, g ∈ Ξ → lexCallOK m d.sizeParams Ψ g.name as →
      sctCallOK (lexInvGraphFamily (Ξ.map FunDecl.name) n m) d.name d.sizeParams Ψ g.name as := by
  intro Ψ g as hg ⟨hlen, k, hk, hpre, i, hmi, hi, hj, hlt⟩
  refine ⟨lexInvGraph m n k, ?_, ?_⟩
  · simp only [lexInvGraphFamily]
    rw [if_pos ⟨List.mem_map_of_mem hd, List.mem_map_of_mem hg⟩]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  · refine ⟨by simp [lexInvGraph, hlen, hdn], by simp [lexInvGraph, hdn], ?_⟩
    intro i' j' hi' hj'
    have hi'n : i' < n := by rw [← hdn, ← hlen]; exact hi'
    have hj'n : j' < n := by simpa [hdn] using hj'
    rw [NishtAbel2024V2.LexGraphBase.lex_lookup m n k i' j' hi'n hj'n]
    by_cases hij : i' = j'
    · subst hij
      simp only [beq_self_eq_true, if_true]
      cases hpos : m.idxOf? i' with
      | none => simp
      | some pos =>
        simp only
        have hmpos := idxOf?_getElem? hpos
        refine ⟨fun hcase => ?_, fun hcase => ?_⟩
        · have hposk : pos = k := by
            by_contra hne
            by_cases hlt' : pos < k
            · simp [hlt'] at hcase
            · simp [hlt', hne] at hcase
          subst hposk
          rw [hmi] at hmpos
          injection hmpos with hii
          subst hii
          simpa [List.get_eq_getElem] using hlt
        · have hposk : pos < k := by
            by_contra hnlt
            by_cases heq : pos = k
            · simp [heq] at hcase
            · simp [hnlt, heq] at hcase
          obtain ⟨hi₂, hj₂, hle⟩ := hpre pos hposk i' hmpos
          simpa [List.get_eq_getElem] using hle
    · have : (i' == j') = false := by simpa using hij
      simp [this]

/-! ## Theorem 6 -/

theorem theorem_6_proof {sig Ξ : List FunDecl} (h : LexBlockTy sig Ξ) : BlockTy sig Ξ := by
  obtain ⟨n, m, hnd, hbound, harity, hdecl⟩ := h
  refine ⟨lexInvGraphFamily (Ξ.map FunDecl.name) n m,
    NishtAbel2024V2.LexicographicEmbedding.lex_family_sct _ n m hnd hbound,
    fun d hd => (harity d hd).symm, ?_⟩
  intro d hd
  obtain ⟨hwf, hty, hcls⟩ := hdecl d hd
  exact ⟨hwf, hty, fun cl hcl =>
    clauseTy_mono_local (lex_to_sct hnd hbound hd (harity d hd)) (hcls cl hcl)⟩

end NishtAbel2024V5
