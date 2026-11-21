import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Chief.Existence
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Chief.AlternatingFour
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

/-! The chief and composition series of the alternating group on four letters. -/

namespace ALG02GroupTheory.Chief.AlternatingFour

open Specs.ALG02GroupTheory.Chief.AlternatingFour

abbrev V : Subgroup A4 := vValue
abbrev U : Subgroup A4 := uValue

private theorem v_klein : IsKleinFour V :=
  alternatingGroup.kleinFour_isKleinFour (by simp : Nat.card (Fin 4) = 4)

theorem elementary_abelian : ElementaryAbelian := by
  let _ : IsKleinFour V := v_klein
  exact ⟨v_klein, IsKleinFour.nonempty_mulEquiv⟩

private theorem v_card : Nat.card V = 4 := v_klein.card_four

private theorem u_card : Nat.card U = 2 := by
  change Nat.card (Subgroup.zpowers double12_34) = 2
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by decide) (by decide)

private theorem mem_v_of_sq_eq_one {g : A4} (hg : (g : Equiv.Perm (Fin 4)) ^ 2 = 1) :
    g ∈ V := by
  change g ∈ alternatingGroup.kleinFour (Fin 4)
  have hc := alternatingGroup.mem_kleinFour_of_order_two_pow
    (by simp : Nat.card (Fin 4) = 4) g.property (n := 1)
    (by simpa using (orderOf_dvd_iff_pow_eq_one.mpr hg))
  rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four
    (by simp : Nat.card (Fin 4) = 4)]
  rcases hc with h | h
  · exact Or.inl (Subtype.ext (Equiv.Perm.cycleType_eq_zero.mp h))
  · exact Or.inr h

private theorem double12_mem : double12_34 ∈ V := mem_v_of_sq_eq_one (by decide)
private theorem double13_mem : double13_24 ∈ V := mem_v_of_sq_eq_one (by decide)
private theorem double14_mem : double14_23 ∈ V := mem_v_of_sq_eq_one (by decide)

theorem subgroup_carriers : SubgroupCarriers := by
  constructor
  · let s : Finset A4 := {1, double12_34, double13_24, double14_23}
    have hs : (s : Set A4) = {1, double12_34, double13_24, double14_23} := by
      simp [s]
    rw [← hs]
    symm
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro g hg
      simp only [s, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact V.one_mem
      · exact double12_mem
      · exact double13_mem
      · exact double14_mem
    · rw [← Nat.card_coe_set_eq, Set.ncard_coe_finset]
      change Nat.card V ≤ s.card
      rw [v_card]
      decide
  · let s : Finset A4 := {1, double12_34}
    have hs : (s : Set A4) = {1, double12_34} := by simp [s]
    rw [← hs]
    symm
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro g hg
      simp only [s, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact U.one_mem
      · exact Subgroup.mem_zpowers _
    · rw [← Nat.card_coe_set_eq, Set.ncard_coe_finset]
      change Nat.card U ≤ s.card
      rw [u_card]
      decide

theorem conjugation_cycle : ConjugationCycle := by
  unfold ConjugationCycle
  decide

private theorem bot_lt_v : ⊥ < V := by
  refine bot_lt_iff_ne_bot.mpr (fun h => ?_)
  have := v_card
  rw [h, Subgroup.card_bot] at this
  omega

theorem minimal_normal : MinimalNormal := by
  refine ⟨inferInstance, bot_lt_v, fun M hM hne hle => le_antisymm hle ?_⟩
  have ⟨g, hgM, hg⟩ : ∃ g ∈ M, g ≠ 1 := by
    simpa only [ne_eq, Subgroup.eq_bot_iff_forall, not_forall, exists_prop, not_imp] using hne.ne'
  have hv := hle hgM
  rw [← SetLike.mem_coe, subgroup_carriers.1] at hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  have ⟨h12, h14, h13⟩ := conjugation_cycle
  have next14 (ha : double12_34 ∈ M) : double14_23 ∈ M :=
    h12 ▸ hM.conj_mem _ ha cycle123
  have next13 (hc : double14_23 ∈ M) : double13_24 ∈ M :=
    h14 ▸ hM.conj_mem _ hc cycle123
  have next12 (hb : double13_24 ∈ M) : double12_34 ∈ M :=
    h13 ▸ hM.conj_mem _ hb cycle123
  have ha : double12_34 ∈ M := by
    rcases hv with rfl | rfl | rfl | rfl
    · exact (hg rfl).elim
    · exact hgM
    · exact next12 hgM
    · exact next12 (next13 hgM)
  intro x hx
  rw [← SetLike.mem_coe, subgroup_carriers.1] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact M.one_mem
  · exact ha
  · exact next13 (next14 ha)
  · exact next14 ha

private theorem a4_card : Nat.card A4 = 12 :=
  alternatingGroup.card_of_card_eq_four (by simp : Nat.card (Fin 4) = 4)

private theorem v_index : V.index = 3 := by
  have h := V.card_mul_index
  rw [v_card, a4_card] at h
  omega

private theorem quotient_card : Nat.card (A4 ⧸ V) = 3 :=
  (Subgroup.index_eq_card V).symm.trans v_index

private theorem v_lt_top : V < ⊤ := by
  refine lt_of_le_of_ne le_top (fun h => ?_)
  have := v_card
  rw [h, Subgroup.card_top, a4_card] at this
  omega

theorem chief_chain : ChiefChain := by
  have hbot : AmbientCovBy ⊥ V := ⟨bot_lt_v, fun M hM h₁ h₂ =>
    h₂.ne (minimal_normal.2.2 M hM h₁ h₂.le)⟩
  have htop : AmbientCovBy V ⊤ := by
    refine ⟨v_lt_top, fun M _ hl hr => ?_⟩
    have h := Subgroup.index_dvd_of_le hl.le
    rw [v_index, Nat.dvd_prime Nat.prime_three] at h
    rcases h with h | h
    · exact hr.ne (Subgroup.index_eq_one.mp h)
    · exact hl.ne (Subgroup.eq_of_index_dvd_index hl.le (by rw [h, v_index]))
  refine ⟨rfl, rfl, fun i => ?_, fun i => ?_⟩
  · fin_cases i
    · exact Subgroup.normal_bot
    · exact vNormal
    · exact Subgroup.normal_top
  · fin_cases i
    · exact hbot
    · exact htop

theorem first_factor_and_action : FirstFactorAndAction := by
  let e : Factor ⊥ V ≃* V :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf V)).trans
      QuotientGroup.quotientBot
  have he (x : V) : e (factorMk ⊥ V x) = x := rfl
  let f : A4 →* MulAut V := MulAut.conjNormal
  have hker : V ≤ f.ker := by
    let _ : IsKleinFour V := v_klein
    let _ : IsMulCommutative V := IsKleinFour.isMulCommutative
    intro g hg
    change MulAut.conjNormal g = (1 : MulAut V)
    rw [← Subtype.coe_mk g hg, MulAut.conjNormal_val]
    apply MulEquiv.ext
    intro x
    change (⟨g, hg⟩ : V) * x * (⟨g, hg⟩ : V)⁻¹ = x
    rw [mul_comm' (⟨g, hg⟩ : V) x, mul_inv_cancel_right]
  let ρ := QuotientGroup.lift V f hker
  have hρ (g : A4) (x : V) :
      (ρ (QuotientGroup.mk' V g) x : A4) = g * (x : A4) * g⁻¹ := rfl
  refine ⟨e, ρ, he, hρ, ?_, ?_⟩
  · intro g z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((⊥ : Subgroup A4).subgroupOf V) z
    change e (g • factorMk ⊥ V x) = ρ (QuotientGroup.mk' V g) (e (factorMk ⊥ V x))
    rw [factor_smul_mk, he, he]
    exact Subtype.ext (hρ g x).symm
  · intro x
    dsimp only
    rw [hρ]
    obtain ⟨h12, h14, h13⟩ := conjugation_cycle
    exact ⟨fun hx => hx.symm ▸ h12, fun hx => hx.symm ▸ h14, fun hx => hx.symm ▸ h13⟩

theorem second_factor_and_action : SecondFactorAndAction := by
  let e : Factor V ⊤ ≃* A4 ⧸ V :=
    QuotientGroup.congr (V.subgroupOf ⊤) V Subgroup.topEquiv
      (Subgroup.map_subgroupOf_eq_of_le le_top)
  have he (x : (⊤ : Subgroup A4)) :
      e (factorMk V ⊤ x) = QuotientGroup.mk' V (x : A4) := rfl
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic (A4 ⧸ V) := isCyclic_of_prime_card quotient_card
  let _ : IsMulCommutative (A4 ⧸ V) := hcyc.isMulCommutative
  refine ⟨⟨e, he⟩, quotient_card, ⟨mulEquivOfPrimeCardEq quotient_card (by simp)⟩,
    fun g z => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf ⊤) z
  change g • factorMk V ⊤ x = factorMk V ⊤ x
  apply e.injective
  rw [factor_smul_mk, he, he]
  simp only [map_mul, map_inv]
  rw [mul_comm' (QuotientGroup.mk' V g), mul_inv_cancel_right]

private theorem bot_lt_u : ⊥ < U := by
  refine bot_lt_iff_ne_bot.mpr (fun h => ?_)
  have := u_card
  rw [h, Subgroup.card_bot] at this
  omega

private theorem u_lt_v : U < V := by
  refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr double12_mem) (fun h => ?_)
  have := u_card
  rw [h, v_card] at this
  omega

private theorem factor_order_formula {K L : Subgroup A4} (h : K ≤ L) :
    Nat.card (Factor K L) * Nat.card K = Nat.card L := by
  have hcard := K.relIndex_mul_card L
  rwa [inf_eq_left.mpr h, Subgroup.relIndex, Subgroup.index_eq_card] at hcard

private theorem u_normal_in_v : (U.subgroupOf V).Normal := by
  let _ : IsKleinFour V := v_klein
  let _ : IsMulCommutative V := IsKleinFour.isMulCommutative
  infer_instance

theorem composition_chain : CompositionChain := by
  have h₀ := factor_order_formula bot_lt_u.le
  rw [Subgroup.card_bot, u_card, mul_one] at h₀
  have h₁ : Nat.card (Factor U V) = 2 := by
    have h := factor_order_formula u_lt_v.le
    rw [u_card, v_card] at h
    omega
  have h₂ : Nat.card (Factor V ⊤) = 3 := by
    have h := factor_order_formula v_lt_top.le
    rw [Subgroup.card_top, v_card, a4_card] at h
    omega
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨rfl, rfl, Fin.strictMono_iff_lt_succ.mpr (fun i => ?_), fun i => ?_⟩
  · fin_cases i
    · exact bot_lt_u
    · exact u_lt_v
    · exact v_lt_top
  · fin_cases i
    · exact ⟨inferInstanceAs (((⊥ : Subgroup A4).subgroupOf U).Normal),
        (isSimpleGroup_of_prime_card h₀ : IsSimpleGroup (Factor ⊥ U)), h₀⟩
    · let _ := u_normal_in_v
      exact ⟨u_normal_in_v, (isSimpleGroup_of_prime_card h₁ : IsSimpleGroup (Factor U V)), h₁⟩
    · exact ⟨inferInstanceAs ((V.subgroupOf ⊤).Normal),
        (isSimpleGroup_of_prime_card h₂ : IsSimpleGroup (Factor V ⊤)), h₂⟩

theorem moved_subgroup : MovedSubgroup := by
  have hc := conjugation_cycle.1
  have hmap : U.map (MulAut.conj cycle123).toMonoidHom = Subgroup.zpowers double14_23 := by
    rw [show U = Subgroup.zpowers double12_34 from rfl, MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hc
  have hnmem : double14_23 ∉ U := by
    rw [← SetLike.mem_coe, subgroup_carriers.2]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    decide
  have hmoved : U.map (MulAut.conj cycle123).toMonoidHom ≠ U := by
    intro h
    have hu : U = Subgroup.zpowers double14_23 := h.symm.trans hmap
    exact hnmem (hu.symm ▸ Subgroup.mem_zpowers double14_23)
  have hnon : ¬ U.Normal := by
    intro h
    exact hnmem (hc ▸ h.conj_mem _ (Subgroup.mem_zpowers double12_34) cycle123)
  exact ⟨hmap, hmoved, hnon, fun h => hnon (h.2.2.1 1)⟩

end ALG02GroupTheory.Chief.AlternatingFour
