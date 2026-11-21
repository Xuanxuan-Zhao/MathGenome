import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.FiniteOrderDivisorGrowth
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.ZeroCounting
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.ExponentCountingRank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
open Filter Set
open scoped Topology ENNReal
namespace D12Complex.FiniteOrderDivisorGrowth
open OrderDivisorDefinitions ExponentCountingRank ZeroCounting

/-- A strict upper bound on the order gives the required growth estimate;
no estimate at the order itself is asserted. -/
lemma log_maximum_eventually_le (f : NonzeroEntireFunction) (hfin : order f ≠ ⊤)
    {s : ℝ} (hs : (order f).toReal < s) :
    ∀ᶠ r : ℝ in atTop, Real.log (max (Real.exp 1) (maximumModulus f.toFun r)) ≤ r ^ s := by
  have hs0 : 0 < s := lt_of_le_of_lt ENNReal.toReal_nonneg hs
  have horder : order f < ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hs0).mpr hs
  have he := eventually_lt_of_limsup_lt horder
  change ∀ᶠ r : ℝ in atTop, _ at he
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with r hr hr1
  have hq : growthQuotient f.toFun r < s :=
    (ENNReal.ofReal_lt_ofReal_iff hs0).mp hr
  have hr0 : 0 < r := zero_lt_one.trans hr1
  have hL : 0 < Real.log (max (Real.exp 1) (maximumModulus f.toFun r)) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (le_max_left (Real.exp 1) (maximumModulus f.toFun r))
    rw [Real.log_exp] at h
    linarith
  have hl : Real.log (Real.log (max (Real.exp 1) (maximumModulus f.toFun r))) <
      Real.log (r ^ s) := by
    rw [Real.log_rpow hr0]
    exact (div_lt_iff₀ (Real.log_pos hr1)).mp hq
  exact ((Real.log_lt_log_iff hL (Real.rpow_pos_of_pos hr0 s)).mp hl).le

/-- The repeated-zero count is bounded by the sum of all analytic
multiplicities, including the possible center zero. -/
lemma counting_le_zeroCount (f : NonzeroEntireFunction) (r : ℝ) :
    countingFunction (zeroLocation f) r ≤ zeroCount f.toFun r := by
  classical
  let n : ℂ → ℕ := fun z => if ‖z‖ ≤ r then (analyticOrderAt f.toFun z).toNat else 0
  let S := (count_support_finite f r).toFinset
  have hS : ∀ z, z ∈ S ↔ n z ≠ 0 := by
    intro z
    simp [S, n, Function.mem_support]
  let g : {i : RepeatedZero f // ‖zeroLocation f i‖ ≤ r} → (z : S) × Fin (n z) :=
    fun i => ⟨⟨zeroLocation f i.val, (hS _).mpr (by
      dsimp [n]
      rw [ite_eq_left i.property]
      exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) i.val.2.isLt))⟩,
      ⟨i.val.2.val, by
        change i.val.2.val < (if ‖zeroLocation f i.val‖ ≤ r then
          (analyticOrderAt f.toFun (zeroLocation f i.val)).toNat else 0)
        rw [ite_eq_left i.property]
        exact i.val.2.isLt⟩⟩
  have hg : Function.Injective g := by
    intro i j h
    have hz : i.val.1 = j.val.1 := Subtype.ext (congrArg (fun x => x.1.val) h)
    have hk : i.val.2.val = j.val.2.val := congrArg (fun x => x.2.val) h
    apply Subtype.ext
    cases i with | mk i hi =>
      cases j with | mk j hj =>
        cases i with | mk z k =>
          cases j with | mk w l =>
            dsimp at hz
            subst w
            have he : k = l := Fin.ext hk
            subst l
            rfl
  let : Fintype S := Finset.Subtype.fintype S
  have hc := Nat.card_le_card_of_injective g hg
  change countingFunction (zeroLocation f) r ≤ _ at hc
  rw [Nat.card_sigma] at hc
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hc
  have he : (∑ z : S, n z) = zeroCount f.toFun r := by
    change (∑ z : S, n z) = ∑ᶠ z, n z
    rw [finsum_eq_sum_of_support_subset _ (fun z hz => (hS z).mpr hz)]
    exact Finset.sum_coe_sort S n
  exact hc.trans_eq he

/-- Dividing out the center power and normalizing costs only a fixed
additive term in the logarithmic maximum on circles of radius at least one. -/
lemma normalized_log_bound (f : NonzeroEntireFunction) (m : ℕ) (c : ℂ) (g : ℂ → ℂ)
    (hc : c ≠ 0) (hg : HolomorphicOn univ g) (hg0 : g 0 = 1)
    (he : ∀ z, f.toFun z = z ^ m * (c * g z))
    (R : ℝ) (hR : 1 ≤ R) :
    Real.log (maximumModulus g R) ≤
      Real.log (max (Real.exp 1) (maximumModulus f.toFun R)) + |Real.log ‖c‖| := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hgc : Continuous g := (show Differentiable ℂ g from fun z => hg.2 z (mem_univ _)).continuous
  obtain ⟨z, hz, hzg, _⟩ := maximumModulus_attained g hgc R hR0
  have hzR : ‖z‖ = R := by simpa using hz
  have hMG : 1 ≤ maximumModulus g R := one_le_maximumModulus hg hg0 hR0
  have hMF := (maximumModulus_attained f.toFun
    (show Differentiable ℂ f.toFun from fun z => f.holomorphic.2 z (mem_univ _)).continuous
    R hR0).choose_spec.2.2 z hz
  have hmul : ‖c‖ * maximumModulus g R ≤ maximumModulus f.toFun R := by
    calc
      _ ≤ R ^ m * (‖c‖ * maximumModulus g R) :=
        le_mul_of_one_le_left (mul_nonneg (norm_nonneg _) (by linarith)) (one_le_pow₀ hR)
      _ = ‖f.toFun z‖ := by
        rw [he z, norm_mul, norm_pow, norm_mul, hzR, hzg]
        rfl
      _ ≤ _ := hMF
  have hl := Real.log_le_log (mul_pos (norm_pos_iff.mpr hc) (by linarith : 0 < maximumModulus g R))
    (hmul.trans (le_max_right (Real.exp 1) _))
  rw [Real.log_mul (norm_ne_zero_iff.mpr hc) (by linarith : maximumModulus g R ≠ 0)] at hl
  have habs := neg_abs_le (Real.log ‖c‖)
  linarith

theorem counting_growth : Specs.D12Complex.Ch17.FiniteOrderDivisorGrowth.counting_growth_type := by
  intro f hfin s hs
  have hs0 : 0 < s := lt_of_le_of_lt ENNReal.toReal_nonneg hs
  obtain ⟨m, c, g, hm, hc, hg, hg0, he, hord, hcounts, hJ⟩ := center_reduction f
  have ht : Tendsto (fun r : ℝ => 2 * r) atTop atTop := by
    exact tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hb := ht.eventually (log_maximum_eventually_le f hfin hs)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hb
  let A := |Real.log ‖c‖|
  let C := (m : ℝ) + ((2 : ℝ) ^ s + A) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C, A]; positivity
  refine ⟨C, hC, max 1 R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun r hr => ?_⟩
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  have hpow1 : 1 ≤ r ^ s := Real.one_le_rpow hr1 hs0.le
  have hb' : Real.log (maximumModulus g (2 * r)) ≤ (2 * r) ^ s + A := by
    have h₁ := normalized_log_bound f m c g hc hg hg0 he (2 * r) (by linarith)
    have h₂ := hR r ((le_max_right _ _).trans hr)
    dsimp [A]
    linarith
  have hn : (zeroCount g r : ℝ) ≤ ((2 : ℝ) ^ s + A) / Real.log 2 * r ^ s := by
    apply (mul_le_mul_iff_left₀ hlog2).mp
    have h := (hJ r hr0).trans hb'
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr0.le] at h
    have hA : 0 ≤ A := abs_nonneg _
    have hAA : A ≤ A * r ^ s := le_mul_of_one_le_right hA hpow1
    calc
      (zeroCount g r : ℝ) * Real.log 2 ≤ (2 : ℝ) ^ s * r ^ s + A := h
      _ ≤ (((2 : ℝ) ^ s + A) / Real.log 2 * r ^ s) * Real.log 2 := by
        field_simp
        nlinarith
  have hcount : (countingFunction (zeroLocation f) r : ℝ) ≤ (m : ℝ) + zeroCount g r := by
    have h := counting_le_zeroCount f r
    change countingFunction (zeroLocation f) r ≤
      Specs.D12Complex.Ch17.ZeroCounting.zeroCount_value f.toFun r at h
    rw [hcounts r hr0.le] at h
    exact_mod_cast h
  have hm1 : (m : ℝ) ≤ (m : ℝ) * r ^ s :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hpow1
  dsimp [C]
  nlinarith

theorem summable_above_order :
    Specs.D12Complex.Ch17.FiniteOrderDivisorGrowth.summable_above_order_type := by
  intro f hfin s hs
  obtain ⟨u, hρu, hus⟩ := exists_between hs
  obtain ⟨C, _, R, _, hR⟩ := counting_growth f hfin u hρu
  exact counting_bound_summable (zeroLocation f) (zeros_locallyFinite f) hus
    ⟨C, (eventually_ge_atTop R).mono (fun r hr => hR r hr)⟩

theorem divisorExponent_le_order :
    Specs.D12Complex.Ch17.FiniteOrderDivisorGrowth.divisorExponent_le_order_type := by
  intro f hfin
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  obtain ⟨s, hs0, hos, hsb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb
  have hspos : 0 < s := ENNReal.ofReal_pos.mp (bot_le.trans_lt hos)
  have hs : (order f).toReal < s := by
    rw [← ENNReal.ofReal_toReal hfin] at hos
    exact (ENNReal.ofReal_lt_ofReal_iff hspos).mp hos
  have hm : ENNReal.ofReal s ∈ {x | ∃ t : ℝ,
      Specs.D12Complex.Ch17.OrderDivisorDefinitions.AdmissibleExponent_value
        (zeroLocation f) t ∧ x = ENNReal.ofReal t} :=
    ⟨s, ⟨hspos, summable_above_order f hfin s hs⟩, rfl⟩
  exact (sInf_le hm).trans hsb.le

theorem floor_sum : Specs.D12Complex.Ch17.FiniteOrderDivisorGrowth.floor_sum_type := by
  intro f hfin
  exact summable_above_order f hfin _ (Nat.lt_floor_add_one _)

theorem canonicalRank_le_floor :
    Specs.D12Complex.Ch17.FiniteOrderDivisorGrowth.canonicalRank_le_floor_type := by
  classical
  intro f hfin
  have hsum : RankSummable (zeroLocation f) ⌊(order f).toReal⌋₊ := floor_sum f hfin
  have hex : ∃ q, Specs.D12Complex.Ch17.OrderDivisorDefinitions.RankSummable_value
      (zeroLocation f) q := ⟨_, hsum⟩
  change (if h : ∃ q, Specs.D12Complex.Ch17.OrderDivisorDefinitions.RankSummable_value
      (zeroLocation f) q then (Nat.find h : ℕ∞) else ⊤) ≤ _
  rw [dite_eq_left hex]
  exact_mod_cast Nat.find_min' hex hsum

end D12Complex.FiniteOrderDivisorGrowth
