import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.ExponentCountingRank
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Set.Card

noncomputable section
open Filter Set
open scoped Topology ENNReal
namespace D12Complex.ExponentCountingRank
open OrderDivisorDefinitions

theorem countingQuotient_nonneg :
    Specs.D12Complex.Ch17.ExponentCountingRank.countingQuotient_nonneg_type := by
  intro ι a r hr
  exact div_nonneg (Real.log_nonneg (le_max_left _ _)) (Real.log_pos hr).le

theorem zeros_locallyFinite :
    Specs.D12Complex.Ch17.ExponentCountingRank.zeros_locallyFinite_type := by
  intro f r
  have hnon : ¬ EqOn f.toFun (fun _ => 0) univ := by
    intro h
    obtain ⟨z, hz⟩ := f.nonzero
    exact hz (h (mem_univ z))
  have hfin := DiscreteCountableZeros.zeros_finite_on_compact univ f.toFun
    ⟨Set.univ_nonempty, isOpen_univ, isPreconnected_univ⟩ f.holomorphic hnon
    (Metric.closedBall 0 r) (isCompact_closedBall 0 r) (subset_univ _)
  let Z := {z : ℂ // z ∈ Metric.closedBall 0 r ∧ f.toFun z = 0}
  have : Finite Z := hfin
  let g : {i : RepeatedZero f // ‖zeroLocation f i‖ ≤ r} →
      (z : Z) × Fin (analyticOrderAt f.toFun z.val).toNat :=
    fun i => ⟨⟨zeroLocation f i.val,
      by simpa using i.property, zeroLocation_is_zero f i.val⟩, i.val.2⟩
  have hg : Function.Injective g := by
    intro i j h
    apply Subtype.ext
    have h₁ : i.val.1 = j.val.1 := Subtype.ext (congrArg (fun x => x.1.val) h)
    cases i with | mk i hi =>
      cases j with | mk j hj =>
        dsimp at h₁
        cases i with | mk z k =>
          cases j with | mk w l =>
            dsimp at h₁
            subst w
            have hk : k = l := Fin.ext (congrArg (fun x => x.2.val) h)
            subst l
            rfl
  exact Finite.of_injective g hg

theorem summable_exponent_mono :
    Specs.D12Complex.Ch17.ExponentCountingRank.summable_exponent_mono_type := by
  intro ι a hloc s t hst hs
  apply hs.of_norm_bounded_eventually
  have he : ∀ᶠ i in cofinite, i ∉ {i | ‖a i‖ ≤ 1} :=
    (hloc 1).compl_mem_cofinite
  filter_upwards [he] with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow_of_exponent_le (le_of_lt (not_le.mp hi)) (neg_le_neg hst)

theorem canonicalRank_bounds :
    Specs.D12Complex.Ch17.ExponentCountingRank.canonicalRank_bounds_type := by
  intro ι a hloc q hq
  obtain ⟨hsum, hmin⟩ := (canonicalRank_eq_nat_iff a q).mp hq
  constructor
  · change (q : ℝ≥0∞) ≤ sInf _
    apply le_sInf
    rintro _ ⟨s, ⟨hs, hsumS⟩, rfl⟩
    have hqs : (q : ℝ) ≤ s := by
      by_contra! h
      cases q with
      | zero => exact (not_lt_of_ge hs.le (by simpa using h))
      | succ p =>
        apply hmin p (Nat.lt_succ_self p)
        exact summable_exponent_mono a hloc (by simpa only [Nat.cast_add, Nat.cast_one] using h.le) hsumS
    exact_mod_cast (ENNReal.ofReal_le_ofReal hqs)
  · change sInf _ ≤ _
    have hmem : ENNReal.ofReal ((q : ℝ) + 1) ∈ {x | ∃ s : ℝ,
        Specs.D12Complex.Ch17.OrderDivisorDefinitions.AdmissibleExponent_value a s ∧
        x = ENNReal.ofReal s} := ⟨(q : ℝ) + 1, ⟨by positivity, hsum⟩, rfl⟩
    simpa only [ENNReal.ofReal_add (Nat.cast_nonneg q) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one, Nat.cast_add, Nat.cast_one] using sInf_le hmem

theorem finite_divisor_bounds :
    Specs.D12Complex.Ch17.ExponentCountingRank.finite_divisor_bounds_type := by
  intro ι hι a
  exact ⟨canonicalRank_finite a, divisorExponent_finite a⟩

theorem summable_bounds_counting :
    Specs.D12Complex.Ch17.ExponentCountingRank.summable_bounds_counting_type := by
  classical
  intro ι a hloc hne s hs hsum
  refine ⟨∑' i, ‖a i‖ ^ (-s), tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _), ?_⟩
  intro r hr
  let S := (hloc r).toFinset
  have hcard : S.card = countingFunction a r := by
    change S.card = {i | ‖a i‖ ≤ r}.ncard
    exact (Set.ncard_eq_toFinset_card _ (hloc r)).symm
  have hbound : (S.card : ℝ) * r ^ (-s) ≤ ∑' i, ‖a i‖ ^ (-s) := by
    calc
      _ = ∑ i ∈ S, r ^ (-s) := by simp
      _ ≤ ∑ i ∈ S, ‖a i‖ ^ (-s) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr (hne i))
          ((hloc r).mem_toFinset.mp hi) (neg_nonpos.mpr hs.le)
      _ ≤ _ := hsum.sum_le_tsum S (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
  rw [hcard] at hbound
  have hmul : r ^ (-s) * r ^ s = 1 := by rw [← Real.rpow_add hr]; simp
  calc
    (countingFunction a r : ℝ) = (countingFunction a r : ℝ) * r ^ (-s) * r ^ s := by
      rw [mul_assoc, hmul, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hr.le _)

/-- Dyadic shells prove the counting-to-summability direction. The first
shell and every finite initial collection of shells are harmless. -/
lemma counting_bound_summable_pos {ι : Type} (a : ι → ℂ)
    (hloc : LocallyFiniteDivisor a) {u s : ℝ} (hs : 0 < s) (hus : u < s)
    (hb : ∃ C : ℝ, ∀ᶠ r : ℝ in atTop, (countingFunction a r : ℝ) ≤ C * r ^ u) :
    Summable (fun i => ‖a i‖ ^ (-s)) := by
  classical
  obtain ⟨C, hC⟩ := hb
  have hex (i : ι) : ∃ n : ℕ, ‖a i‖ ≤ (2 : ℝ) ^ n :=
    (pow_unbounded_of_one_lt ‖a i‖ (by norm_num : (1 : ℝ) < 2)).imp fun _ h => h.le
  let k : ι → ℕ := fun i => Nat.find (hex i)
  have hupper (i : ι) : ‖a i‖ ≤ (2 : ℝ) ^ k i := Nat.find_spec (hex i)
  have hlower (i : ι) (n : ℕ) (hi : k i = n + 1) : (2 : ℝ) ^ n < ‖a i‖ := by
    apply not_le.mp
    exact Nat.find_min (hex i) (by change n < k i; omega)
  let F : ℕ → Set ι := fun n => {i | k i = n}
  have hF (n : ℕ) : (F n).Finite :=
    (hloc ((2 : ℝ) ^ n)).subset (fun i hi => by
      have hi : k i = n := hi
      change ‖a i‖ ≤ (2 : ℝ) ^ n
      rw [← hi]
      exact hupper i)
  have (n : ℕ) : Finite (F n) := hF n
  have hpart : ∀ i, ∃! n, i ∈ F n := fun i => ⟨k i, rfl, fun _ h => h.symm⟩
  apply (summable_partition (fun i => Real.rpow_nonneg (norm_nonneg (a i)) (-s)) hpart).mpr
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  apply (summable_nat_add_iff 1).mp
  have hgeom : Summable (fun n : ℕ => (max 1 C * (2 : ℝ) ^ u) *
      ((2 : ℝ) ^ (u - s)) ^ n) := by
    apply Summable.mul_left
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hus)
  apply hgeom.of_norm_bounded_eventually_nat
  have ht : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually hC] with n hn
  have hc : (Nat.card (F (n + 1)) : ℝ) ≤ max 1 C * ((2 : ℝ) ^ (n + 1)) ^ u := by
    have hc0 : Nat.card (F (n + 1)) ≤ countingFunction a ((2 : ℝ) ^ (n + 1)) := by
      have : Finite {i // ‖a i‖ ≤ (2 : ℝ) ^ (n + 1)} := hloc _
      exact Nat.card_le_card_of_injective
        (fun i => (⟨i.val, by
          have hi : k i.val = n + 1 := i.property
          simpa only [hi] using hupper i.val⟩ :
          {i // ‖a i‖ ≤ (2 : ℝ) ^ (n + 1)}))
        (fun (i j : F (n + 1)) h => Subtype.ext (congrArg (fun x :
          {i // ‖a i‖ ≤ (2 : ℝ) ^ (n + 1)} => x.val) h))
    exact (Nat.cast_le.mpr hc0).trans (hn.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)))
  have hterm (i : F (n + 1)) : ‖a i.val‖ ^ (-s) ≤ ((2 : ℝ) ^ n) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (hlower i.val n i.property).le (neg_nonpos.mpr hs.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))]
  calc
    (∑' i : F (n + 1), ‖a i.val‖ ^ (-s)) ≤
        (Nat.card (F (n + 1)) : ℝ) * ((2 : ℝ) ^ n) ^ (-s) := by
      let := Fintype.ofFinite (F (n + 1))
      simpa [tsum_fintype, Nat.card_eq_fintype_card] using
        (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i))
    _ ≤ (max 1 C * ((2 : ℝ) ^ (n + 1)) ^ u) * ((2 : ℝ) ^ n) ^ (-s) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (max 1 C * (2 : ℝ) ^ u) * ((2 : ℝ) ^ (u - s)) ^ n := by
      rw [pow_succ, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_natCast_mul (by norm_num),
        ← Real.rpow_mul_natCast (by norm_num)]
      rw [show (u - s) * (n : ℝ) = (n : ℝ) * u + (n : ℝ) * (-s) by ring,
        Real.rpow_add (by norm_num)]
      ring

/-- If the counting bound has a negative exponent, the divisor must be
empty. This also handles nonpositive summation exponents in the bridge. -/
theorem counting_bound_summable :
    Specs.D12Complex.Ch17.ExponentCountingRank.counting_bound_summable_type := by
  intro ι a hloc u s hus hb
  by_cases hs : 0 < s
  · exact counting_bound_summable_pos a hloc hs hus hb
  · obtain ⟨C, hC⟩ := hb
    have hu : u < 0 := hus.trans_le (not_lt.mp hs)
    have ht : Tendsto (fun r : ℝ => C * r ^ u) atTop (𝓝 0) := by
      simpa only [neg_neg, mul_zero] using
        tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (neg_pos.mpr hu))
    have hempty : IsEmpty ι := ⟨fun i => by
      obtain ⟨r, hr, hsmall, hi⟩ :=
        (hC.and ((ht.eventually (gt_mem_nhds zero_lt_one)).and
          (eventually_ge_atTop ‖a i‖))).exists
      have : Finite {i // ‖a i‖ ≤ r} := hloc r
      have : Nonempty {i // ‖a i‖ ≤ r} := ⟨⟨i, hi⟩⟩
      have hpos : 0 < countingFunction a r := Nat.card_pos
      have hc : (1 : ℝ) ≤ countingFunction a r := by exact_mod_cast hpos
      linarith⟩
    exact Summable.of_finite

/-- An eventual polynomial bound controls the logarithmic counting limsup. -/
lemma logarithmic_limsup_le_of_power_bound (N : ℝ → ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hb : ∃ C : ℝ, ∀ᶠ r : ℝ in atTop, (N r : ℝ) ≤ C * r ^ u) :
    limsup (fun r : ℝ => ENNReal.ofReal
      (Real.log (max 1 (N r : ℝ)) / Real.log r)) atTop ≤ ENNReal.ofReal u := by
  obtain ⟨C, hC⟩ := hb
  let D := max 1 C
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have ht : Tendsto (fun r : ℝ => Real.log D / Real.log r + u) atTop (𝓝 u) := by
    simpa using (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).add_const u
  have hte := ENNReal.tendsto_ofReal ht
  rw [← hte.limsup_eq]
  refine limsup_le_limsup ?_
  filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with r hr hr1
  apply ENNReal.ofReal_le_ofReal
  have hr0 : 0 < r := zero_lt_one.trans hr1
  have hlog : 0 < Real.log r := Real.log_pos hr1
  have hb' : max 1 (N r : ℝ) ≤ D * r ^ u := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hr1.le hu)
    · exact hr.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hl : Real.log (max 1 (N r : ℝ)) ≤ Real.log D + u * Real.log r := by
    calc
      _ ≤ Real.log (D * r ^ u) := Real.log_le_log (by positivity) hb'
      _ = _ := by rw [Real.log_mul hD.ne' (Real.rpow_pos_of_pos hr0 u).ne', Real.log_rpow hr0]
  calc
    _ ≤ (Real.log D + u * Real.log r) / Real.log r := div_le_div_of_nonneg_right hl hlog.le
    _ = _ := by field_simp

/-- A strict upper bound on the logarithmic limsup gives an eventual
power bound, without a claim at the limsup itself. -/
lemma power_bound_of_logarithmic_limsup_lt (N : ℝ → ℕ) (u : ℝ) (hu : 0 < u)
    (h : limsup (fun r : ℝ => ENNReal.ofReal
      (Real.log (max 1 (N r : ℝ)) / Real.log r)) atTop < ENNReal.ofReal u) :
    ∀ᶠ r : ℝ in atTop, (N r : ℝ) ≤ r ^ u := by
  have he := eventually_lt_of_limsup_lt h
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with r hr hr1
  have hr0 : 0 < r := zero_lt_one.trans hr1
  have hq := (ENNReal.ofReal_lt_ofReal_iff hu).mp hr
  have hl : Real.log (max 1 (N r : ℝ)) < Real.log (r ^ u) := by
    rw [Real.log_rpow hr0]
    exact (div_lt_iff₀ (Real.log_pos hr1)).mp hq
  exact (le_max_right _ _).trans
    (((Real.log_lt_log_iff (by positivity) (Real.rpow_pos_of_pos hr0 u)).mp hl).le)

theorem divisorExponent_eq_countingExponent :
    Specs.D12Complex.Ch17.ExponentCountingRank.divisorExponent_eq_countingExponent_type := by
  intro ι a hloc hne
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    obtain ⟨u, hu0, heu, hub⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb
    have hu : 0 < u := ENNReal.ofReal_pos.mp (bot_le.trans_lt heu)
    obtain ⟨s, _, hus, hsb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hub
    have hs0 : 0 < s := ENNReal.ofReal_pos.mp (bot_le.trans_lt hus)
    have hus' : u < s := (ENNReal.ofReal_lt_ofReal_iff hs0).mp hus
    have hpow := power_bound_of_logarithmic_limsup_lt (countingFunction a) u hu heu
    have hsum := counting_bound_summable a hloc hus' ⟨1, by simpa using hpow⟩
    have hm : ENNReal.ofReal s ∈ {x | ∃ t : ℝ,
        Specs.D12Complex.Ch17.OrderDivisorDefinitions.AdmissibleExponent_value a t ∧
        x = ENNReal.ofReal t} := ⟨s, ⟨hs0, hsum⟩, rfl⟩
    exact (sInf_le hm).trans hsb.le
  · change countingExponent a ≤ sInf _
    apply le_sInf
    rintro _ ⟨s, ⟨hs, hsum⟩, rfl⟩
    obtain ⟨C, _, hC⟩ := summable_bounds_counting a hloc hne hs hsum
    exact logarithmic_limsup_le_of_power_bound (countingFunction a) s hs.le
      ⟨C, (eventually_gt_atTop (0 : ℝ)).mono fun r hr => hC r hr⟩

theorem zero_divisorExponent_eq_limsup :
    Specs.D12Complex.Ch17.ExponentCountingRank.zero_divisorExponent_eq_limsup_type := by
  intro f
  exact divisorExponent_eq_countingExponent (zeroLocation f) (zeros_locallyFinite f)
    (zeroLocation_nonzero f)

/-- A fixed finite addition to a counting function does not change its
logarithmic limsup. This includes an empty or finite divisor. -/
theorem finite_center_correction :
    Specs.D12Complex.Ch17.ExponentCountingRank.finite_center_correction_type := by
  intro ι a _ m
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    obtain ⟨u, hu0, heu, hub⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb
    have hu : 0 < u := ENNReal.ofReal_pos.mp (bot_le.trans_lt heu)
    have hpow := power_bound_of_logarithmic_limsup_lt (countingFunction a) u hu heu
    have hbound : ∃ C : ℝ, ∀ᶠ r : ℝ in atTop,
        ((countingFunction a r + m : ℕ) : ℝ) ≤ C * r ^ u := by
      refine ⟨1 + m, ?_⟩
      filter_upwards [hpow, eventually_ge_atTop (1 : ℝ)] with r hr hr1
      push_cast
      have hm : (m : ℝ) ≤ (m : ℝ) * r ^ u :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow hr1 hu0)
      nlinarith
    exact (logarithmic_limsup_le_of_power_bound
      (fun r => countingFunction a r + m) u hu0 hbound).trans hub.le
  · refine limsup_le_limsup ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (Real.log_pos hr).le
    apply Real.log_le_log (by positivity)
    apply max_le_max le_rfl
    exact_mod_cast Nat.le_add_right (countingFunction a r) m

theorem all_zeros_eq_limsup :
    Specs.D12Complex.Ch17.ExponentCountingRank.all_zeros_eq_limsup_type := by
  intro f
  rw [zero_divisorExponent_eq_limsup]
  exact (finite_center_correction (zeroLocation f) (zeros_locallyFinite f)
    (analyticOrderAt f.toFun 0).toNat).symm

end D12Complex.ExponentCountingRank
