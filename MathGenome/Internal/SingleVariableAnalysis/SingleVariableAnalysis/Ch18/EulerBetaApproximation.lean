import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.EulerBetaApproximation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.BetaRecurrence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.GammaDefinition
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace SingleVariableAnalysis.EulerBetaApproximation
open Set Filter MeasureTheory
open scoped Topology BigOperators
open SpecialIntegrals
namespace E
export Specs.SingleVariableAnalysis.Ch18.EulerBetaApproximation
  (scaledKernelValue logarithmicEstimate compactUniform domination integrability
    properTruncations scaledIntegral independentImproper nearZeroBound tailBound
    uniformSmallTails betaApproximation)
end E

def scaledKernel : ℝ → ℕ → ℝ → ℝ := E.scaledKernelValue

theorem scaledKernel_nonneg (s : ℝ) (n : ℕ) (u : ℝ) : 0 ≤ scaledKernel s n u := by
  by_cases h : u ∈ Ioc (0 : ℝ) (n : ℝ)
  · simp only [scaledKernel, E.scaledKernelValue, indicator_of_mem h]
    exact mul_nonneg (Real.rpow_nonneg h.1.le _)
      (pow_nonneg (sub_nonneg.mpr (div_le_one_of_le₀ h.2 (Nat.cast_nonneg n))) _)
  · simp [scaledKernel, E.scaledKernelValue, indicator_of_notMem h]

theorem scaled_domination : E.domination := by
  intro s n u hu
  refine ⟨scaledKernel_nonneg s n u, ?_, ?_⟩
  · by_cases h : u ∈ Ioc (0 : ℝ) (n : ℝ)
    · change scaledKernel s n u ≤ u ^ (s-1) * Real.exp (-u)
      simp only [scaledKernel, E.scaledKernelValue, indicator_of_mem h]
      exact mul_le_mul_of_nonneg_left (Real.one_sub_div_pow_le_exp_neg h.2)
        (Real.rpow_nonneg hu.le _)
    · simp only [E.scaledKernelValue, indicator_of_notMem h]
      exact (gammaKernel_pos s u hu).le
  · have hg : gammaKernel s u ≤ u ^ (s-1) := by
      change u ^ (s-1) * Real.exp (-u) ≤ u ^ (s-1)
      exact mul_le_of_le_one_right (Real.rpow_nonneg hu.le _)
        (Real.exp_le_one_iff.mpr (by linarith))
    by_cases h : u ∈ Ioc (0 : ℝ) (n : ℝ)
    · simp only [E.scaledKernelValue, indicator_of_mem h]
      exact (mul_le_mul_of_nonneg_left (Real.one_sub_div_pow_le_exp_neg h.2)
        (Real.rpow_nonneg hu.le _)).trans hg
    · simp only [E.scaledKernelValue, indicator_of_notMem h]
      exact Real.rpow_nonneg hu.le _

theorem scaled_integrable : E.integrability := by
  intro s hs n
  have hm : AEStronglyMeasurable (scaledKernel s n) (volume.restrict (Ioi 0)) := by
    apply AEStronglyMeasurable.indicator _ measurableSet_Ioc
    exact ((measurable_id.pow_const (s-1)).mul
      ((measurable_const.sub (measurable_id.div_const (n : ℝ))).pow_const n)).aestronglyMeasurable
  apply (gammaKernel_integrable hs).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (scaledKernel_nonneg s n u)]
  exact (scaled_domination s n u hu).2.1

theorem beta_eq_gammaSeq (s : ℝ) (hs : 0 < s) (n : ℕ) :
    (n : ℝ) ^ s * beta s ((n : ℝ)+1) = Real.GammaSeq s n := by
  change (n : ℝ) ^ s * Specs.SingleVariableAnalysis.Ch18.BetaDefinition.betaValue s ((n : ℝ)+1) = _
  rw [beta_nat_add_one_right s hs n]
  exact (mul_div_assoc _ _ _).symm

/-- The library's approximation is exactly the scaled integrand, restricted
only at the two endpoints (which have measure zero). -/
theorem raw_integral_eq_gammaSeq (s : ℝ) (hs : 0 < s) (n : ℕ) (hn : 0 < n) :
    (∫ u in (0 : ℝ)..(n : ℝ), u ^ (s-1) * (1-u/n)^n) = Real.GammaSeq s n := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he : (Real.GammaSeq s n : ℂ) = Complex.GammaSeq (s : ℂ) n := by
    dsimp [Real.GammaSeq, Complex.GammaSeq]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [he, Complex.GammaSeq_eq_approx_Gamma_integral (by simpa using hs) (Nat.ne_of_gt hn)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with u
  intro hu
  have hu0 : 0 ≤ u := by
    rw [uIoc_of_le (Nat.cast_nonneg n)] at hu
    exact hu.1.le
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hu0]
  push_cast
  ring

theorem scaled_integral : E.scaledIntegral := by
  intro s hs n hn
  rw [beta_eq_gammaSeq s hs n, ← raw_integral_eq_gammaSeq s hs n hn]
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
  change _ = ∫ u in Ioi (0 : ℝ), (Ioc (0 : ℝ) (n : ℝ)).indicator _ u
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]

theorem logarithmic_estimate : E.logarithmicEstimate := by
  intro R n hR hn hRn u hu
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hx0 : 0 ≤ u / n := div_nonneg hu.1 hnR.le
  have hxhalf : u / n ≤ 1/2 := (div_le_iff₀ hnR).mpr (by linarith [hu.2])
  have hx1 : |u / n| < 1 := by rw [abs_of_nonneg hx0]; linarith
  have hlog := Real.abs_log_sub_add_sum_range_le hx1 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one,
    abs_of_nonneg hx0] at hlog
  have hbound : |u / n + Real.log (1-u/n)| ≤ 2 * (u/n)^2 := by
    apply hlog.trans
    apply (div_le_iff₀ (by linarith : 0 < 1-u/n)).mpr
    nlinarith [sq_nonneg (u/n)]
  calc
    |(n : ℝ) * Real.log (1-u/n) + u| =
        (n : ℝ) * |u/n + Real.log (1-u/n)| := by
      have he : (n : ℝ) * Real.log (1-u/n) + u =
          (n : ℝ) * (u/n + Real.log (1-u/n)) := by
        field_simp
        ring
      rw [he, abs_mul, abs_of_pos hnR]
    _ ≤ (n : ℝ) * (2 * (u/n)^2) := mul_le_mul_of_nonneg_left hbound hnR.le
    _ = 2 * u^2 / n := by field_simp
    _ ≤ 2 * R^2 / n := by
      apply div_le_div_of_nonneg_right _ hnR.le
      have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
      linarith

theorem exp_difference_bound {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) :
    |Real.exp b - Real.exp a| ≤ b-a := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := Real.exp) (f' := Real.exp) (C := 1)
    (a := a) (b := b)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
      exact Real.exp_le_one_iff.mpr (hx.2.le.trans hb)) b ⟨hab, le_rfl⟩
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem power_exp_difference_bound (R : ℝ) (n : ℕ) (hR : 0 < R)
    (hn : 0 < n) (hRn : 2 * R ≤ (n : ℝ)) (u : ℝ) (hu : u ∈ Icc 0 R) :
    |(1-u/(n : ℝ))^n - Real.exp (-u)| ≤ 2 * R^2 / n := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hbase : 0 < 1-u/(n : ℝ) := by
    have : u/(n : ℝ) ≤ 1/2 := (div_le_iff₀ hnR).mpr (by linarith [hu.2])
    linarith
  have ha : (n : ℝ) * Real.log (1-u/n) ≤ -u := by
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hbase) hnR.le
    have he : (n : ℝ) * ((1-u/n)-1) = -u := by field_simp; ring
    rwa [he] at h
  have he : Real.exp ((n : ℝ) * Real.log (1-u/n)) = (1-u/(n : ℝ))^n := by
    rw [Real.exp_nat_mul, Real.exp_log hbase]
  have h := exp_difference_bound ha (by linarith [hu.1] : -u ≤ 0)
  rw [he, abs_sub_comm] at h
  have hlog := logarithmic_estimate R n hR hn hRn u hu
  rw [abs_of_nonpos (by linarith : (n : ℝ) * Real.log (1-u/n) + u ≤ 0)] at hlog
  exact h.trans (by linarith)


theorem compact_uniform : E.compactUniform := by
  intro s η R _hs hη hηR
  have hR : 0 < R := hη.trans_le hηR
  have hc : ContinuousOn (fun u : ℝ => u^(s-1)) (Icc η R) :=
    fun u hu => (Real.continuousAt_rpow_const u (s-1)
      (Or.inl (ne_of_gt (hη.trans_le hu.1)))).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc
  have hlim : Tendsto (fun n : ℕ => max M 1 * (2 * R^2 / (n : ℝ))) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero, div_eq_mul_inv] using (h.const_mul (2 * R^2)).const_mul (max M 1)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall := (tendsto_order.mp hlim).2 ε hε
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 * R < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (2*R))
  filter_upwards [hsmall, hlarge] with n hn hnR u hu
  have hnpos : 0 < n := Nat.cast_pos.mp (by linarith : (0 : ℝ) < n)
  have hun : u ≤ (n : ℝ) := by linarith [hu.2]
  have hu0 : 0 < u := hη.trans_le hu.1
  change dist (gammaKernel s u) (scaledKernel s n u) < ε
  rw [Real.dist_eq, abs_sub_comm]
  simp only [scaledKernel, E.scaledKernelValue, indicator_of_mem (show u ∈ Ioc 0 (n : ℝ) from ⟨hu0, hun⟩)]
  change |u^(s-1) * (1-u/(n : ℝ))^n - u^(s-1) * Real.exp (-u)| < ε
  rw [← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu0 _)]
  apply lt_of_le_of_lt _ hn
  apply mul_le_mul
  · exact (hM (mem_image_of_mem _ hu)).trans (le_max_left _ _)
  · exact power_exp_difference_bound R n hR hnpos hnR.le u ⟨hu0.le, hu.2⟩
  · exact abs_nonneg _
  · exact (zero_lt_one.trans_le (le_max_right _ _)).le


theorem scaledKernel_eq_max (s : ℝ) (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u) :
    scaledKernel s n u = u^(s-1) * (max (1-u/(n : ℝ)) 0)^n := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  by_cases hun : u ≤ (n : ℝ)
  · rw [scaledKernel, E.scaledKernelValue, indicator_of_mem (show u ∈ Ioc 0 (n : ℝ) from ⟨hu, hun⟩),
      max_eq_left (sub_nonneg.mpr ((div_le_one hnR).mpr hun))]
  · have hu' : (n : ℝ) < u := lt_of_not_ge hun
    have hb : 1-u/(n : ℝ) ≤ 0 := by
      have : 1 < u/(n : ℝ) := (lt_div_iff₀ hnR).mpr (by simpa using hu')
      linarith
    simp [scaledKernel, E.scaledKernelValue, indicator_of_notMem (show u ∉ Ioc 0 (n : ℝ) from fun h => hun h.2),
      max_eq_right hb, Nat.ne_of_gt hn]

theorem scaledKernel_continuousAt (s : ℝ) (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u) :
    ContinuousAt (scaledKernel s n) u := by
  have hc : ContinuousAt (fun x : ℝ => x^(s-1) * (max (1-x/(n : ℝ)) 0)^n) u :=
    (Real.continuousAt_rpow_const u (s-1) (Or.inl hu.ne')).mul
      ((continuousAt_const.sub (continuousAt_id.div_const _)).max continuousAt_const |>.pow n)
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu] with x hx
  exact scaledKernel_eq_max s n hn x hx

theorem scaled_proper_truncations : E.properTruncations := by
  intro s n hn a b ha hab
  exact positive_continuous_darboux (scaledKernel_continuousAt s n hn) ha hab

theorem scaled_independent_improper : E.independentImproper := by
  intro s hs n hn
  have hi := scaled_integrable s hs n
  obtain ⟨hl, hr⟩ := positive_integrable_independent
    (scaledKernel_continuousAt s n hn) hi
  refine ⟨?_, ⟨1, WithBot.coe_lt_coe.mpr zero_lt_one, WithTop.coe_lt_top _⟩,
    _, _, hl, hr, ?_⟩
  · intro a b ha hab _
    exact (scaled_proper_truncations s n hn a b (WithBot.coe_lt_coe.mp ha) hab).choose
  · exact (scaled_integral s hs n hn).trans
      (intervalIntegral.integral_interval_add_Ioi hi
        (hi.mono_set (Ioi_subset_Ioi zero_le_one))).symm

theorem scaled_near_zero_bound : E.nearZeroBound := by
  intro s hs η hη n
  have hi : IntervalIntegrable (scaledKernel s n) volume 0 η :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hη.le).mpr
      ((scaled_integrable s hs n).mono_set Ioc_subset_Ioi_self)
  have hp : IntervalIntegrable (fun u : ℝ => u^(s-1)) volume 0 η :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  refine ⟨intervalIntegral.integral_nonneg hη.le (fun u _ => scaledKernel_nonneg s n u), ?_⟩
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hη.le hi hp
    (fun u hu => (scaled_domination s n u hu.1).2.2)
  have he : (∫ u in (0 : ℝ)..η, u^(s-1)) = η^s/s := by
    rw [integral_rpow (Or.inl (by linarith : -1 < s-1))]
    simp [Real.zero_rpow hs.ne']
  exact h.trans_eq he

theorem scaled_tail_bound : E.tailBound := by
  intro s hs R hR n
  refine ⟨integral_nonneg (fun _ => scaledKernel_nonneg s n _), ?_⟩
  apply setIntegral_mono_on
    ((scaled_integrable s hs n).mono_set (Ioi_subset_Ioi hR.le))
    ((gammaKernel_integrable hs).mono_set (Ioi_subset_Ioi hR.le)) measurableSet_Ioi
  intro u hu
  exact (scaled_domination s n u (hR.trans hu)).2.1

theorem scaled_uniform_small_tails : E.uniformSmallTails := by
  intro s hs ε hε
  have h := (tendsto_order.mp (tendsto_integral_Ioi_zero (f := gammaKernel s)
    (μ := volume) tendsto_id)).2 ε hε
  obtain ⟨A, hA⟩ := eventually_atTop.mp h
  refine ⟨max A 1, zero_lt_one.trans_le (le_max_right _ _), fun n => ?_⟩
  exact (scaled_tail_bound s hs _ (zero_lt_one.trans_le (le_max_right _ _)) n).2.trans_lt
    (hA _ (le_max_left _ _))

/-- The limit interchange uses the scaled functions themselves. The final
measure-theoretic step is dominated convergence, as in Mathlib's Gamma/Beta
proof; independent Darboux convergence and all stated uniform endpoint bounds
are proved separately above. No multidimensional integral formula is used. -/
theorem euler_beta_approximation : E.betaApproximation := by
  intro s hs
  have hlim : Tendsto (fun n : ℕ => ∫ u in Ioi (0 : ℝ), scaledKernel s n u) atTop
      (𝓝 (∫ u in Ioi (0 : ℝ), gammaKernel s u)) := by
    apply tendsto_integral_of_dominated_convergence (gammaKernel s)
      (fun n => (scaled_integrable s hs n).1) (gammaKernel_integrable hs)
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      change ‖scaledKernel s n u‖ ≤ gammaKernel s u
      rw [Real.norm_eq_abs, abs_of_nonneg (scaledKernel_nonneg s n u)]
      exact (scaled_domination s n u hu).2.1
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact (compact_uniform s u u hs hu le_rfl).tendsto_at ⟨le_rfl, le_rfl⟩
  have he : (∫ u in Ioi (0 : ℝ), gammaKernel s u) = gammaIntegral s hs :=
    (intervalIntegral.integral_interval_add_Ioi (gammaKernel_integrable hs)
      ((gammaKernel_integrable hs).mono_set (Ioi_subset_Ioi zero_le_one))).symm
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (scaled_integral s hs n hn).symm

end SingleVariableAnalysis.EulerBetaApproximation
