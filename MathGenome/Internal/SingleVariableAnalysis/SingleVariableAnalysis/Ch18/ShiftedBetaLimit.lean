import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.ShiftedBetaLimit
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.EulerBetaApproximation
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SingleVariableAnalysis.ShiftedBetaLimit
open Set Filter MeasureTheory
open scoped Topology
open SpecialIntegrals
namespace S
export Specs.SingleVariableAnalysis.Ch18.ShiftedBetaLimit
  (shiftedKernelValue logarithmicEstimate compactUniform domination
    majorantIntegrability integrability properTruncations nearZeroBound
    tailBound uniformSmallTails independentImproper kernelIntegralLimit shiftedBetaLimit scaledIntegral)
end S

def shiftedKernel : ℝ → ℝ → ℕ → ℝ → ℝ := S.shiftedKernelValue

/-- The real shift contributes an additional O(R/n) term to the Euler estimate. -/
theorem logarithmic_estimate : S.logarithmicEstimate := by
  intro p R n hR hn hRn u hu
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hx : 0 ≤ u/(n : ℝ) := div_nonneg hu.1 hnR.le
  have hxhalf : u/(n : ℝ) ≤ 1/2 := (div_le_iff₀ hnR).mpr (by linarith [hu.2])
  have hb : 0 < 1-u/(n : ℝ) := by linarith
  have hlog := EulerBetaApproximation.logarithmic_estimate R n hR hn hRn u hu
  have hnlog : |Real.log (1-u/(n : ℝ))| ≤ 2*R/n := by
    have he : Real.log (1-u/(n : ℝ)) ≤ 0 :=
      Real.log_nonpos (by linarith) (by linarith)
    rw [abs_of_nonpos he]
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hb)
    rw [Real.log_inv] at h
    have hi : (1-u/(n : ℝ))⁻¹ - 1 ≤ 2*u/n := by
      rw [inv_eq_one_div, div_sub_one hb.ne']
      apply (div_le_iff₀ hb).mpr
      have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
      have heq : 2*u/(n : ℝ) = 2*(u/n) := by ring
      rw [heq]
      nlinarith
    exact (h.trans hi).trans ((div_le_div_iff_of_pos_right hnR).mpr (by linarith [hu.2]))
  calc
    |((n : ℝ)+p-1)*Real.log (1-u/n)+u| =
        |((n : ℝ)*Real.log (1-u/n)+u) + (p-1)*Real.log (1-u/n)| := by ring_nf
    _ ≤ |(n : ℝ)*Real.log (1-u/n)+u| + |(p-1)*Real.log (1-u/n)| := abs_add_le _ _
    _ ≤ 2*R^2/n + |p-1| *(2*R/n) :=
      add_le_add hlog (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hnlog (abs_nonneg _))
    _ = (2*R^2+2*|p-1| *R)/n := by ring

/-- Uniform estimate for the power factor, including an arbitrary fixed real shift. -/
theorem power_exp_difference_bound (p R : ℝ) (n : ℕ) (hp : 0 < p)
    (hR : 0 < R) (hn : 2 ≤ n) (hRn : 2*R ≤ (n : ℝ))
    (u : ℝ) (hu : u ∈ Icc 0 R) :
    |(1-u/(n : ℝ))^((n : ℝ)+p-1) - Real.exp (-u)| ≤
      (2*R^2+2*|p-1| *R)/n := by
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hb : 0 < 1-u/(n : ℝ) := by
    have : u/(n : ℝ) ≤ 1/2 := (div_le_iff₀ hnR).mpr (by linarith [hu.2])
    linarith
  have hlog : Real.log (1-u/(n : ℝ)) ≤ 0 :=
    Real.log_nonpos hb.le (by have := div_nonneg hu.1 hnR.le; linarith)
  have hexp : ((n : ℝ)+p-1)*Real.log (1-u/n) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith) hlog
  have hdiff : |Real.exp (((n : ℝ)+p-1)*Real.log (1-u/n)) - Real.exp (-u)| ≤
      |((n : ℝ)+p-1)*Real.log (1-u/n)+u| := by
    by_cases h : ((n : ℝ)+p-1)*Real.log (1-u/n) ≤ -u
    · have he := EulerBetaApproximation.exp_difference_bound h (by linarith [hu.1])
      rw [abs_sub_comm] at he
      exact he.trans (by rw [abs_of_nonpos (by linarith)]; linarith)
    · have he := EulerBetaApproximation.exp_difference_bound (le_of_not_ge h) hexp
      exact he.trans (by rw [abs_of_nonneg (by linarith)]; linarith)
  rw [Real.rpow_def_of_pos hb, mul_comm (Real.log _) _]
  exact hdiff.trans (logarithmic_estimate p R n hR hnpos hRn u hu)



theorem compact_uniform : S.compactUniform := by
  intro p q η R hp _hq hη hηR
  have hR : 0 < R := hη.trans_le hηR
  have hc : ContinuousOn (fun u : ℝ => u^(q-1)) (Icc η R) :=
    fun u hu => (Real.continuousAt_rpow_const u (q-1)
      (Or.inl (ne_of_gt (hη.trans_le hu.1)))).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc
  have hlim : Tendsto (fun n : ℕ => max M 1 *
      ((2*R^2+2*|p-1| *R)/(n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (2*R^2+2*|p-1| *R) |>.const_mul (max M 1)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall := (tendsto_order.mp hlim).2 ε hε
  have hlarge : ∀ᶠ n : ℕ in atTop, 2*R < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (2*R))
  filter_upwards [hsmall, hlarge, eventually_ge_atTop 2] with n hn hnR hn2 u hu
  have hu0 : 0 < u := hη.trans_le hu.1
  have hun : u ≤ (n : ℝ) := by linarith [hu.2]
  change dist (gammaKernel q u) (shiftedKernel p q n u) < ε
  rw [Real.dist_eq, abs_sub_comm]
  simp only [shiftedKernel, S.shiftedKernelValue,
    indicator_of_mem (show u ∈ Ioc 0 (n : ℝ) from ⟨hu0, hun⟩)]
  change |u^(q-1)*(1-u/(n : ℝ))^((n : ℝ)+p-1) - u^(q-1)*Real.exp (-u)| < ε
  rw [← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu0 _)]
  apply lt_of_le_of_lt _ hn
  apply mul_le_mul
  · exact (hM (mem_image_of_mem _ hu)).trans (le_max_left _ _)
  · exact power_exp_difference_bound p R n hp hR hn2 hnR.le u ⟨hu0.le, hu.2⟩
  · exact abs_nonneg _
  · exact (zero_lt_one.trans_le (le_max_right _ _)).le

theorem shiftedKernel_nonneg (p q : ℝ) (n : ℕ) (u : ℝ) :
    0 ≤ shiftedKernel p q n u := by
  by_cases h : u ∈ Ioc (0 : ℝ) (n : ℝ)
  · simp only [shiftedKernel, S.shiftedKernelValue, indicator_of_mem h]
    exact mul_nonneg (Real.rpow_nonneg h.1.le _) (Real.rpow_nonneg
      (sub_nonneg.mpr (div_le_one_of_le₀ h.2 (Nat.cast_nonneg n))) _)
  · simp [shiftedKernel, S.shiftedKernelValue, indicator_of_notMem h]

theorem shifted_domination : S.domination := by
  intro p q hp n hn u hu
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have ha : 0 < (n : ℝ)+p-1 := by linarith
  have hhalf : (n : ℝ)/2 ≤ (n : ℝ)+p-1 := by linarith
  have he : shiftedKernel p q n u ≤ u^(q-1)*Real.exp (-u/2) := by
    by_cases hun : u ∈ Ioc (0 : ℝ) (n : ℝ)
    · simp only [shiftedKernel, S.shiftedKernelValue, indicator_of_mem hun]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu.le _)
      by_cases hune : u = (n : ℝ)
      · simp [hune, div_self hnpos.ne', Real.zero_rpow ha.ne', (Real.exp_pos _).le]
      · have hb : 0 < 1-u/(n : ℝ) := by
          apply sub_pos.mpr
          exact (div_lt_one hnpos).mpr (lt_of_le_of_ne hun.2 hune)
        rw [Real.rpow_def_of_pos hb]
        apply Real.exp_le_exp.mpr
        have hl : Real.log (1-u/(n : ℝ)) ≤ -u/(n : ℝ) := by
          have h := Real.log_le_sub_one_of_pos hb
          convert h using 1 <;> ring
        have h₁ := mul_le_mul_of_nonneg_right hl ha.le
        have h₂ := mul_le_mul_of_nonpos_left hhalf
          (neg_nonpos.mpr (div_nonneg hu.le hnpos.le))
        have heq : -(u/(n : ℝ))*((n : ℝ)/2) = -u/2 := by field_simp
        exact h₁.trans (by simpa only [neg_div] using h₂.trans_eq heq)
    · simp only [shiftedKernel, S.shiftedKernelValue, indicator_of_notMem hun]
      exact mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le
  refine ⟨shiftedKernel_nonneg p q n u, he, he.trans ?_⟩
  exact mul_le_of_le_one_right (Real.rpow_nonneg hu.le _)
    (Real.exp_le_one_iff.mpr (by linarith))

theorem majorant_integrable : S.majorantIntegrability := by
  intro q hq
  have hi : IntegrableOn (fun u : ℝ => gammaKernel q (u*(1/2))) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_right_iff (gammaKernel q) 0 (by norm_num : (0 : ℝ) < 1/2)).mpr
    simpa using gammaKernel_integrable hq
  apply IntegrableOn.congr_fun (hi.const_mul ((2 : ℝ)^(q-1))) _ measurableSet_Ioi
  intro u hu
  change (2 : ℝ)^(q-1) * ((u*(1/2))^(q-1)*Real.exp (-(u*(1/2)))) =
    u^(q-1)*Real.exp (-u/2)
  rw [← mul_assoc, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
    (mul_nonneg hu.le (by norm_num : (0 : ℝ) ≤ 1/2))]
  congr 2 <;> ring

theorem shifted_integrable : S.integrability := by
  intro p q hp hq n hn
  have hm : AEStronglyMeasurable (shiftedKernel p q n) (volume.restrict (Ioi 0)) := by
    apply AEStronglyMeasurable.indicator _ measurableSet_Ioc
    exact ((measurable_id.pow_const (q-1)).mul
      ((measurable_const.sub (measurable_id.div_const (n : ℝ))).pow_const
        ((n : ℝ)+p-1))).aestronglyMeasurable
  apply (majorant_integrable q hq).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (shiftedKernel_nonneg p q n u)]
  exact (shifted_domination p q hp n hn u hu).2.1

/-- The zero extension is continuous at the moving upper endpoint because
its exponent is positive once n ≥ 2. -/
theorem shiftedKernel_eq_max (p q : ℝ) (hp : 0 < p) (n : ℕ) (hn : 2 ≤ n)
    (u : ℝ) (hu : 0 < u) :
    shiftedKernel p q n u = u^(q-1) * (max (1-u/(n : ℝ)) 0)^((n : ℝ)+p-1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have ha : (n : ℝ)+p-1 ≠ 0 := by linarith
  by_cases hun : u ≤ (n : ℝ)
  · rw [shiftedKernel, S.shiftedKernelValue,
      indicator_of_mem (show u ∈ Ioc 0 (n : ℝ) from ⟨hu, hun⟩),
      max_eq_left (sub_nonneg.mpr ((div_le_one hnpos).mpr hun))]
  · have hb : 1-u/(n : ℝ) ≤ 0 := by
      have : 1 < u/(n : ℝ) := (lt_div_iff₀ hnpos).mpr (by linarith)
      linarith
    simp [shiftedKernel, S.shiftedKernelValue,
      indicator_of_notMem (show u ∉ Ioc 0 (n : ℝ) from fun h => hun h.2),
      max_eq_right hb, Real.zero_rpow ha]

theorem shiftedKernel_continuousAt (p q : ℝ) (hp : 0 < p) (n : ℕ) (hn : 2 ≤ n)
    (u : ℝ) (hu : 0 < u) : ContinuousAt (shiftedKernel p q n) u := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 ≤ (n : ℝ)+p-1 := by linarith
  have hc : ContinuousAt (fun x : ℝ =>
      x^(q-1) * (max (1-x/(n : ℝ)) 0)^((n : ℝ)+p-1)) u :=
    (Real.continuousAt_rpow_const u (q-1) (Or.inl hu.ne')).mul
      (((Real.continuous_rpow_const ha).comp
        ((continuous_const.sub (continuous_id.div_const _)).max continuous_const)).continuousAt)
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu] with x hx
  exact shiftedKernel_eq_max p q hp n hn x hx

theorem shifted_proper_truncations : S.properTruncations := by
  intro p q hp n hn a b ha hab
  exact positive_continuous_darboux (shiftedKernel_continuousAt p q hp n hn) ha hab

theorem shifted_near_zero_bound : S.nearZeroBound := by
  intro p q hp hq η hη n hn
  have hi : IntervalIntegrable (shiftedKernel p q n) volume 0 η :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hη.le).mpr
      ((shifted_integrable p q hp hq n hn).mono_set Ioc_subset_Ioi_self)
  have hpow : IntervalIntegrable (fun u : ℝ => u^(q-1)) volume 0 η :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  refine ⟨intervalIntegral.integral_nonneg hη.le (fun u _ => shiftedKernel_nonneg p q n u), ?_⟩
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hη.le hi hpow
    (fun u hu => (shifted_domination p q hp n hn u hu.1).2.2)
  have he : (∫ u in (0 : ℝ)..η, u^(q-1)) = η^q/q := by
    rw [integral_rpow (Or.inl (by linarith : -1 < q-1))]
    simp [Real.zero_rpow hq.ne']
  exact h.trans_eq he

theorem shifted_tail_bound : S.tailBound := by
  intro p q hp hq R hR n hn
  refine ⟨integral_nonneg (fun _ => shiftedKernel_nonneg p q n _), ?_⟩
  apply setIntegral_mono_on
    ((shifted_integrable p q hp hq n hn).mono_set (Ioi_subset_Ioi hR.le))
    ((majorant_integrable q hq).mono_set (Ioi_subset_Ioi hR.le)) measurableSet_Ioi
  intro u hu
  exact (shifted_domination p q hp n hn u (hR.trans hu)).2.1

theorem shifted_uniform_small_tails : S.uniformSmallTails := by
  intro p q hp hq ε hε
  have h := (tendsto_order.mp (tendsto_integral_Ioi_zero
    (f := fun u : ℝ => u^(q-1)*Real.exp (-u/2)) (μ := volume) tendsto_id)).2 ε hε
  obtain ⟨A, hA⟩ := eventually_atTop.mp h
  refine ⟨max A 1, zero_lt_one.trans_le (le_max_right _ _), fun n hn => ?_⟩
  exact (shifted_tail_bound p q hp hq _ (zero_lt_one.trans_le (le_max_right _ _)) n hn).2.trans_lt
    (hA _ (le_max_left _ _))

/-- Domination is needed only eventually; discard n=0,1 before applying
one-dimensional dominated convergence. All Darboux endpoint limits and their
uniform bounds have been established independently above. -/
theorem kernel_integral_limit : S.kernelIntegralLimit := by
  intro p q hp hq
  have hlim : Tendsto (fun n : ℕ => ∫ u in Ioi (0 : ℝ), shiftedKernel p q (n+2) u)
      atTop (𝓝 (∫ u in Ioi (0 : ℝ), gammaKernel q u)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun u : ℝ => u^(q-1)*Real.exp (-u/2))
      (fun n => (shifted_integrable p q hp hq (n+2) (by omega)).1)
      (majorant_integrable q hq)
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      change ‖shiftedKernel p q (n+2) u‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (shiftedKernel_nonneg p q (n+2) u)]
      exact (shifted_domination p q hp (n+2) (by omega) u hu).2.1
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact ((compact_uniform p q u u hp hq hu le_rfl).tendsto_at ⟨le_rfl, le_rfl⟩).comp
        (tendsto_add_atTop_nat 2)
  have he : (∫ u in Ioi (0 : ℝ), gammaKernel q u) = gammaIntegral q hq :=
    (intervalIntegral.integral_interval_add_Ioi (gammaKernel_integrable hq)
      ((gammaKernel_integrable hq).mono_set (Ioi_subset_Ioi zero_le_one))).symm
  rw [he] at hlim
  exact (tendsto_add_atTop_iff_nat 2).mp hlim

open private cut cut_pos cut_lt_half cut_tendsto trim_integrable betaTrim betaTrim_tendsto darboux_congr
  from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.BetaRecurrence

/-- Increasing a positive Beta parameter decreases its integral. This uses
proper Darboux comparisons, then the already proved independent endpoint limits. -/
theorem beta_antitone_left {p r q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpr : p ≤ r) :
    beta r q ≤ beta p q := by
  apply le_of_tendsto_of_tendsto' (betaTrim_tendsto r q (hp.trans_le hpr) hq)
    (betaTrim_tendsto p q hp hq)
  intro n
  apply Riemann.realIntegral_mono _ _ (trim_integrable r q n) (trim_integrable p q n)
  intro t ht
  have ht0 : 0 < t := (cut_pos n).trans_le ht.1
  have ht1 : t < 1 := ht.2.trans_lt (by linarith [cut_pos n])
  change realPower t (r-1)*realPower (1-t) (q-1) ≤
    realPower t (p-1)*realPower (1-t) (q-1)
  rw [realPower_eq_rpow t ht0, realPower_eq_rpow t ht0,
    realPower_eq_rpow (1-t) (sub_pos.mpr ht1)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le (by linarith))
    (Real.rpow_nonneg (by linarith) _)

/-- Euler approximants with a fixed natural shift, normalized by (n+1)^q. -/
theorem shifted_euler_limit (q : ℝ) (hq : 0 < q) (k : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ)+1)^q * beta q ((n : ℝ)+k+1))
      atTop (𝓝 (gammaIntegral q hq)) := by
  have hr : Tendsto (fun n : ℕ => ((n : ℝ)+1)/((n : ℝ)+k)) atTop (𝓝 1) := by
    simpa [add_comm, one_mul] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ) 1 (k : ℝ) 1
        (d := 1) one_ne_zero)
  have hp := hr.rpow_const (p := q) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at hp
  have he := (EulerBetaApproximation.euler_beta_approximation q hq).comp
    (tendsto_add_atTop_nat k)
  have hh := hp.mul he
  rw [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnk : 0 < (n : ℝ)+(k : ℝ) := add_pos_of_pos_of_nonneg hnR (Nat.cast_nonneg k)
  dsimp only [Function.comp_def]
  simp only [Nat.cast_add]
  rw [Real.div_rpow (by linarith : 0 ≤ (n : ℝ)+1) hnk.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hnk q)]

/-- Squeeze between two shifted Euler approximants. No Beta--Gamma formula,
double integral, or Gamma ratio asymptotic is used. -/
theorem shifted_beta_limit : S.shiftedBetaLimit := by
  intro p q hp hq
  obtain ⟨k, hk⟩ := exists_nat_gt p
  have hl := shifted_euler_limit q hq k
  have hu := shifted_euler_limit q hq 0
  simp only [Nat.cast_zero, add_zero] at hu
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ)+1)^q * beta (p+((n : ℝ)+1)) q)
      atTop (𝓝 (gammaIntegral q hq)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
    · intro n
      change ((n : ℝ)+1)^q * beta q ((n : ℝ)+k+1) ≤
        ((n : ℝ)+1)^q * beta (p+((n : ℝ)+1)) q
      have hs : beta q ((n : ℝ)+k+1) = beta ((n : ℝ)+k+1) q :=
        beta_symmetry q ((n : ℝ)+k+1) hq (by positivity)
      rw [hs]
      exact mul_le_mul_of_nonneg_left
        (beta_antitone_left (by positivity) hq (by linarith))
        (Real.rpow_nonneg (by positivity) _)
    · intro n
      change ((n : ℝ)+1)^q * beta (p+((n : ℝ)+1)) q ≤
        ((n : ℝ)+1)^q * beta q ((n : ℝ)+1)
      have hs : beta q ((n : ℝ)+1) = beta ((n : ℝ)+1) q :=
        beta_symmetry q ((n : ℝ)+1) hq (by positivity)
      rw [hs]
      exact mul_le_mul_of_nonneg_left
        (beta_antitone_left (by positivity) hq (by linarith))
        (Real.rpow_nonneg (by positivity) _)
  change Tendsto (fun n : ℕ => (n : ℝ)^q * beta (p+n) q) atTop (𝓝 (gammaIntegral q hq))
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hlim

theorem beta_interval_of_one_lt (q r : ℝ) (hq : 0 < q) (hr : 1 < r) :
    beta q r = ∫ t in (0 : ℝ)..1, t^(q-1)*(1-t)^(r-1) := by
  let f : ℝ → ℝ := fun t => t^(q-1)*(1-t)^(r-1)
  have hc : ∀ t : ℝ, 0 < t → ContinuousAt f t := by
    intro t ht
    exact (Real.continuousAt_rpow_const t (q-1) (Or.inl ht.ne')).mul
      (((Real.continuous_rpow_const (by linarith : 0 ≤ r-1)).comp
        (continuous_const.sub continuous_id)).continuousAt)
  have hi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q-1)).mul_continuousOn
      (((Real.continuous_rpow_const (by linarith : 0 ≤ r-1)).comp
        (continuous_const.sub continuous_id)).continuousOn)
  have hF : ContinuousOn (fun b => ∫ t in (0 : ℝ)..b, f t) (Icc 0 1) := by
    simpa only [uIcc_of_le zero_le_one] using
      intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have hcm (m : ℕ) : cut m ∈ Icc (0 : ℝ) 1 := ⟨(cut_pos m).le, by linarith [cut_lt_half m]⟩
  have hdm (m : ℕ) : 1-cut m ∈ Icc (0 : ℝ) 1 := ⟨by linarith [cut_lt_half m], by linarith [cut_pos m]⟩
  have hleft := (hF 0 ⟨le_rfl, zero_le_one⟩).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨cut_tendsto, Eventually.of_forall hcm⟩)
  have hright := (hF 1 ⟨zero_le_one, le_rfl⟩).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr
      ⟨show Tendsto (fun m => 1-cut m) atTop (𝓝 (1 : ℝ)) by simpa using tendsto_const_nhds.sub cut_tendsto,
        Eventually.of_forall hdm⟩)
  have hlim := hright.sub hleft
  simp only [intervalIntegral.integral_same, sub_zero] at hlim
  apply tendsto_nhds_unique (betaTrim_tendsto q r hq (by linarith))
  apply hlim.congr
  intro m
  have h0 := hi.mono_set (show uIcc (0 : ℝ) (cut m) ⊆ uIcc 0 1 by
    rw [uIcc_of_le (cut_pos m).le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl (hcm m).2)
  have h1 := hi.mono_set (show uIcc (cut m) (1-cut m) ⊆ uIcc 0 1 by
    rw [uIcc_of_le (by linarith [cut_lt_half m]), uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (cut_pos m).le (hdm m).2)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0 h1
  have hval : betaTrim q r m = ∫ t in cut m..1-cut m, f t := by
    obtain ⟨hd, hv⟩ := positive_continuous_darboux (b := 1-cut m) hc (cut_pos m) (by linarith [cut_lt_half m])
    exact (darboux_congr (trim_integrable q r m) hd (fun t ht => by
      have ht0 := (cut_pos m).trans_le ht.1
      have ht1 : t < 1 := by linarith [ht.2, cut_pos m]
      change realPower t (q-1)*realPower (1-t) (r-1) = _
      rw [realPower_eq_rpow t ht0, realPower_eq_rpow (1-t) (sub_pos.mpr ht1)])).trans hv
  rw [hval]
  change (∫ t in (0 : ℝ)..1-cut m, f t) - (∫ t in (0 : ℝ)..cut m, f t) = _
  linarith



theorem scaled_beta_integral (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n) :
    (n : ℝ)^q * beta (p+n) q = ∫ u in (0 : ℝ)..(n : ℝ),
      u^(q-1)*(1-u/n)^((n : ℝ)+p-1) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let f : ℝ → ℝ := fun t => t^(q-1)*(1-t)^((n : ℝ)+p-1)
  have hb : beta (p+n) q = ∫ t in (0 : ℝ)..1, f t := by
    have hs : beta (p+n) q = beta q (p+n) := beta_symmetry _ _ (by positivity) hq
    rw [hs, beta_interval_of_one_lt q (p+n) hq (by linarith)]
    congr 1
    funext t
    dsimp [f]
    congr 2 <;> ring
  have hsub := intervalIntegral.integral_comp_div f hnR.ne' (a := 0) (b := (n : ℝ))
  simp only [zero_div, div_self hnR.ne', smul_eq_mul] at hsub
  have he : (∫ u in (0 : ℝ)..(n : ℝ), u^(q-1)*(1-u/n)^((n : ℝ)+p-1)) =
      (n : ℝ)^(q-1) * ∫ u in (0 : ℝ)..(n : ℝ), f (u/n) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hnR.le
    intro u hu
    dsimp [f]
    rw [← mul_assoc, ← Real.mul_rpow hnR.le (div_nonneg hu.1.le hnR.le),
      mul_div_cancel₀ _ hnR.ne']
  rw [he, hsub, ← mul_assoc, ← Real.rpow_add_one hnR.ne', sub_add_cancel, ← hb]


/-- The manuscript's finite scaling identity, with the Beta value defined by
independent improper Darboux limits. Only one-variable dilation is used. -/
theorem shifted_scaled_integral : S.scaledIntegral := by
  intro p q hp hq n hn
  change (n : ℝ)^q * beta (p+n) q = ∫ u in Ioi (0 : ℝ), shiftedKernel p q n u
  rw [scaled_beta_integral p q hp hq n hn,
    intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
  change _ = ∫ u in Ioi (0 : ℝ), (Ioc (0 : ℝ) (n : ℝ)).indicator
    (fun u : ℝ => u^(q-1)*(1-u/n)^((n : ℝ)+p-1)) u
  rw [integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]

theorem shifted_independent_improper : S.independentImproper := by
  intro p q hp hq n hn
  have he : (n : ℝ)^q * Specs.SingleVariableAnalysis.Ch18.BetaDefinition.betaValue (p+n) q =
      ∫ u in Ioi (0 : ℝ), S.shiftedKernelValue p q n u :=
    shifted_scaled_integral p q hp hq n (by omega)
  rw [he]
  have hi := shifted_integrable p q hp hq n hn
  obtain ⟨hl, hr⟩ := positive_integrable_independent (shiftedKernel_continuousAt p q hp n hn) hi
  refine ⟨?_, ⟨1, WithBot.coe_lt_coe.mpr zero_lt_one, WithTop.coe_lt_top _⟩,
    _, _, hl, hr, ?_⟩
  · intro a b ha hab _
    exact (shifted_proper_truncations p q hp n hn a b (WithBot.coe_lt_coe.mp ha) hab).choose
  · exact (intervalIntegral.integral_interval_add_Ioi hi
      (hi.mono_set (Ioi_subset_Ioi zero_le_one))).symm

end SingleVariableAnalysis.ShiftedBetaLimit
