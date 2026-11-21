import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.RealPartPolynomial
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Metric Complex
open scoped Topology ComplexConjugate

namespace D12Complex.RealPartPolynomial

private lemma mean {h : ℂ → ℂ} (hh : Differentiable ℂ h) (r : ℝ) :
    Real.circleAverage h 0 r = h 0 := by
  apply DiffContOnCl.circleAverage
  exact ⟨hh.differentiableOn, hh.continuous.continuousOn⟩

private lemma coefficient_average {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Real.circleAverage (fun z => h z / z^n) 0 r = Taylor.coefficients h 0 n := by
  rw [Real.circleAverage_eq_circleIntegral hr.ne']
  have hc := circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    (f := h) (c := 0) hr n countable_empty hh.continuous.continuousOn
    (fun z _ => hh z)
  simp only [sub_zero, smul_eq_mul, one_div] at hc
  have he : (fun z : ℂ => z⁻¹ * (h z / z^n)) =
      (fun z => (z^(n+1))⁻¹ * h z) := by
    funext z
    simp [pow_succ, mul_inv_rev, div_eq_mul_inv, mul_comm, mul_left_comm]
  simp only [sub_zero, smul_eq_mul]
  rw [he, hc]
  unfold Taylor.coefficients
  field_simp [two_pi_I_ne_zero]

private lemma conjugate_average_zero {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 1 ≤ n) :
    Real.circleAverage (fun z => conj (h z) / z^n) 0 r = 0 := by
  have hprod : Differentiable ℂ (fun z => h z * z^n) := hh.mul (differentiable_id.pow n)
  have hm : Real.circleAverage (fun z => conj (h z * z^n)) 0 r = 0 := by
    have he := conjCLE.toContinuousLinearMap.circleAverage_comp_comm (c := 0)
      (hprod.continuous.continuousOn.circleIntegrable hr.le)
    simpa [Function.comp_def, mean hprod r, zero_pow (by omega : n ≠ 0)] using he
  have he : Real.circleAverage (fun z => conj (h z) / z^n) 0 r =
      ((r : ℂ)^(2*n))⁻¹ * Real.circleAverage (fun z => conj (h z * z^n)) 0 r := by
    rw [← smul_eq_mul, ← Real.circleAverage_fun_smul]
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hzN : ‖z‖ = r := by simpa [abs_of_pos hr, mem_sphere_iff_norm] using hz
    have hzz : z * conj z = (r : ℂ)^2 := by
      rw [mul_conj, normSq_eq_norm_sq, hzN]
      norm_cast
    have hz0 : z ≠ 0 := by intro he; simp [he] at hzN; linarith
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    simp only [smul_eq_mul, map_mul, map_pow]
    have hp : z^n * (conj z)^n = (r : ℂ)^(2*n) := by
      rw [← mul_pow, hzz, pow_mul]
    field_simp
    rw [← hp]
    ring
  rw [he, hm, mul_zero]

theorem real_part_coefficient_identity :
    Specs.D12Complex.Ch17.RealPartPolynomial.real_part_coefficient_identity_type := by
  intro h hh r hr n hn
  have hd : Differentiable ℂ h := fun z => hh.2 z (mem_univ z)
  have hz0 : ∀ z ∈ sphere (0 : ℂ) r, z^n ≠ 0 := by
    intro z hz
    apply pow_ne_zero
    intro he
    have : (0 : ℝ) = r := by simpa [he, mem_sphere_iff_norm] using hz
    exact hr.ne' this.symm
  have hc : ContinuousOn (fun z => h z / z^n) (sphere (0 : ℂ) r) :=
    hd.continuous.continuousOn.div (continuousOn_id.pow n) hz0
  have hcc : ContinuousOn (fun z => conj (h z) / z^n) (sphere (0 : ℂ) r) :=
    (continuous_conj.comp hd.continuous).continuousOn.div (continuousOn_id.pow n) hz0
  have he : (fun z => ((h z).re : ℂ) / z^n) =
      (fun z => (2 : ℂ)⁻¹ • (h z / z^n + conj (h z) / z^n)) := by
    funext z
    rw [smul_eq_mul, ← add_div, Complex.re_eq_add_conj]
    ring
  rw [he, Real.circleAverage_fun_smul,
    Real.circleAverage_fun_add (hc.circleIntegrable hr.le) (hcc.circleIntegrable hr.le),
    coefficient_average hd hr n, conjugate_average_zero hd hr hn]
  simp

/-- Integrating the nonnegative boundary deficit uses only an upper bound on Re h. -/
theorem real_part_coefficient_bound :
    Specs.D12Complex.Ch17.RealPartPolynomial.real_part_coefficient_bound_type := by
  intro h hh r B hr hB n hn
  have hd : Differentiable ℂ h := fun z => hh.2 z (mem_univ z)
  have hz0 : ∀ z ∈ sphere (0 : ℂ) r, z^n ≠ 0 := by
    intro z hz
    apply pow_ne_zero
    intro he
    have : (0 : ℝ) = r := by simpa [he, mem_sphere_iff_norm] using hz
    exact hr.ne' this.symm
  have hcont : Continuous (fun z => (h z).re) := continuous_re.comp hd.continuous
  have hi : CircleIntegrable (fun z => ((h z).re : ℂ) / z^n) 0 r :=
    ((continuous_ofReal.comp hcont).continuousOn.div
      (continuousOn_id.pow n) hz0).circleIntegrable hr.le
  have hiB : CircleIntegrable (fun z : ℂ => (B : ℂ) / z^n) 0 r :=
    (continuousOn_const.div (continuousOn_id.pow n) hz0).circleIntegrable hr.le
  have hzero : Real.circleAverage (fun z : ℂ => (B : ℂ) / z^n) 0 r = 0 := by
    simpa using conjugate_average_zero (h := fun _ => (B : ℂ)) (differentiable_const _) hr hn
  let F : ℂ → ℂ := fun z => ((B - (h z).re : ℝ) : ℂ) / z^n
  have hF : F = fun z => (B : ℂ) / z^n - ((h z).re : ℂ) / z^n := by
    funext z
    simp only [F, ofReal_sub, sub_div]
  have hav : Taylor.coefficients h 0 n = -2 * Real.circleAverage F 0 r := by
    rw [hF, Real.circleAverage_fun_sub hiB hi, hzero]
    have hid := real_part_coefficient_identity h hh r hr n hn
    linear_combination -hid
  have hmean : Real.circleAverage (fun z => (h z).re) 0 r = (h 0).re := by
    have he := reCLM.circleAverage_comp_comm (c := 0)
      (hd.continuous.continuousOn.circleIntegrable hr.le)
    simpa [Function.comp_def, mean hd r] using he
  have hnorm : Real.circleAverage (fun z => ‖F z‖) 0 r =
      (B - (h 0).re) / r^n := by
    calc
      _ = Real.circleAverage (fun z => (r^n)⁻¹ • (B - (h z).re)) 0 r := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        have hzN : ‖z‖ = r := by simpa [abs_of_pos hr, mem_sphere_iff_norm] using hz
        have hz' : z ∈ sphere (0 : ℂ) r := by simpa [abs_of_pos hr] using hz
        change ‖((B - (h z).re : ℝ) : ℂ) / z^n‖ = (r^n)⁻¹ • (B - (h z).re)
        rw [norm_div, norm_pow, hzN, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr (hB z hz'))]
        simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
      _ = _ := by
        rw [Real.circleAverage_fun_smul,
          Real.circleAverage_fun_sub (circleIntegrable_const B 0 r)
            (hcont.continuousOn.circleIntegrable hr.le), Real.circleAverage_const, hmean]
        simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hle : ‖Taylor.coefficients h 0 n‖ ≤ 2 * ((B - (h 0).re) / r^n) := by
    rw [hav, norm_mul]
    rw [show ‖(-2 : ℂ)‖ = (2 : ℝ) by norm_num]
    exact mul_le_mul_of_nonneg_left
      ((Real.norm_circleAverage_le_circleAverage_norm (f := F)).trans_eq hnorm) (by norm_num)
  have hp : 0 < r^n := pow_pos hr n
  calc
    _ ≤ (2 * ((B - (h 0).re) / r^n)) * r^n := mul_le_mul_of_nonneg_right hle hp.le
    _ = _ := by field_simp

theorem real_part_coefficient_bound_max :
    Specs.D12Complex.Ch17.RealPartPolynomial.real_part_coefficient_bound_max_type := by
  intro h hh r hr
  have hd : Differentiable ℂ h := fun z => hh.2 z (mem_univ z)
  obtain ⟨b, hb, hmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn
    ⟨circleMap 0 r 0, circleMap_mem_sphere 0 hr.le 0⟩
    (continuous_re.comp hd.continuous).continuousOn
  exact ⟨b, hb, hmax, real_part_coefficient_bound h hh r (h b).re hr hmax⟩

/-- The high coefficients vanish by taking limits along exactly the given circles. -/
theorem polynomial_of_real_part_growth :
    Specs.D12Complex.Ch17.RealPartPolynomial.polynomial_of_real_part_growth_type := by
  intro h hh p t C r ht hrTop hbound
  have hzero : ∀ n : ℕ, p < n → Taylor.coefficients h 0 n = 0 := by
    intro n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have htn : t < (n : ℝ) := by
      have : (p : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
      exact ht.trans_le this
    have hlim1 : Tendsto (fun k => (r k)^(t - (n : ℝ))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, neg_sub] using
        (tendsto_rpow_neg_atTop (sub_pos.mpr htn)).comp hrTop
    have hlim2 : Tendsto (fun k => (r k)^(-(n : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hnpos).comp hrTop
    have hlim : Tendsto
        (fun k => 2 * (C * (r k)^(t - (n : ℝ)) - (h 0).re * (r k)^(-(n : ℝ))))
        atTop (𝓝 0) := by
      simpa using (hlim1.const_mul C |>.sub (hlim2.const_mul (h 0).re)).const_mul 2
    have hle : ∀ᶠ k in atTop, ‖Taylor.coefficients h 0 n‖ ≤
        2 * (C * (r k)^(t - (n : ℝ)) - (h 0).re * (r k)^(-(n : ℝ))) := by
      filter_upwards [hrTop.eventually_gt_atTop 0] with k hk
      have hb := real_part_coefficient_bound h hh (r k) (C * (r k)^t) hk
        (hbound k) n (by omega)
      have hb' := (le_div_iff₀ (pow_pos hk n)).mpr hb
      convert hb' using 1
      rw [Real.rpow_sub hk, Real.rpow_natCast, Real.rpow_neg hk.le,
        Real.rpow_natCast]
      ring
    have hz : ‖Taylor.coefficients h 0 n‖ ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle
    exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))
  refine ⟨hzero, ?_⟩
  let Q : Polynomial ℂ := ∑ n ∈ Finset.range (p+1),
    Polynomial.monomial n (Taylor.coefficients h 0 n)
  refine ⟨Q, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro n hn
    exact (Polynomial.natDegree_monomial_le _).trans (by simpa using Finset.mem_range.mp hn)
  · intro z
    have hd : Differentiable ℂ h := fun z => hh.2 z (mem_univ z)
    have htaylor : (∑' n, Taylor.coefficients h 0 n * z^n) = h z := by
      convert Complex.taylorSeries_eq_of_entire' (c := 0) (z := z) hd using 1
      congr 1
      funext n
      simp only [Taylor.coefficients, sub_zero, div_eq_mul_inv]
      ring
    rw [← htaylor]
    change (∑' n, Taylor.coefficients h 0 n * z^n) =
      (∑ n ∈ Finset.range (p+1), Polynomial.monomial n (Taylor.coefficients h 0 n)).eval z
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    apply tsum_eq_sum
    intro n hn
    rw [hzero n (by simpa using hn), zero_mul]

theorem polynomial_of_finite_order_real_part_growth :
    Specs.D12Complex.Ch17.RealPartPolynomial.polynomial_of_finite_order_real_part_growth_type := by
  intro h hh ρ t C r _ _ ht hrTop hbound
  exact (polynomial_of_real_part_growth h hh ⌊ρ⌋₊ t C r ht hrTop hbound).2

end D12Complex.RealPartPolynomial
