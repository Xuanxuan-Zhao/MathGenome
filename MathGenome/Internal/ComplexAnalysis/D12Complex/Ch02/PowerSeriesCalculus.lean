import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.PowerSeriesCalculus
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.PowerSeriesRadius
import Mathlib.Analysis.Calculus.FDeriv.Analytic

open Filter
open scoped Topology NNReal ENNReal

/-! Direct power-series calculus. The analytic API used here starts from an
actual convergent formal series; no theorem converting weak holomorphy to a
power-series expansion is used. The radius is the upstream root-limsup radius.
-/

namespace D12Complex.PowerSeriesCalculus

private noncomputable def evalOne : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ 1

/-- Evaluating the formal Fréchet derivative at 1 gives the scalar derivative coefficients. -/
private theorem derivSeries_scalar (c : ℕ → ℂ) :
    evalOne.compFormalMultilinearSeries (FormalMultilinearSeries.ofScalars ℂ c).derivSeries =
      FormalMultilinearSeries.ofScalars ℂ (derivativeCoefficients c) := by
  ext n
  rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  congr 1
  change (FormalMultilinearSeries.ofScalars ℂ c).derivSeries.coeff n 1 = _
  simp [derivativeCoefficients, nsmul_eq_mul]

private theorem radius_shift_scalar (c : ℕ → ℂ) :
    (FormalMultilinearSeries.ofScalars ℂ (fun n => c (n + 1))).radius =
      (FormalMultilinearSeries.ofScalars ℂ c).radius := by
  have hn (n : ℕ) :
      ‖FormalMultilinearSeries.ofScalars ℂ (fun n => c (n + 1)) n‖ =
      ‖(FormalMultilinearSeries.ofScalars ℂ c).shift n‖ := by
    simp [FormalMultilinearSeries.shift]
  exact (le_antisymm (FormalMultilinearSeries.radius_le_of_le (fun n => (hn n).ge))
    (FormalMultilinearSeries.radius_le_of_le (fun n => (hn n).le))).trans
    (FormalMultilinearSeries.radius_shift _)

/-- The formal derivative estimate gives one inequality. The reverse follows
from coefficient domination and invariance under deleting the constant term.
Neither inequality requires a positive or finite radius. -/
theorem radius_derivative (c : ℕ → ℂ) : powerSeriesRadius (derivativeCoefficients c) = powerSeriesRadius c := by
  simp only [PowerSeriesRadius.radius_eq_formal]
  apply le_antisymm
  · apply le_trans (FormalMultilinearSeries.radius_le_of_le (p :=
        FormalMultilinearSeries.ofScalars ℂ (fun n => c (n + 1))) ?_)
      (radius_shift_scalar c).le
    intro n
    simp only [FormalMultilinearSeries.ofScalars_norm, derivativeCoefficients, norm_mul,
      Complex.norm_natCast]
    exact le_mul_of_one_le_left (norm_nonneg _) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  · have h := (FormalMultilinearSeries.ofScalars ℂ c).radius_le_radius_derivSeries
    have h' := (FormalMultilinearSeries.ofScalars ℂ c).derivSeries.radius_le_radius_continuousLinearMap_comp evalOne
    rw [derivSeries_scalar] at h'
    exact h.trans h'


theorem iteratedCoefficients_formula (c : ℕ → ℂ) (k n : ℕ) :
    iteratedCoefficients c k n = ((n + 1).ascFactorial k : ℂ) * c (n + k) := by
  induction k generalizing n with
  | zero => simp [iteratedCoefficients]
  | succ k ih =>
    simp only [iteratedCoefficients, derivativeCoefficients, ih, ← mul_assoc, ← Nat.cast_mul]
    rw [Nat.succ_ascFactorial, ← Nat.ascFactorial_succ]
    congr 2; omega

theorem radius_iterated (c : ℕ → ℂ) (k : ℕ) :
    powerSeriesRadius (iteratedCoefficients c k) = powerSeriesRadius c := by
  induction k with
  | zero => rfl
  | succ k ih => exact (radius_derivative _).trans ih

private theorem derivative_primitive (c : ℕ → ℂ) :
    derivativeCoefficients (primitiveCoefficients c) = c := by
  funext n
  simp only [derivativeCoefficients, primitiveCoefficients]
  exact mul_div_cancel₀ _ (by exact_mod_cast Nat.succ_ne_zero n)

theorem radius_primitive (c : ℕ → ℂ) :
    powerSeriesRadius (primitiveCoefficients c) = powerSeriesRadius c := by
  rw [← radius_derivative, derivative_primitive]

private theorem hasFPowerSeries_sum (c : ℕ → ℂ) (a : ℂ)
    (hr : 0 < powerSeriesRadius c) :
    HasFPowerSeriesOnBall (seriesSum c a) (FormalMultilinearSeries.ofScalars ℂ c)
      a (powerSeriesRadius c) := by
  refine ⟨(PowerSeriesRadius.radius_eq_formal c).le, hr, ?_⟩
  intro y hy
  have h := PowerSeriesRadius.summable_inside c a (a + y) (by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm] using hy)
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, seriesSum, smul_eq_mul, mul_comm] using h.hasSum

private theorem hasFPowerSeries_deriv {f : ℂ → ℂ} {c : ℕ → ℂ} {a : ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) a r) :
    HasFPowerSeriesOnBall (deriv f) (FormalMultilinearSeries.ofScalars ℂ (derivativeCoefficients c)) a r := by
  have h' := evalOne.comp_hasFPowerSeriesOnBall h.fderiv
  rw [derivSeries_scalar] at h'
  exact h'

theorem hasDerivAt_sum (c : ℕ → ℂ) (a z : ℂ) (hz : z ∈ convergenceDisk c a) :
    HasDerivAt (seriesSum c a) (seriesSum (derivativeCoefficients c) a z) z := by
  have hr : 0 < powerSeriesRadius c := lt_of_le_of_lt (bot_le : (0 : ℝ≥0∞) ≤ _) hz
  have h := hasFPowerSeries_sum c a hr
  have hd := hasFPowerSeries_deriv h
  have heq := hd.sum (y := z - a) (by
    simpa [convergenceDisk, Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm] using hz)
  have hf := (h.hasFDerivAt (y := z - a) hz).hasDerivAt
  have hdiff : DifferentiableAt ℂ (seriesSum c a) z := by
    simpa using hf.differentiableAt
  convert hdiff.hasDerivAt using 1
  simpa [FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq,
    seriesSum, smul_eq_mul, mul_comm] using heq.symm

private theorem disk_eq_eball (c : ℕ → ℂ) (a : ℂ) :
    convergenceDisk c a = Metric.eball a (powerSeriesRadius c) := by
  ext z
  simp [convergenceDisk, Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm]

theorem holomorphic_sum (c : ℕ → ℂ) (a : ℂ) :
    HolomorphicOn (convergenceDisk c a) (seriesSum c a) := by
  refine ⟨?_, fun z hz => (hasDerivAt_sum c a z hz).differentiableAt⟩
  rw [disk_eq_eball]
  exact Metric.isOpen_eball

private theorem hasFPowerSeries_iterated (c : ℕ → ℂ) (a : ℂ) (k : ℕ)
    (hr : 0 < powerSeriesRadius c) :
    HasFPowerSeriesOnBall (iteratedDeriv k (seriesSum c a))
      (FormalMultilinearSeries.ofScalars ℂ (iteratedCoefficients c k))
      a (powerSeriesRadius c) := by
  induction k with
  | zero => exact hasFPowerSeries_sum c a hr
  | succ k ih => simpa only [iteratedDeriv_succ, iteratedCoefficients] using hasFPowerSeries_deriv ih

theorem iteratedDeriv_sum (c : ℕ → ℂ) (a z : ℂ) (k : ℕ)
    (hz : z ∈ convergenceDisk c a) :
    iteratedDeriv k (seriesSum c a) z = seriesSum (iteratedCoefficients c k) a z := by
  have h := (hasFPowerSeries_iterated c a k (lt_of_le_of_lt (bot_le : (0 : ℝ≥0∞) ≤ _) hz)).sum
    (y := z - a) (by
      simpa [convergenceDisk, Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm] using hz)
  simpa [FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq,
    seriesSum, smul_eq_mul, mul_comm] using h


private theorem closedBall_subset_disk (c : ℕ → ℂ) (a : ℂ) (r : ℝ)
    (h : ENNReal.ofReal r < powerSeriesRadius c) :
    Metric.closedBall a r ⊆ convergenceDisk c a := by
  intro z hz
  apply lt_of_le_of_lt _ h
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  simpa [dist_eq_norm] using hz

theorem uniform_derivatives (c : ℕ → ℂ) (a : ℂ) (k : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (h : ENNReal.ofReal r < powerSeriesRadius c) :
    Summable (fun n => ‖iteratedCoefficients c k n‖ * r ^ n) ∧
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, iteratedCoefficients c k n * (z - a) ^ n)
      (iteratedDeriv k (seriesSum c a)) atTop (Metric.closedBall a r) ∧
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, ‖iteratedCoefficients c k n * (z - a) ^ n‖)
      (fun z => ∑' n, ‖iteratedCoefficients c k n * (z - a) ^ n‖)
      atTop (Metric.closedBall a r) := by
  have hh : ENNReal.ofReal r < powerSeriesRadius (iteratedCoefficients c k) := by
    rwa [radius_iterated]
  obtain ⟨hs, hu, ha⟩ := PowerSeriesRadius.uniform_closedDisk (iteratedCoefficients c k) a r hr hh
  refine ⟨hs, hu.congr_right ?_, ha⟩
  intro z hz
  exact (iteratedDeriv_sum c a z k (closedBall_subset_disk c a r h hz)).symm

theorem holomorphic_iterated (c : ℕ → ℂ) (a : ℂ) (k : ℕ) :
    HolomorphicOn (convergenceDisk c a) (iteratedDeriv k (seriesSum c a)) := by
  refine ⟨(holomorphic_sum c a).1, ?_⟩
  intro z hz
  have h := hasFPowerSeries_iterated c a k (lt_of_le_of_lt bot_le hz)
  simpa using (h.hasFDerivAt (y := z - a) hz).differentiableAt

theorem primitive_sum (c : ℕ → ℂ) (a z : ℂ) (hz : z ∈ convergenceDisk c a) :
    seriesSum (primitiveCoefficients c) a z =
      ∑' n, (c n / (n + 1 : ℕ)) * (z - a) ^ (n + 1) := by
  have h : (‖z - a‖₊ : ℝ≥0∞) < powerSeriesRadius (primitiveCoefficients c) := by
    rwa [radius_primitive]
  have hs := PowerSeriesRadius.summable_inside (primitiveCoefficients c) a z h
  simpa [seriesSum, primitiveCoefficients] using hs.tsum_eq_zero_add

theorem hasDerivAt_primitive (c : ℕ → ℂ) (a z : ℂ) (hz : z ∈ convergenceDisk c a) :
    HasDerivAt (seriesSum (primitiveCoefficients c) a) (seriesSum c a z) z := by
  have h : z ∈ convergenceDisk (primitiveCoefficients c) a := by
    simpa only [convergenceDisk, Set.mem_ofPred_eq, radius_primitive] using hz
  simpa only [derivative_primitive] using hasDerivAt_sum (primitiveCoefficients c) a z h

private theorem sum_center (c : ℕ → ℂ) (a : ℂ) : seriesSum c a a = c 0 := by
  simp [seriesSum, zero_pow_eq]

theorem coefficient_identification (c : ℕ → ℂ) (a : ℂ) (n : ℕ)
    (hr : 0 < powerSeriesRadius c) :
    c n = iteratedDeriv n (seriesSum c a) a / (n.factorial : ℂ) := by
  have h : a ∈ convergenceDisk c a := by
    simpa [convergenceDisk] using hr
  rw [iteratedDeriv_sum c a a n h, sum_center, iteratedCoefficients_formula]
  simp only [zero_add, Nat.one_ascFactorial]
  exact (mul_div_cancel_left₀ (c n) (by exact_mod_cast Nat.factorial_ne_zero n)).symm

end D12Complex.PowerSeriesCalculus

