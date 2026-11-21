import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.SteinProblem5Caution
import MathGenome.Internal.RealAnalysis.D11.Ch05.AtomicIntegrals
import Mathlib.Analysis.SpecificLimits.Basic

/-! The bounded discrete probability space in paper.tex:5627–5633.
We use the upstream atomic-integral formula for the shared source integral,
then compute every weighted value as one. The scalar nonintegrability and
failure of a finite-valued integration assignment are consequences of that
extended nonnegative integral, never of a totalized scalar integral.
-/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace D11.Ch19.SteinProblem5Caution
open Specs.D11.Ch19.SteinProblem5Caution

private theorem distance (x y : Space) : dist x y = if x = y then 0 else 1 := rfl

private instance : DiscreteTopology Space :=
  DiscreteTopology.of_forall_le_dist (by norm_num : (0 : ℝ) < 1)
    (fun x y h => by simp [distance, h])

private theorem closedBall_one (x : Space) : Metric.closedBall x 1 = univ := by
  ext y
  simp only [Metric.mem_closedBall, mem_univ, iff_true]
  by_cases h : y = x <;> simp [distance, h]

private theorem enum_index (k : ℕ) : ((enumeration k).index : ℕ) = k + 1 := rfl

private theorem measure_singleton (x : Space) : atomicMeasure {x} = weight x := by
  rw [atomicMeasure, Measure.sum_apply _ (measurableSet_singleton x)]
  rw [tsum_eq_single (enumeration.symm x)]
  · simp
  · intro k hk
    have hne : enumeration k ≠ x := by
      intro h
      apply hk
      exact enumeration.injective (h.trans (enumeration.apply_symm_apply x).symm)
    simp [hne]

private theorem total_mass : atomicMeasure univ = 1 := by
  simp only [atomicMeasure, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  simp only [weight, enum_index, ENNReal.tsum_geometric_add_one]
  rw [ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)

private theorem function_nonnegative (x : Space) : 0 ≤ testFunction x := by
  exact pow_nonneg (by norm_num) _

private theorem infinite_integral :
    Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value atomicMeasure
      (fun x => ENNReal.ofReal (testFunction x)) = ∞ := by
  rw [show atomicMeasure = Measure.sum (fun k : ℕ =>
    weight (enumeration k) • Measure.dirac (enumeration k)) from rfl]
  rw [D11.Ch05.AtomicIntegrals.atomic_integral _ _ _ (measurable_of_countable _)]
  have hterm (k : ℕ) : weight (enumeration k) *
      ENNReal.ofReal (testFunction (enumeration k)) = 1 := by
    simp only [weight, testFunction, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num only [ENNReal.ofReal_ofNat]
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  simp_rw [hterm]
  simp

private theorem not_integrable : ¬ Integrable testFunction atomicMeasure := by
  intro h
  have hfinite := h.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfinite
  have heq : (fun x : Space => ‖testFunction x‖ₑ) =
      (fun x => ENNReal.ofReal (testFunction x)) := by
    funext x
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (function_nonnegative x)]
  rw [heq] at hfinite
  have htop := infinite_integral
  change D11.Ch05.NonnegativeIntegral.nonnegativeIntegral atomicMeasure
    (fun x => ENNReal.ofReal (testFunction x)) = ∞ at htop
  rw [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral] at htop
  rw [htop] at hfinite
  exact (lt_irrefl _ hfinite)

theorem counterexample : Specs.D11.Ch19.SteinProblem5Caution.counterexample := by
  refine ⟨distance, fun _ => continuous_of_discreteTopology, ?_, measure_singleton,
    total_mass, ?_, closedBall_one, continuous_of_discreteTopology, function_nonnegative,
    ?_, infinite_integral, not_integrable, ?_⟩
  · intro E
    refine ⟨E.to_countable.measurableSet, ?_⟩
    apply (Metric.isBounded_iff_subset_closedBall (enumeration 0)).2
    exact ⟨1, by rw [closedBall_one]; exact subset_univ _⟩
  · intro x r
    constructor <;> exact (measure_mono (subset_univ _)).trans_lt (by rw [total_mass]; exact ENNReal.one_lt_top)
  · intro x
    rw [closedBall_one]
    exact subset_univ _
  · rintro ⟨I, hI⟩
    have h := hI testFunction continuous_of_discreteTopology
      ⟨enumeration 0, 1, by rw [closedBall_one]; exact subset_univ _⟩ function_nonnegative
    rw [infinite_integral] at h
    exact ENNReal.ofReal_ne_top h

end D11.Ch19.SteinProblem5Caution
