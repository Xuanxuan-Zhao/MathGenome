import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.VarianceWeakLaw
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.ConvergenceComparisons
import Mathlib.Probability.Moments.Variance

open MeasureTheory Filter
open scoped ENNReal Topology

universe u
namespace ProbabilityFoundations.Ch08
open Specs.ProbabilityFoundations.Ch08.VarianceWeakLaw
open Specs.ProbabilityFoundations.Ch01.ProbabilityBounds

private theorem partialSum_memLp {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hX : ∀ k, 1 ≤ k → MemLp (X k) 2 P) (n : ℕ) :
    MemLp (partialSum X n) 2 P := by
  exact memLp_finsetSum _ (fun k hk => hX k (Finset.mem_Icc.mp hk).1)

private theorem partialSum_measurable {Ω : Type u} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, 1 ≤ k → Measurable (X k)) (n : ℕ) :
    Measurable (partialSum X n) := by
  exact Finset.measurable_sum _ (fun k hk => hX k (Finset.mem_Icc.mp hk).1)

private theorem variance_partialSum {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, 1 ≤ k → MemLp (X k) 2 P)
    (hcov : ∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j →
      ProbabilityTheory.covariance (X i) (X j) P = 0) (n : ℕ) :
    ProbabilityTheory.variance (partialSum X n) P =
      ∑ k ∈ Finset.Icc 1 n, realVarianceValue P (X k) := by
  change ProbabilityTheory.variance (fun ω => ∑ k ∈ Finset.Icc 1 n, X k ω) P = _
  rw [ProbabilityTheory.variance_fun_sum'
    (fun k hk => hX k (Finset.mem_Icc.mp hk).1)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single_of_mem i hi]
  · rw [ProbabilityTheory.covariance_self (hX i (Finset.mem_Icc.mp hi).1).aemeasurable]
    exact ProbabilityTheory.variance_eq_integral (hX i (Finset.mem_Icc.mp hi).1).aemeasurable
  · intro j hj hji
    exact hcov i j (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1 hji.symm

/-- The off-diagonal covariances vanish, leaving exactly the normalized variance sum. -/
theorem centered_second_moment : centeredSecondMomentType := by
  intro Ω mΩ P hP X hXm hX hcov n hn
  have hsum := variance_partialSum P X hX hcov n
  rw [ProbabilityTheory.variance_eq_integral (partialSum_measurable X hXm n).aemeasurable] at hsum
  simp only [centeredAverage, sq_abs, div_pow, integral_div]
  rw [hsum]
  simp [zpow_neg, div_eq_mul_inv, mul_comm]

/-- The variance criterion gives moment L² convergence and hence convergence in probability. -/
theorem variance_weak_law : varianceWeakLawType := by
  intro Ω mΩ P hP X hXm hX hcov hvar
  have hmem (n : ℕ) : MemLp (centeredAverage P X n) 2 P := by
    have h := (partialSum_memLp P X hX n).sub (memLp_const (∫ t, partialSum X n t ∂P))
    change MemLp (fun ω => (partialSum X n ω - ∫ t, partialSum X n t ∂P) / (n : ℝ)) 2 P
    simpa only [div_eq_inv_mul, Pi.sub_apply] using h.const_mul ((n : ℝ)⁻¹)
  have hmeas (n : ℕ) : Measurable (centeredAverage P X n) :=
    ((partialSum_measurable X hXm n).sub_const _).div_const _
  have hmoment : Tendsto (fun n => ∫ ω, |centeredAverage P X n ω| ^ 2 ∂P)
      atTop (𝓝 0) := by
    apply hvar.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (centered_second_moment P X hXm hX hcov n hn).symm
  refine ⟨hmem, hmoment, ?_⟩
  apply ProbabilityFoundations.Ch02.lp_implies_probability P (centeredAverage P X)
    (fun _ => 0) 2 hmeas measurable_const (by norm_num)
  · simpa using hmem
  · simp
  · simpa only [sub_zero, Real.rpow_two] using hmoment

end ProbabilityFoundations.Ch08
