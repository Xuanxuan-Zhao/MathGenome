import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.CzeroNonattainment
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.SequenceDuals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.Supplements.CzeroNonattainment
open ExpandedFA.P1.C01SequenceSpaces
open ExpandedFA.FunctionSpaces.SequenceDuals

/-- The positive geometric coefficients indexed from zero. -/
def weight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

lemma weight_pos (n : ℕ) : 0 < weight n := by
  unfold weight
  positivity

lemma weight_hasSum : HasSum weight 1 := by
  have h := hasSum_geometric_two.mul_right (1 / 2 : ℝ)
  change HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) 1
  convert h using 1 <;> norm_num [pow_succ]

lemma weight_sum (N : ℕ) : ∑ n ∈ Finset.range N, weight n = 1 - (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [weight, pow_succ]
    ring

/-- The actual ℓ¹ sequence of coefficients, with no assumed summability. -/
def coefficients (𝕜 : Type u) [RCLike 𝕜] : SequenceLp 𝕜 1 :=
  ⟨fun n => (weight n : 𝕜), by
    apply memℓp_gen
    simpa [RCLike.norm_ofReal, abs_of_pos (weight_pos _)] using weight_hasSum.summable⟩

@[simp] lemma coefficients_apply (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    coefficients 𝕜 n = (weight n : 𝕜) := rfl

lemma coefficients_norm (𝕜 : Type u) [RCLike 𝕜] : ‖coefficients 𝕜‖ = 1 := by
  have h := lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) (coefficients 𝕜)
  simpa [RCLike.norm_ofReal, abs_of_pos (weight_pos _), weight_hasSum.tsum_eq] using h

/-- Integration against exactly the coefficients of the manuscript. -/
def functional (𝕜 : Type u) [RCLike 𝕜] : SequenceC0 𝕜 →L[𝕜] 𝕜 :=
  c0SeriesFunctional (coefficients 𝕜)

lemma initialOnes_apply (𝕜 : Type u) [RCLike 𝕜] (N n : ℕ) :
    (initialOnes 𝕜 N).val n = if n < N then 1 else 0 := by
  classical
  simp only [initialOnes, Submodule.coe_sum, lp.coeFn_sum, Finset.sum_apply,
    c0Coordinate_apply]
  simp_rw [eq_comm (a := n)]
  simp

lemma initialOnes_norm_le (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) :
    ‖initialOnes 𝕜 N‖ ≤ 1 := by
  change ‖(initialOnes 𝕜 N).val‖ ≤ 1
  apply lp.norm_le_of_forall_le zero_le_one
  intro n
  rw [initialOnes_apply]
  split_ifs <;> simp

lemma functional_initialOnes (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) :
    functional 𝕜 (initialOnes 𝕜 N) = ((1 - (1 / 2 : ℝ) ^ N : ℝ) : 𝕜) := by
  change (c0SeriesFunctional (coefficients 𝕜)).toLinearMap
    (∑ n ∈ Finset.range N, c0Coordinate 𝕜 n) = _
  rw [map_sum]
  simp only [ContinuousLinearMap.coe_coe, c0SeriesFunctional_coordinate, coefficients_apply]
  rw [← RCLike.ofReal_sum, weight_sum]

lemma functional_initialOnes_tendsto (𝕜 : Type u) [RCLike 𝕜] :
    Tendsto (fun N => functional 𝕜 (initialOnes 𝕜 N)) atTop (𝓝 1) := by
  have h := (RCLike.continuous_ofReal (K := 𝕜)).continuousAt.tendsto.comp
    weight_hasSum.tendsto_sum_nat
  simpa only [Function.comp_def, weight_sum, functional_initialOnes, RCLike.ofReal_one] using h

/-- The finite initial-one vectors prove the lower bound on the operator norm. -/
lemma functional_norm (𝕜 : Type u) [RCLike 𝕜] : ‖functional 𝕜‖ = 1 := by
  apply le_antisymm
  · exact (c0SeriesFunctional_norm_le (coefficients 𝕜)).trans_eq (coefficients_norm 𝕜)
  · have h := le_of_tendsto (functional_initialOnes_tendsto 𝕜).norm
      (Eventually.of_forall fun N =>
        ((functional 𝕜).le_opNorm (initialOnes 𝕜 N)).trans
          (mul_le_of_le_one_right (norm_nonneg _) (initialOnes_norm_le 𝕜 N)))
    simpa using h

lemma functional_strict (𝕜 : Type u) [RCLike 𝕜] (x : SequenceC0 𝕜) (hx : ‖x‖ ≤ 1) :
    ‖functional 𝕜 x‖ < 1 := by
  have hcoord (n : ℕ) : ‖x.val n‖ ≤ 1 :=
    (lp.norm_apply_le_norm (by simp) x.val n).trans hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp x.property (1 / 2) (by norm_num)
  have hsmall : ‖x.val N‖ < 1 := by
    have h := hN N le_rfl
    rw [dist_zero_right] at h
    linarith
  have hs := (c0_pairing_holder (coefficients 𝕜) x).1
  have hle (n : ℕ) : ‖(weight n : 𝕜) * x.val n‖ ≤ weight n := by
    rw [norm_mul, RCLike.norm_ofReal, abs_of_pos (weight_pos n)]
    exact mul_le_of_le_one_right (weight_pos n).le (hcoord n)
  have hlt : ‖(weight N : 𝕜) * x.val N‖ < weight N := by
    rw [norm_mul, RCLike.norm_ofReal, abs_of_pos (weight_pos N)]
    exact mul_lt_of_lt_one_right (weight_pos N) hsmall
  have hsum : (∑' n, ‖(weight n : 𝕜) * x.val n‖) < ∑' n, weight n := by
    exact Summable.tsum_lt_tsum_of_nonneg (fun n => norm_nonneg _) hle hlt
      weight_hasSum.summable
  exact (norm_tsum_le_tsum_norm hs).trans_lt (hsum.trans_eq weight_hasSum.tsum_eq)

theorem nonattainment : Spec.Nonattainment.{u} := by
  intro 𝕜 _
  refine ⟨functional 𝕜, ?_, functional_norm 𝕜, ?_,
    functional_initialOnes_tendsto 𝕜, functional_strict 𝕜⟩
  · intro x
    exact ⟨(c0_pairing_holder (coefficients 𝕜) x).1, rfl⟩
  · intro N
    exact ⟨initialOnes_apply 𝕜 N, initialOnes_norm_le 𝕜 N, functional_initialOnes 𝕜 N⟩

end ExpandedFA.Supplements.CzeroNonattainment
