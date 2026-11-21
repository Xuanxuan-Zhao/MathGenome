import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.Hoeffding
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace P205.Probability

/-- Hoeffding's inequality with both tails and the zero-range case. -/
theorem hoeffding : Specs.P205.Probability.HoeffdingStatement := by
  intro Ω mΩ μ hμ ι hι X a b hmeas hind _hab hbound
  classical
  let Y : ι → Ω → ℝ := fun i ω ↦ X i ω - ∫ ω, X i ω ∂μ
  let c : ι → ℝ≥0 := fun i ↦ (‖b i - a i‖₊ / 2) ^ 2
  let S : Ω → ℝ := fun ω ↦ ∑ i, Y i ω
  let V : ℝ := ∑ i, (b i - a i) ^ 2
  have hY : ∀ i, HasSubgaussianMGF (Y i) (c i) μ := fun i ↦
    hasSubgaussianMGF_of_mem_Icc (hmeas i).aemeasurable (hbound i)
  have hindY : iIndepFun Y μ :=
    hind.comp (fun i x ↦ x - ∫ ω, X i ω ∂μ) (fun i ↦ by fun_prop)
  have hS : HasSubgaussianMGF S (∑ i, c i) μ := by
    simpa [S] using HasSubgaussianMGF.sum_of_iIndepFun hindY
      (s := Finset.univ) (fun i _ ↦ hY i)
  have hc : ((∑ i, c i : ℝ≥0) : ℝ) = V / 4 := by
    norm_num [c, V, NNReal.coe_sum, div_pow, Finset.sum_div]
  have hexp (t : ℝ) : -t ^ 2 / (2 * ((∑ i, c i : ℝ≥0) : ℝ)) =
      -2 * t ^ 2 / V := by
    rw [hc]
    ring
  change (∀ t : ℝ, 0 < t → 0 < V →
      μ.real {ω | t ≤ S ω} ≤ Real.exp (-2 * t ^ 2 / V) ∧
      μ.real {ω | S ω ≤ -t} ≤ Real.exp (-2 * t ^ 2 / V)) ∧
    (V = 0 → (∀ᵐ ω ∂μ, S ω = 0) ∧
      ∀ t : ℝ, 0 < t →
        μ.real {ω | t ≤ S ω} = 0 ∧ μ.real {ω | S ω ≤ -t} = 0)
  constructor
  · intro t ht _hV
    constructor
    · simpa only [hexp] using hS.measure_ge_le ht.le
    · have hevent : {ω | t ≤ (-S) ω} = {ω | S ω ≤ -t} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Pi.neg_apply, le_neg]
      simpa only [hevent, hexp] using hS.neg.measure_ge_le ht.le
  · intro hV
    have hc0 : (∑ i, c i) = 0 := by
      apply NNReal.coe_injective
      simpa [hV] using hc
    rw [hc0] at hS
    have hzero : ∀ᵐ ω ∂μ, S ω = 0 := hS.ae_eq_zero_of_hasSubgaussianMGF_zero
    refine ⟨hzero, ?_⟩
    intro t ht
    constructor
    · have hevent : {ω | t ≤ S ω} =ᵐ[μ] (∅ : Set Ω) := by
        filter_upwards [hzero] with ω hω
        simp [hω, not_le.mpr ht]
      simpa using measureReal_congr hevent
    · have hevent : {ω | S ω ≤ -t} =ᵐ[μ] (∅ : Set Ω) := by
        filter_upwards [hzero] with ω hω
        simp [hω, not_le.mpr (neg_neg_of_pos ht)]
      simpa using measureReal_congr hevent

end P205.Probability
