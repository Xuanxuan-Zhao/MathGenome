import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.TwoTimeAndExamples
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.ConditionalHoeffding
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

universe u
namespace P207
variable {Ω : Type u} [m : MeasurableSpace Ω]

theorem increment_condExp_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ) (k : ℕ) :
    μ[(fun ω => M (k + 1) ω - M k ω) | ℱ k] =ᵐ[μ] (fun _ => 0) := by
  have hs := condExp_sub (hM.2.1 (k + 1)) (hM.2.1 k) (ℱ k)
  have hself := condExp_of_stronglyMeasurable (ℱ.le k)
    (hM.1.stronglyAdapted k) (hM.2.1 k)
  filter_upwards [hs, hM.2.2 k] with ω hω hnext
  change μ[M (k + 1) - M k | ℱ k] ω = 0
  rw [hω]
  change μ[M (k + 1) | ℱ k] ω - μ[M k | ℱ k] ω = 0
  rw [hself, hnext, sub_self]

/-- Eventwise proof: normalize the restriction to every event in the conditioning
sigma-algebra and apply the ordinary bounded-variable Hoeffding lemma there.
This argument needs no regular conditional distribution or independence. -/
theorem conditional_hoeffding_of_condExp_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ m) (X : Ω → ℝ)
    (hi : Integrable X μ) (hz : μ[X | 𝒢] =ᵐ[μ] (fun _ => 0))
    (a b : ℝ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (s : ℝ) :
    Integrable (fun ω => Real.exp (s * X ω)) μ ∧
    μ[(fun ω => Real.exp (s * X ω)) | 𝒢] ≤ᵐ[μ]
      (fun _ => Real.exp (s ^ 2 * (b - a) ^ 2 / 8)) := by
  let Y := fun ω => Real.exp (s * X ω)
  let C := Real.exp (s ^ 2 * (b - a) ^ 2 / 8)
  have hY : Integrable Y μ := integrable_exp_mul_of_mem_Icc hi.aemeasurable hb
  refine ⟨hY, ?_⟩
  apply ae_of_ae_trim h𝒢
  apply ae_le_of_forall_setIntegral_le
    (integrable_condExp.trim h𝒢 stronglyMeasurable_condExp) (integrable_const C)
  intro A hA _
  rw [← setIntegral_trim h𝒢 stronglyMeasurable_condExp hA,
    ← setIntegral_trim h𝒢 stronglyMeasurable_const hA,
    setIntegral_condExp h𝒢 hY hA]
  by_cases hnull : μ A = 0
  · simp [Measure.restrict_eq_zero.mpr hnull]
  have : IsProbabilityMeasure (cond μ A) := cond_isProbabilityMeasure hnull
  have hmean : (∫ ω, X ω ∂(cond μ A)) = 0 := by
    have hzero : (∫ ω in A, X ω ∂μ) = 0 := by
      rw [← setIntegral_condExp h𝒢 hi hA]
      exact (integral_congr_ae (ae_restrict_of_ae hz)).trans (integral_zero _ _)
    simp [ProbabilityTheory.cond, integral_smul_measure, hzero]
  have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (hi.aemeasurable.mono_ac cond_absolutelyContinuous)
    (cond_absolutelyContinuous hb) hmean
  have hbound := hsub.mgf_le s
  have hexp : (((‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) * s ^ 2 / 2 =
      s ^ 2 * (b - a) ^ 2 / 8 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm]
    rw [Real.norm_eq_abs, div_pow, sq_abs]
    ring
  rw [hexp] at hbound
  change (∫ ω, Y ω ∂(cond μ A)) ≤ C at hbound
  simp only [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul] at hbound
  rw [setIntegral_const, smul_eq_mul]
  exact (inv_mul_le_iff₀ (ENNReal.toReal_pos hnull (measure_ne_top μ A))).mp hbound

theorem conditional_hoeffding (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (k : ℕ) (a b : ℝ)
    (hb : ∀ᵐ ω ∂μ, a ≤ M (k + 1) ω - M k ω ∧ M (k + 1) ω - M k ω ≤ b)
    (s : ℝ) :
    Integrable (fun ω => Real.exp (s * (M (k + 1) ω - M k ω))) μ ∧
    μ[(fun ω => Real.exp (s * (M (k + 1) ω - M k ω))) | ℱ k] ≤ᵐ[μ]
      (fun _ => Real.exp (s ^ 2 * (b - a) ^ 2 / 8)) :=
  conditional_hoeffding_of_condExp_zero μ (ℱ.le k) _
    ((hM.2.1 (k + 1)).sub (hM.2.1 k)) (increment_condExp_zero μ ℱ M hM k) a b hb s

end P207
