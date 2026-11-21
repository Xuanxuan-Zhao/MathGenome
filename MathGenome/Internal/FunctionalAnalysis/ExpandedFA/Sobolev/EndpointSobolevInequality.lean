import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.EndpointSobolevInequality
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace ExpandedFA.Sobolev
open ExpandedFA.Distributions

/-- In the accepted coordinate model, the operator norm is bounded by the sum
of the norms of the images of the coordinate vectors. -/
theorem norm_le_sum_coordinate_norm {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : Domain d →L[ℝ] F) :
    ‖A‖ ≤ ∑ j : Fin d, ‖A (coordinateVector j)‖ := by
  classical
  apply A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro x
  have hx : x = ∑ j : Fin d, x j • coordinateVector j := by
    ext i
    simp [coordinateVector, Pi.single_apply, Finset.sum_apply]
  calc
    ‖A x‖ = ‖∑ j : Fin d, x j • A (coordinateVector j)‖ := by
      conv_lhs => rw [hx]
      simp only [map_sum, map_smul]
    _ ≤ ∑ j : Fin d, ‖x j • A (coordinateVector j)‖ := norm_sum_le _ _
    _ = ∑ j : Fin d, ‖x j‖ * ‖A (coordinateVector j)‖ := by
      simp only [norm_smul]
    _ ≤ ∑ j : Fin d, ‖x‖ * ‖A (coordinateVector j)‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x j) (norm_nonneg _)
    _ = (∑ j : Fin d, ‖A (coordinateVector j)‖) * ‖x‖ := by
      rw [← Finset.mul_sum, mul_comm]

/-- The L¹ operator norm of the derivative is controlled by the sum of the
ordinary coordinate L¹ norms. This proves the bridge needed for the manuscript's
specific right-hand side of the endpoint inequality. -/
theorem eLpNorm_fderiv_one_le_sum {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u : Domain d → F}
    (hu : ContDiff ℝ 1 u) :
    eLpNorm (fderiv ℝ u) 1 volume ≤
      ∑ j : Fin d, eLpNorm (fun x => fderiv ℝ u x (coordinateVector j)) 1 volume := by
  classical
  have hc := hu.continuous_fderiv one_ne_zero
  simp_rw [eLpNorm_one_eq_lintegral_enorm hc.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm (hc.clm_apply continuous_const).aestronglyMeasurable]
  calc
    (∫⁻ x, ‖fderiv ℝ u x‖ₑ) ≤
        ∫⁻ x, ∑ j : Fin d, ‖fderiv ℝ u x (coordinateVector j)‖ₑ := by
      apply lintegral_mono
      intro x
      have hn : ‖fderiv ℝ u x‖₊ ≤
          ∑ j : Fin d, ‖fderiv ℝ u x (coordinateVector j)‖₊ := by
        apply NNReal.coe_le_coe.mp
        simpa only [NNReal.coe_sum, coe_nnnorm] using
          norm_le_sum_coordinate_norm (fderiv ℝ u x)
      simpa only [enorm_eq_nnnorm, ENNReal.ofNNReal_finsetSum] using ENNReal.coe_le_coe.mpr hn
    _ = ∑ j : Fin d, ∫⁻ x, ‖fderiv ℝ u x (coordinateVector j)‖ₑ := by
      apply lintegral_finsetSum
      intro j _
      exact (hc.clm_apply continuous_const).enorm.measurable

/-- The p=1 Sobolev inequality with its full C¹ compact-support hypotheses,
the exponent d/(d-1), and a constant depending only on dimension. -/
theorem endpoint_sobolev_inequality :
    Specs.ExpandedFA.Sobolev.EndpointSobolevInequality.EndpointInequality := by
  intro d hd
  let q : ℝ≥0 := NNReal.conjExponent d
  refine ⟨eLpNormLESNormFDerivOneConst (volume : Measure (Domain d)) q, ?_⟩
  intro 𝕜 _ u hu hsupport
  have hd' : (1 : ℝ≥0) < d := by exact_mod_cast hd
  have hq : NNReal.HolderConjugate (Module.finrank ℝ (Domain d)) q := by
    simpa [Domain] using NNReal.HolderConjugate.conjExponent hd'
  have hqval : (q : ℝ≥0∞) = ENNReal.ofReal ((d : ℝ) / ((d : ℝ) - 1)) := by
    have hreal : (q : ℝ) = (d : ℝ) / ((d : ℝ) - 1) := by
      simp only [q, NNReal.conjExponent, NNReal.coe_div, NNReal.coe_sub hd'.le,
        NNReal.coe_natCast, NNReal.coe_one]
    rw [← hreal, ENNReal.ofReal_coe_nnreal]
  refine ⟨hu.continuous.memLp_of_hasCompactSupport hsupport, ?_, ?_⟩
  · intro j
    exact Continuous.integrable_of_hasCompactSupport
      ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (HasCompactSupport.fderiv_apply ℝ hsupport (coordinateVector j))
  · rw [← hqval]
    exact (eLpNorm_le_eLpNorm_fderiv_one volume hu hsupport hq).trans
      (mul_le_mul_right (eLpNorm_fderiv_one_le_sum hu) _)

end ExpandedFA.Sobolev
