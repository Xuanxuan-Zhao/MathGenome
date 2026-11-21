import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Bessel
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.FiniteProjection
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Nonnegative

/-! Bessel's inequality is derived from the finite projection identity with
zero polynomial. Positivity concerns the actual proper Riemann residual
integral. Completeness of ℝ then gives the nonnegative sum over all integers;
no completed function space, Parseval theorem or measure integral is used. -/
noncomputable section
namespace SingleVariableAnalysis
open Riemann
open scoped BigOperators

namespace FourierProjection

theorem normSquared_nonneg (f : ℝ → ℂ)
    (hs : RealIntegrable (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi) :
    0 ≤ fourierNormSquared f hs := by
  obtain ⟨hz, he⟩ := real_zero_value (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])
  have hi := realIntegral_mono (fun _ => 0) (fun x => ‖f x‖ ^ 2)
    hz hs (fun x _ => sq_nonneg ‖f x‖)
  change realIntegral (fun _ => 0) hz ≤ realIntegral (fun x => ‖f x‖ ^ 2) hs at hi
  rw [he] at hi
  exact mul_nonneg (by positivity) hi

end FourierProjection

open Specs.SingleVariableAnalysis.Ch19.Bessel

theorem fourierBessel_squaredNorm_integrable : squaredNormIntegrability :=
  fourierNormSquared_integrable

theorem fourierBessel_finite : finiteBessel := by
  intro f hf h hs E
  let hP := fourierResidual_integrable f hf E (fun n => fourierCoeff f n (h n))
  have hd : RealIntegrable (fun x => ‖f x - fourierPolynomial E (fun _ => 0) x‖ ^ 2)
      (-Real.pi) Real.pi := by
    simpa [fourierPolynomial, Specs.SingleVariableAnalysis.Ch19.FiniteProjection.polynomialValue]
      using hs
  have he := fourierProjection_identity f hf h E (fun _ => 0) hd hP
  have hz : fourierPolynomial E (fun _ => 0) = (fun _ => 0) := by
    funext x
    simp [fourierPolynomial, Specs.SingleVariableAnalysis.Ch19.FiniteProjection.polynomialValue]
  simp only [hz, sub_zero] at he
  have hp := FourierProjection.normSquared_nonneg (fun x => f x - fourierProjection f h E x) hP
  linarith

theorem fourierBessel_summable : coefficientsSummable := by
  intro f hf h
  exact summable_of_sum_le (fun n => sq_nonneg _) (fourierBessel_finite f hf h
    (fourierBessel_squaredNorm_integrable f hf))

theorem fourierBessel_tsum_le : totalBessel := by
  intro f hf h hs
  exact Real.tsum_le_of_sum_le (fun n => sq_nonneg _) (fourierBessel_finite f hf h hs)

theorem fourierBessel_nonnegativeSum : nonnegativeSum := by
  intro f hf h hs
  have hsum := fourierBessel_summable f hf h
  have he := ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg ‖fourierCoeff f n (h n)‖) hsum
  change IsLUB _ _ ∧ nonnegativeExtendedSum _ = _ ∧ nonnegativeExtendedSum _ ≤ _ ∧
    nonnegativeExtendedSum _ ≠ ⊤
  refine ⟨?_, he.symm, ?_, ?_⟩
  · constructor
    · rintro _ ⟨E, rfl⟩
      exact hsum.sum_le_tsum E (fun n _ => sq_nonneg _)
    · intro b hb
      exact hsum.tsum_le_of_sum_le (fun E => hb ⟨E, rfl⟩)
  · rw [show nonnegativeExtendedSum (fun n => ‖fourierCoeff f n (h n)‖ ^ 2) = _ from he.symm]
    exact ENNReal.ofReal_le_ofReal (fourierBessel_tsum_le f hf h hs)
  · exact hsum.tsum_ofReal_ne_top

theorem fourierBessel_real : realBessel := by
  intro f hf
  have hc := fourierRealEmbedding_integrable f hf
  have hn : RealIntegrable (fun x => |f x| ^ 2) (-Real.pi) Real.pi := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      fourierBessel_squaredNorm_integrable (fun x => (f x : ℂ)) hc
  refine ⟨hn, ?_⟩
  intro h hs
  have hs' : RealIntegrable (fun x => ‖(f x : ℂ)‖ ^ 2) (-Real.pi) Real.pi := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hs
  refine ⟨?_, fourierBessel_summable _ hc h, ?_⟩
  · intro E
    simpa only [fourierNormSquared,
      Specs.SingleVariableAnalysis.Ch19.FiniteProjection.normSquaredValue,
      Complex.norm_real, Real.norm_eq_abs] using fourierBessel_finite _ hc h hs' E
  · simpa only [fourierNormSquared,
      Specs.SingleVariableAnalysis.Ch19.FiniteProjection.normSquaredValue,
      Complex.norm_real, Real.norm_eq_abs] using fourierBessel_tsum_le _ hc h hs'

end SingleVariableAnalysis
