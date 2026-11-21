import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.PeriodicSetup
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Oriented
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.Euler
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.PiPeriod

/-! The Fourier normalization uses the upstream proper Darboux integral.
Canonical exp, sin, cos and π agree with the upstream series constructions
by expSeries_eq_complexExp, sinCosSeries_eq_real and analyticPi_eq_pi.
Integrability of the weights is established directly by uniform continuity
and the Darboux criterion, then combined with the upstream product theorem. -/
noncomputable section
namespace SingleVariableAnalysis
namespace Fourier
open Riemann
open scoped BigOperators

/-- Uniform continuity on a compact interval gives a small Darboux gap. -/
theorem realIntegrable_of_continuousOn {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Set.Icc a b)) : RealIntegrable g a b := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · have hb : BoundedOnInterval g a b :=
      ⟨(isCompact_Icc.image_of_continuousOn hg).bddBelow,
        (isCompact_Icc.image_of_continuousOn hg).bddAbove⟩
    apply (realIntegrable_iff_small_gap g hab.le hb).mpr
    intro ε hε
    let η := ε / (b - a + 1)
    have hlen : 0 < b - a := sub_pos.mpr hab
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hg) η hη
    obtain ⟨P, _, hP⟩ := arbitrarily_fine hab δ hδ
    have hcell (i : Fin P.n) :
        cellSupremum g P hb i - cellInfimum g P hb i ≤ η := by
      apply cell_oscillation_le_of_sub_le
      intro x hx y hy
      have hdist : dist x y < δ := by
        have hxy : |x-y| ≤ cellLength P i := by
          apply abs_le.mpr
          dsimp [cellLength, Riemann.S.lengthValue]
          constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
        exact (show dist x y ≤ mesh P by
          simpa only [Real.dist_eq] using hxy.trans (cellLength_le_mesh P i)).trans_lt hP
      have hd := huc x (cell_subset_interval P i hx) y (cell_subset_interval P i hy) hdist
      exact (le_abs_self _).trans (show |g x - g y| ≤ η by
        simpa only [Real.dist_eq] using hd.le)
    refine ⟨P, ?_⟩
    have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      mul_le_mul_of_nonneg_right (hcell i) (cell_positive P i).le
    rw [sum_cell_oscillation, ← Finset.mul_sum, sum_cellLength] at hs
    have heq : η * (b - a + 1) = ε := by
      dsimp [η]
      exact div_mul_cancel₀ _ (by positivity)
    exact hs.trans_lt (by nlinarith)
  · exact realIntegrable_degenerate g a

theorem complexIntegrable_of_continuousOn {g : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Set.Icc a b)) : ComplexIntegrable g a b :=
  ⟨realIntegrable_of_continuousOn hab (Complex.continuous_re.comp_continuousOn hg),
    realIntegrable_of_continuousOn hab (Complex.continuous_im.comp_continuousOn hg)⟩

end Fourier

abbrev fourierMode := Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue
abbrev PeriodicRiemannIntegrable := Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.periodicComplexValue
abbrev RealPeriodicRiemannIntegrable := Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.periodicRealValue
abbrev fourierCoeff := Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.coefficientValue
abbrev fourierPartialSum := Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.partialSumValue
abbrev fourierAZero := Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.aZeroValue
abbrev fourierCosCoeff := Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.cosineCoefficientValue
abbrev fourierSinCoeff := Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.sineCoefficientValue

theorem fourierCoeff_integrable :
    Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.coefficientIntegrability := by
  intro f hf n
  apply Riemann.complex_product hf
  apply Fourier.complexIntegrable_of_continuousOn (by linarith [Real.pi_pos])
  exact (Complex.continuous_exp.comp
    (continuous_const.mul (continuous_const.mul Complex.continuous_ofReal))).continuousOn

theorem fourierCosCoeff_integrable :
    Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.cosineIntegrability := by
  intro f hf n
  apply Riemann.real_product hf
  exact Fourier.realIntegrable_of_continuousOn (by linarith [Real.pi_pos])
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn)

theorem fourierSinCoeff_integrable :
    Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.sineIntegrability := by
  intro f hf n
  apply Riemann.real_product hf
  exact Fourier.realIntegrable_of_continuousOn (by linarith [Real.pi_pos])
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)

theorem fourierRealEmbedding_integrable :
    Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.realEmbeddingIntegrability := by
  intro f hf
  exact ⟨hf, Riemann.real_zero_value (by linarith [Real.pi_pos]) |>.choose⟩

end SingleVariableAnalysis
