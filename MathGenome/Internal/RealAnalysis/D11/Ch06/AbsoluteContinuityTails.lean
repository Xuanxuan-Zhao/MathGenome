import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.AbsoluteContinuityTails
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-! Small sets and finite-measure spatial tails of one absolute integral,
paper.tex:1878–1909. We apply the nonnegative lower-integral estimates to
`ofReal ‖f‖`, transporting through the proved canonical integral bridge.
Both library estimates use finite simple minorants; neither requires a
sigma-finite space or a convergence theorem for signed functions.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch06.AbsoluteContinuityTails

open D11.Ch05.NonnegativeIntegral
open D11.Ch06.ScalarIntegral

/-- Uniform absolute-integral control over all measurable sets of small mass. -/
theorem small_sets : Specs.D11.Ch06.AbsoluteContinuityTails.small_sets.{u} := by
  intro X 𝕜 _ _ _ _ μ f hf ε hε
  change scalarIntegrable μ f at hf
  have hfin : (∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ) ≠ ∞ := by
    exact (integral_eq_lintegral μ _ ▸ hf.2).ne
  obtain ⟨η, hη, hsmall⟩ :=
    exists_pos_setLIntegral_lt_of_measure_lt hfin (ENNReal.ofReal_pos.mpr hε).ne'
  obtain ⟨δ, _, hδ, hδη⟩ := ENNReal.lt_iff_exists_real_btwn.mp hη
  refine ⟨δ, ENNReal.ofReal_pos.mp hδ, ?_⟩
  intro E hE hmass
  change nonnegativeIntegral μ (E.indicator (fun x => ENNReal.ofReal ‖f x‖)) < _
  rw [integral_eq_lintegral, lintegral_indicator hE]
  exact hsmall E (hmass.trans hδη)

/-- The absolute integral is small outside some measurable set of finite mass. -/
theorem finite_measure_tail :
    Specs.D11.Ch06.AbsoluteContinuityTails.finite_measure_tail.{u} := by
  intro X 𝕜 _ _ _ _ μ f hf ε hε
  change scalarIntegrable μ f at hf
  have hfin : (∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ) ≠ ∞ := by
    exact (integral_eq_lintegral μ _ ▸ hf.2).ne
  obtain ⟨A, hA, hmass, htail⟩ :=
    exists_setLIntegral_compl_lt hfin (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨A, hA, hmass, ?_⟩
  change nonnegativeIntegral μ (Aᶜ.indicator (fun x => ENNReal.ofReal ‖f x‖)) < _
  rw [integral_eq_lintegral, lintegral_indicator hA.compl]
  exact htail

end D11.Ch06.AbsoluteContinuityTails
