import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.AlgebraNull
import MathGenome.Internal.RealAnalysis.D11.Ch05.NonnegativeIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch01.ExhaustionRestriction
import MathGenome.Internal.RealAnalysis.D11.Ch04.AeCommonException
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Nonnegative integral algebra, restriction to a measurable trace space,
and null invariance (paper.tex:1553–1596). We transport the shared integral
along its proved lower-integral bridge. Ordinary a.e. hypotheses are converted
using the upstream measurable-null-envelope equivalence, so this does not
assume completeness. The subtype measure is precisely the upstream comap.
-/
open Set MeasureTheory
open scoped ENNReal NNReal
universe u
noncomputable section
namespace D11.Ch05.AlgebraNull

open NonnegativeIntegral
open D11.Ch01.ExhaustionRestriction
open D11.Ch04.AeCommonException

theorem additivity : Specs.D11.Ch05.AlgebraNull.additivity := by
  intro X _ μ f g hf _hg
  change nonnegativeIntegral μ (fun x => f x + g x) =
    nonnegativeIntegral μ f + nonnegativeIntegral μ g
  simp only [integral_eq_lintegral]
  exact lintegral_add_left hf g

theorem homogeneity : Specs.D11.Ch05.AlgebraNull.homogeneity := by
  intro X _ μ f a hf
  change nonnegativeIntegral μ (fun x => (a : ℝ≥0∞) * f x) =
    (a : ℝ≥0∞) * nonnegativeIntegral μ f
  simp only [integral_eq_lintegral]
  exact lintegral_const_mul (a : ℝ≥0∞) hf

theorem monotonicity : Specs.D11.Ch05.AlgebraNull.monotonicity := by
  intro X _ μ f g _hf _hg hfg
  change nonnegativeIntegral μ f ≤ nonnegativeIntegral μ g
  simp only [integral_eq_lintegral]
  exact lintegral_mono hfg

theorem restriction_indicator : Specs.D11.Ch05.AlgebraNull.restriction_indicator := by
  intro X _ μ f E _hf hE
  change nonnegativeIntegral (restrictOnSpace μ E) f =
    nonnegativeIntegral μ (E.indicator f)
  simp only [integral_eq_lintegral, restrictOnSpace]
  exact (lintegral_indicator hE f).symm

theorem restriction_indicator_mul :
    Specs.D11.Ch05.AlgebraNull.restriction_indicator_mul := by
  intro X _ μ f E hf hE
  have h : (fun x => E.indicator (fun _ => (1 : ℝ≥0∞)) x * f x) =
      E.indicator f := by
    classical
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [h]
  exact restriction_indicator μ f E hf hE

theorem restriction_subtype : Specs.D11.Ch05.AlgebraNull.restriction_subtype := by
  intro X _ μ f E _hf hE
  change nonnegativeIntegral (restrictToSubtype μ E) (fun x : E => f x) =
    nonnegativeIntegral μ (E.indicator f)
  simp only [integral_eq_lintegral, restrictToSubtype]
  exact (lintegral_subtype_comap hE f).trans (lintegral_indicator hE f).symm

theorem ae_invariance : Specs.D11.Ch05.AlgebraNull.ae_invariance := by
  intro X _ μ f g _hf _hg hfg
  change nonnegativeIntegral μ f = nonnegativeIntegral μ g
  simp only [integral_eq_lintegral]
  exact lintegral_congr_ae ((aeEq_iff_native μ f g).mp hfg)

theorem null_integral : Specs.D11.Ch05.AlgebraNull.null_integral := by
  intro X _ μ f N _hf hN
  change nonnegativeIntegral μ (N.indicator f) = 0
  rw [integral_eq_lintegral, lintegral_indicator hN.1]
  exact setLIntegral_measure_zero N f hN.2

theorem ae_monotonicity : Specs.D11.Ch05.AlgebraNull.ae_monotonicity := by
  intro X _ μ f g _hf _hg hfg
  change nonnegativeIntegral μ f ≤ nonnegativeIntegral μ g
  simp only [integral_eq_lintegral]
  exact lintegral_mono_ae ((almostEverywhere_iff_native μ _).mp hfg)

end D11.Ch05.AlgebraNull
