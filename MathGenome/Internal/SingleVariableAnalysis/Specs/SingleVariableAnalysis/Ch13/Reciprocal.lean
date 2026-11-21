import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.PowerSeries

/-! K03.13.composition, paper.tex:1448: reciprocal construction and convergence.
The original root-limsup radius and ordinary inclusive partial sums are retained.
The sum F is produced at every nearby argument, so the assertion includes local
nonvanishing and applies to every function represented by the original series,
by uniqueness of its numerical sum. No inverse-series certificate is assumed. -/
namespace Specs.SingleVariableAnalysis.Ch13.Reciprocal
open PowerSeries
open scoped ENNReal BigOperators

def realReciprocal : Prop :=
  ∀ (a : ℕ → ℝ) (c : ℝ), 0 < realPowerSeriesRadiusValue a → a 0 ≠ 0 →
    ∃ (q : ℕ → ℝ) (r : ℝ), 0 < r ∧
      ENNReal.ofReal r < realPowerSeriesRadiusValue a ∧
      ENNReal.ofReal r ≤ realPowerSeriesRadiusValue q ∧
      q 0 = 1 / a 0 ∧
      (∀ k : ℕ, 0 < k → q k = -(a 0)⁻¹ *
        ∑ j ∈ Finset.range k, a (j+1) * q (k-(j+1))) ∧
      ∀ x : ℝ, |x-c| ≤ r → ∃ F : ℝ, F ≠ 0 ∧
        RealPowerSeriesHasSumValue a c x F ∧
        RealPowerSeriesHasSumValue q c x (1/F) ∧
        RealPowerSeriesAbsolutelyConvergesValue q c x

def complexReciprocal : Prop :=
  ∀ (a : ℕ → ℂ) (c : ℝ), 0 < complexPowerSeriesRadiusValue a → a 0 ≠ 0 →
    ∃ (q : ℕ → ℂ) (r : ℝ), 0 < r ∧
      ENNReal.ofReal r < complexPowerSeriesRadiusValue a ∧
      ENNReal.ofReal r ≤ complexPowerSeriesRadiusValue q ∧
      q 0 = 1 / a 0 ∧
      (∀ k : ℕ, 0 < k → q k = -(a 0)⁻¹ *
        ∑ j ∈ Finset.range k, a (j+1) * q (k-(j+1))) ∧
      ∀ z : ℂ, ‖z-(c : ℂ)‖ ≤ r → ∃ F : ℂ, F ≠ 0 ∧
        ComplexPowerSeriesHasSumValue a c z F ∧
        ComplexPowerSeriesHasSumValue q c z (1/F) ∧
        ComplexPowerSeriesAbsolutelyConvergesValue q c z

end Specs.SingleVariableAnalysis.Ch13.Reciprocal
