import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.IntegrableDiscontinuities

/-!
The Lebesgue criterion of K03.08.oscillation_criterion (paper.tex:2204–2250).
Integrability means equality of the real upper and lower Darboux integrals.
Discontinuities are relative to the closed interval, including its endpoints.
Length zero means countable open bounded interval covers of arbitrarily small
extended total length; neither predicate uses a Lebesgue integral.
The interval is ordered, and singleton intervals are included.
-/
namespace Specs.SingleVariableAnalysis.Ch08.OscillationCriterion

def lengthZeroDiscontinuitiesIntegrable : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    DarbouxSums.boundedOnIntervalValue f a b →
    ZeroCovers.lengthZeroValue (OscillationSets.intervalDiscontinuitiesValue f a b) →
    Integral.realIntegrableValue f a b

def discontinuityCriterion : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    DarbouxSums.boundedOnIntervalValue f a b →
    (Integral.realIntegrableValue f a b ↔
      ZeroCovers.lengthZeroValue (OscillationSets.intervalDiscontinuitiesValue f a b))

end Specs.SingleVariableAnalysis.Ch08.OscillationCriterion
