import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.RadixModel

/-! Independent statement of the normal safe-domain proposition following W01. -/
namespace NumAnalysis206.Rounding.Specs

def normalAbsoluteError : Prop :=
  ∀ (P : RadixFormat) (x : ℝ), x ∈ safeDomainValue P →
    |flValue P x - x| ≤ uValue P * |x|

def normalRelativeError : Prop :=
  ∀ (P : RadixFormat) (x : ℝ), x ∈ safeDomainValue P →
    ∃ δ : ℝ, |δ| ≤ uValue P ∧ flValue P x = x * (1 + δ)

end NumAnalysis206.Rounding.Specs
