import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.RadixModel

namespace NumAnalysis206.Rounding.Specs

/-- Sterbenz's lemma in the finite format, including subnormal results. -/
def sterbenzPositive : Prop := ∀ (P : RadixFormat), P.gradual = true →
  ∀ a b : ℝ, a ∈ FValue P → b ∈ FValue P → 0 < a → 0 < b →
    a / 2 ≤ b → b ≤ 2 * a → a - b ∈ FValue P ∧ flValue P (a - b) = a - b

/-- Reflection gives the corresponding statement for two negative inputs. -/
def sterbenzNegative : Prop := ∀ (P : RadixFormat), P.gradual = true →
  ∀ a b : ℝ, a ∈ FValue P → b ∈ FValue P → a < 0 → b < 0 →
    (-a) / 2 ≤ -b → -b ≤ 2 * (-a) →
    a - b ∈ FValue P ∧ flValue P (a - b) = a - b

/-- Equal inputs give an exact zero, even without gradual underflow. -/
def subtractionEqual : Prop := ∀ (P : RadixFormat) (a : ℝ),
  a - a ∈ FValue P ∧ flValue P (a - a) = 0

def subtractionSensitivity : Prop := ∀ a b ε da db : ℝ,
  0 ≤ ε → |da| ≤ ε * |a| → |db| ≤ ε * |b| →
  |((a + da) - (b + db)) - (a - b)| ≤ ε * (|a| + |b|)

/-- Oppositely directed perturbations attain the absolute bound. -/
def subtractionSensitivitySharp : Prop := ∀ a b ε : ℝ, 0 ≤ ε →
  ∃ da db : ℝ, |da| ≤ ε * |a| ∧ |db| ≤ ε * |b| ∧
    |((a + da) - (b + db)) - (a - b)| = ε * (|a| + |b|)

/-- The exact relative amplification, with the nonzero-output hypothesis. -/
def subtractionRelativeSensitivity : Prop := ∀ a b ε : ℝ, 0 ≤ ε → a - b ≠ 0 →
  (∀ da db : ℝ, |da| ≤ ε * |a| → |db| ≤ ε * |b| →
    |((a + da) - (b + db)) - (a - b)| / |a - b| ≤
      ε * ((|a| + |b|) / |a - b|)) ∧
  (∃ da db : ℝ, |da| ≤ ε * |a| ∧ |db| ≤ ε * |b| ∧
    |((a + da) - (b + db)) - (a - b)| / |a - b| =
      ε * ((|a| + |b|) / |a - b|))

/-- Exact subtraction alone gives no uniform conditioning bound over formats. -/
def exactSubtractionUnboundedCondition : Prop := ∀ C : ℝ,
  ∃ (P : RadixFormat) (a b : ℝ), P.gradual = true ∧
    a ∈ FValue P ∧ b ∈ FValue P ∧ 0 < a ∧ 0 < b ∧
    a / 2 ≤ b ∧ b ≤ 2 * a ∧ a - b ≠ 0 ∧
    flValue P (a - b) = a - b ∧ C < (|a| + |b|) / |a - b|

end NumAnalysis206.Rounding.Specs
