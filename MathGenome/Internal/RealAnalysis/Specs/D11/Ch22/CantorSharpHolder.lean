import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.CantorDigitSurjection

/-! Independent sharp Hölder statements for paper.tex:6129–6144.
The set, map, and exponent are the canonical upstream objects. -/
noncomputable section

namespace Specs.D11.Ch22.CantorSharpHolder
open Specs.D11.Ch22.CantorDigitSurjection

/-- The bound at the left endpoint, including zero. -/
def endpoint_upper : Prop := ∀ x : ↥Specs.D11.Ch03.CantorSet.C_value,
  F_value x ≤ (x : ℝ) ^ alpha_value

/-- The reflected bound at the right endpoint, including one. -/
def endpoint_lower : Prop := ∀ x : ↥Specs.D11.Ch03.CantorSet.C_value,
  1 - F_value x ≤ (1 - (x : ℝ)) ^ alpha_value

/-- The exact constant-one bound, for every ordered or unordered pair. -/
def sharp_holder : Prop := ∀ x y : ↥Specs.D11.Ch03.CantorSet.C_value,
  |F_value y - F_value x| ≤ |(y : ℝ) - (x : ℝ)| ^ alpha_value

end Specs.D11.Ch22.CantorSharpHolder
