import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers

/-!
Young's pointwise inequality in the proof of K03.09.holder,
paper.tex:2626–2632. Exponents are real and strictly greater than one;
the inputs may be zero. The first statement uses canonical real powers.
The remaining statements identify these powers with the upstream exp/log
construction, extended to zero for positive exponents, and express the
inequality through that same partial power interface.

In `youngInequalityPartial`, the hypotheses ensure that both options are
`some`, so the default in `getD` is never used for an undefined power.
-/
namespace Specs.SingleVariableAnalysis.Ch09.Young

def youngInequality : Prop :=
  ∀ p q : ℝ, 1 < p → 1 < q → 1 / p + 1 / q = 1 →
    ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
      u * v ≤ u ^ p / p + v ^ q / q

def partialRealPowerRpow : Prop :=
  ∀ x α : ℝ, 0 ≤ x → 0 < α →
    Ch07.RealPowers.partialRealPowerValue x α = some (x ^ α)

def youngInequalityPartial : Prop :=
  ∀ p q : ℝ, 1 < p → 1 < q → 1 / p + 1 / q = 1 →
    ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
      u * v ≤ (Ch07.RealPowers.partialRealPowerValue u p).getD 0 / p +
        (Ch07.RealPowers.partialRealPowerValue v q).getD 0 / q

end Specs.SingleVariableAnalysis.Ch09.Young
