import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.OneEndpoint

/-! Independent statements of K03.10.cauchy, paper.tex:2939–2959.
The regularity hypothesis is precisely proper Darboux integrability of every
compact truncation. RightIndex includes a < r,u,v < b, with b possibly +∞;
LeftIndex includes a < u,v,r < b, with a possibly -∞. The tested tail
integrals carry their own integrability proofs. Values are finite real or
complex scalars; no absolute integrability or linked truncations are assumed.
-/
namespace Specs.SingleVariableAnalysis.Ch10.Cauchy
open _root_.SingleVariableAnalysis
open OneEndpoint

/-- At a right endpoint, including +∞, convergence is equivalent to uniformly
small proper integrals over all ordered intervals beyond one regular point. -/
def rightCauchyCriterion : Prop :=
  ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k) (a : ℝ) (b : WithTop ℝ),
    rightRegularValue k f a b →
      (rightConvergesValue k f a b ↔
        ∀ ε : ℝ, 0 < ε → ∃ r : rightIndexValue a b,
          ∀ u v : rightIndexValue a b, r.val < u.val → u.val < v.val →
            ∃ huv : I.scalarIntegrableValue k f u.val v.val,
              ‖I.scalarIntegralValue k f huv‖ < ε)

/-- The left-endpoint version reverses the approach: a < u < v < r.
It covers finite singular left endpoints and -∞. -/
def leftCauchyCriterion : Prop :=
  ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k) (a : WithBot ℝ) (b : ℝ),
    leftRegularValue k f a b →
      (leftConvergesValue k f a b ↔
        ∀ ε : ℝ, 0 < ε → ∃ r : leftIndexValue a b,
          ∀ u v : leftIndexValue a b, u.val < v.val → v.val < r.val →
            ∃ huv : I.scalarIntegrableValue k f u.val v.val,
              ‖I.scalarIntegralValue k f huv‖ < ε)

end Specs.SingleVariableAnalysis.Ch10.Cauchy
