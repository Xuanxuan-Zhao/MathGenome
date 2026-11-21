import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Filter Asymptotics Topology

namespace Specs.NumAnalysis206.Quadrature

/-- The exact linear combination of the fine and coarse approximations. -/
def richardsonType := ℝ → ℝ → ℝ → ℝ → ℝ

def richardsonValue (p lam fine coarse : ℝ) : ℝ :=
  (lam ^ p * fine - coarse) / (lam ^ p - 1)

/-- W61, with real powers and the right-hand neighborhood of zero. -/
def extrapolation : Prop :=
  ∀ (approx : ℝ → ℝ) (A c p q lam : ℝ),
    0 < p → 0 < q → 1 < lam →
    (fun h => approx h - (A + c * h ^ p)) =O[𝓝[Set.Ioi 0] 0]
      (fun h => h ^ (p + q)) →
    (fun h => richardsonValue p lam (approx (h / lam)) (approx h) - A)
      =O[𝓝[Set.Ioi 0] 0] (fun h => h ^ (p + q))

/-- W61's data-error estimate, for arbitrary fine and coarse input values.
It applies at every positive step, independently of asymptotic hypotheses. -/
def inputError : Prop :=
  ∀ (p lam fine coarse fineHat coarseHat δfine δcoarse : ℝ),
    0 < p → 1 < lam → 0 ≤ δfine → 0 ≤ δcoarse →
    |fineHat - fine| ≤ δfine → |coarseHat - coarse| ≤ δcoarse →
    |richardsonValue p lam fineHat coarseHat - richardsonValue p lam fine coarse| ≤
      (lam ^ p * δfine + δcoarse) / (lam ^ p - 1)

end Specs.NumAnalysis206.Quadrature
