import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaEulerLimit
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.EulerBetaApproximation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.BetaRecurrence

/-! Euler's two limits, with the original improper Beta and Gamma values.
The analytic limit is the upstream scaled-integrand approximation. Finite
Beta recurrence identifies its terms with the factorial/product expression.
-/
namespace SingleVariableAnalysis.SpecialIntegrals
open Filter
open scoped Topology BigOperators

/-- For each positive real parameter, both Euler sequences converge to the
same independently convergent improper Gamma integral. -/
theorem gamma_euler_limit :
    Specs.SingleVariableAnalysis.Ch18.GammaEulerLimit.gammaEulerLimit := by
  intro s hs
  have h := EulerBetaApproximation.euler_beta_approximation s hs
  refine ⟨h, h.congr (fun n => ?_)⟩
  rw [beta_nat_add_one_right s hs n, ← mul_div_assoc, mul_comm ((n : ℝ) ^ s)]

end SingleVariableAnalysis.SpecialIntegrals
