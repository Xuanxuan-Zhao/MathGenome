import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaLogconvex
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.GammaDefinition
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.RealPowers
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-! Log-convexity of the source Gamma integral, K03.18.gamma_logconvex.

Proof provenance: Mathlib's `Real.convexOn_log_Gamma` applies measure-theoretic
Hölder to Euler's convergent integral. We transfer it through the upstream
`gamma_eq_realGamma`, which identifies the shared value with the sum of its
two independent proper Darboux limits. Thus no total measure integral is
being used as a substitute for improper Riemann convergence. This reuse
avoids a second passage from finite Hölder to endpoint limits.

The shared logarithm and powers agree with their canonical counterparts
at the strictly positive Gamma values. Convexity then gives the power bound
for all weights in [0,1], including the two equality cases.
-/
noncomputable section
namespace SingleVariableAnalysis
open Set
namespace GLS
export Specs.SingleVariableAnalysis.Ch18.GammaLogconvex (logConvex powerInequality)
end GLS

theorem gamma_log_convex : GLS.logConvex := by
  apply Real.convexOn_log_Gamma.congr
  intro s hs
  change 0 < s at hs
  have he : Specs.SingleVariableAnalysis.Ch07.LogConstruction.seriesLogValue
      (GSpec.gammaIntegralValue s hs) = Real.log (Real.Gamma s) := by
    exact (seriesLog_eq_realLog _ (gamma_positive s hs)).trans
      (congrArg Real.log (gamma_eq_realGamma s hs))
  simpa [hs] using he.symm

theorem gamma_log_convex_inequality : GLS.powerInequality := by
  intro p q hp hq θ hθ0 hθ1
  dsimp only
  change gammaIntegral ((1 - θ) * p + θ * q) _ ≤
    realPower (gammaIntegral p hp) (1 - θ) * realPower (gammaIntegral q hq) θ
  unfold gammaIntegral
  rw [realPower_eq_rpow _ (gamma_positive p hp),
    realPower_eq_rpow _ (gamma_positive q hq),
    gamma_eq_realGamma, gamma_eq_realGamma, gamma_eq_realGamma]
  have hs : 0 < (1 - θ) * p + θ * q :=
    (convex_Ioi (0 : ℝ)) hp hq (sub_nonneg.mpr hθ1) hθ0 (sub_add_cancel 1 θ)
  have h := Real.convexOn_log_Gamma.2 hp hq
    (sub_nonneg.mpr hθ1) hθ0 (sub_add_cancel 1 θ)
  simp only [Function.comp_apply, smul_eq_mul] at h
  apply (Real.log_le_log_iff (Real.Gamma_pos_of_pos hs)
    (mul_pos (Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos hp) _)
      (Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos hq) _))).mp
  rwa [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos hp) _))
    (ne_of_gt (Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos hq) _)),
    Real.log_rpow (Real.Gamma_pos_of_pos hp), Real.log_rpow (Real.Gamma_pos_of_pos hq)]

end SingleVariableAnalysis
