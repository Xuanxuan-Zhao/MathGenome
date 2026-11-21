import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaDefinition
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers
import Mathlib.Analysis.Convex.Function

/-! K03.18.gamma_logconvex, paper.tex:4120–4141.
The Gamma values are the shared independently convergent improper Riemann
integral values. Logarithm and powers use the shared series constructions.
The conditional extension in `logConvex` only supplies a total real function
for `ConvexOn`; the asserted domain is exactly the positive half-line.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.GammaLogconvex
open Set
namespace G
export GammaDefinition (gammaIntegralValue)
end G
namespace L
export Ch07.LogConstruction (seriesLogValue)
end L
namespace P
export Ch07.RealPowers (realPowerValue)
end P

/-- Convexity of log Gamma on the entire positive half-line. -/
def logConvex : Prop :=
  ConvexOn ℝ (Ioi 0) (fun s =>
    if hs : 0 < s then L.seriesLogValue (G.gammaIntegralValue s hs) else 0)

/-- The equivalent power inequality includes both endpoint weights. -/
def powerInequality : Prop :=
  ∀ (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1),
  let hs : 0 < (1 - θ) * p + θ * q := by
    simpa only [smul_eq_mul, mem_Ioi] using
      (convex_Ioi (0 : ℝ)) hp hq (sub_nonneg.mpr hθ1) hθ0 (sub_add_cancel 1 θ)
  G.gammaIntegralValue ((1 - θ) * p + θ * q) hs ≤
    P.realPowerValue (G.gammaIntegralValue p hp) (1 - θ) *
      P.realPowerValue (G.gammaIntegralValue q hq) θ

end Specs.SingleVariableAnalysis.Ch18.GammaLogconvex
