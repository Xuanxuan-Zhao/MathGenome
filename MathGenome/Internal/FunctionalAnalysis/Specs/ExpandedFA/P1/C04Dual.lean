import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm

/-!
Independent specification for Definition `fa2:p1:c04:dual` (paper.tex, lines 751–758).
Scalar absolute value is the native norm: absolute value on ℝ and modulus on ℂ.
The spaces carry their native algebraic operations and operator norm topology.
There is no completeness or nonzero-domain hypothesis.
-/

namespace ExpandedFA.P1.C04Dual.Spec

universe u v

/-- The continuous dual consists of scalar-linear continuous maps. In particular,
over ℂ these are complex-linear, rather than conjugate-linear, functionals. -/
def ContinuousDualType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], Type (max u v)

def ContinuousDualValue : ContinuousDualType :=
  fun 𝕜 E _ _ _ => E →L[𝕜] 𝕜

/-- No topology or continuity condition is imposed on the algebraic dual. -/
def AlgebraicDualType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E], Type (max u v)

def AlgebraicDualValue : AlgebraicDualType :=
  fun 𝕜 E _ _ _ => E →ₗ[𝕜] 𝕜

/-- The bidual is the continuous linear dual of the continuous linear dual,
with the first dual's actual operator norm and topology. -/
def BidualType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], Type (max u v)

def BidualValue : BidualType :=
  fun 𝕜 E _ _ _ => (E →L[𝕜] 𝕜) →L[𝕜] 𝕜

/-- The dual norm is the supremum of absolute scalar values on the closed
unit ball, including when the domain is the zero space. -/
def DualNormSupremum : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : E →L[𝕜] 𝕜),
    ‖f‖ = sSup ((fun x => ‖f x‖) '' {x : E | ‖x‖ ≤ 1})

end ExpandedFA.P1.C04Dual.Spec
