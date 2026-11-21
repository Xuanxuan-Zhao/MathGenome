import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent specification of paper.tex, Definition W09.

A map on an open domain is represented by a total extension `f : X → Y`;
only its differentiability at the specified interior point is required.
The input and output carry their own normed-space structures. No completeness,
nontriviality, or finite-dimensionality is required of the output space.

The proof arguments restrict the applicability of the derivative formula:
Mathlib's default zero derivative at a nondifferentiable point is never used
as a condition number. The relative definition additionally requires both
scales to be nonzero. The absolute definition has no such restriction.
-/

universe u v w

namespace Specs.NumAnalysis206.Conditioning

/-- Domain and codomain of the absolute condition-number definition. -/
def AbsoluteConditionNumberType : Type _ :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (U : Set X), IsOpen U →
    (f : X → Y) → (x : X) → x ∈ U → DifferentiableAt 𝕜 f x → ℝ

/-- The absolute condition number is the subordinate operator norm of `Df(x)`. -/
noncomputable def absoluteConditionNumberValue : AbsoluteConditionNumberType.{u, v, w} :=
  fun 𝕜 _ _ _ _ _ _ _ _ _ _ f x _ _ => ‖fderiv 𝕜 f x‖

/-- Relative scales are used only when both the input and output are nonzero. -/
def RelativeConditionNumberType : Type _ :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (U : Set X), IsOpen U →
    (f : X → Y) → (x : X) → x ∈ U → DifferentiableAt 𝕜 f x →
    x ≠ 0 → f x ≠ 0 → ℝ

/-- The derivative norm multiplied by the input scale and divided by the output scale. -/
noncomputable def relativeConditionNumberValue : RelativeConditionNumberType.{u, v, w} :=
  fun 𝕜 _ _ _ _ _ _ _ _ _ _ f x _ _ _ _ => ‖fderiv 𝕜 f x‖ * ‖x‖ / ‖f x‖

end Specs.NumAnalysis206.Conditioning
