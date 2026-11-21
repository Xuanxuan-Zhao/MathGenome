import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UniformFrechetNorm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap

/-!
Independent specification of the complete Uniform duality theorem,
`fa2:p1:uniform-smooth-duality`, paper.tex:4802–4810, with definitions
at 4755–4770 and the concluding proof at 4835–4861.

The field is real or complex; the dual is the continuous scalar-linear dual
with its operator norm. The smoothness modulus includes the zero-space case.
Only the reflexivity conclusion assumes completeness. Uniform real Fréchet
differentiability uses arbitrary increments, uniformly over the unit sphere.
-/
namespace ExpandedFA.P1.UniformSmoothDuality.Spec
universe u v

/-- Uniform convexity is equivalent to uniform smoothness of the dual. -/
def ConvexIffDualSmooth : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 E ↔
      SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 (E →L[𝕜] 𝕜)

/-- Uniform smoothness is equivalent to uniform convexity of the dual. -/
def SmoothIffDualConvex : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E ↔
      C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 (E →L[𝕜] 𝕜)

/-- Uniform differentiability is real even for a complex normed space. -/
def SmoothIffUniformFrechet : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E ↔
      UniformFrechetNorm.Spec.UniformlyFrechetDifferentiableNorm 𝕜 E

/-- A uniformly smooth Banach space is reflexive via its canonical evaluation. -/
def SmoothBanachReflexive : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E →
      C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E

/-- The unique norming functional varies uniformly continuously in operator
norm over the sphere with its inherited norm metric, including an empty sphere. -/
def UniformlyContinuousNormingMap : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E →
      ∃ f : UniformFrechetNorm.Spec.UnitSphere E → (E →L[𝕜] 𝕜),
        (∀ x, ‖f x‖ = 1 ∧ f x x = 1 ∧
          ∀ g : E →L[𝕜] 𝕜, ‖g‖ = 1 → g x = 1 → g = f x) ∧
        UniformContinuous f

end ExpandedFA.P1.UniformSmoothDuality.Spec
