import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SmoothnessDefinitions
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Uniform real Fréchet differentiability and the norming map, from
`fa2:p1:uniform-smooth-duality`, paper.tex 4841–4861. No completeness or
nontriviality is required. The dual is scalar-linear even over the complex field. -/
namespace ExpandedFA.P1.UniformFrechetNorm.Spec

universe u v

/-- The unit sphere, with the induced norm metric. It is empty in the zero space. -/
abbrev UnitSphere (E : Type v) [NormedAddCommGroup E] := {x : E // ‖x‖ = 1}

/-- The usual uniform real Fréchet remainder estimate. The derivative is a
continuous REAL-linear functional, and the increment ranges over all of E.
The radius is independent of the point on the sphere and the direction. -/
def UniformlyFrechetDifferentiableNorm (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  ∃ D : UnitSphere E → (E →L[ℝ] ℝ),
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (x : UnitSphere E) (h : E), ‖h‖ < δ →
        |‖(x : E) + h‖ - 1 - D x h| ≤ ε * ‖h‖

def Characterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E ↔
      UniformlyFrechetDifferentiableNorm 𝕜 E

def UniqueNormingFunctional : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E →
      ∀ x : E, ‖x‖ = 1 → ∃! f : E →L[𝕜] 𝕜, ‖f‖ = 1 ∧ f x = 1

/-- The map has the unique scalar-linear norming value, and is uniformly
continuous for the sphere's norm metric and the dual's operator norm metric. -/
def UniformlyContinuousNormingMap : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E →
      ∃ f : UnitSphere E → (E →L[𝕜] 𝕜),
        (∀ x, ‖f x‖ = 1 ∧ f x x = 1 ∧
          ∀ g : E →L[𝕜] 𝕜, ‖g‖ = 1 → g x = 1 → g = f x) ∧
        UniformContinuous f

/-- Identification with the native real Fréchet derivative, for every member
of the source's norming set. -/
def NormDerivativeFormula : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E →
      ∀ (x : E) (f : E →L[𝕜] 𝕜), ‖x‖ = 1 → ‖f‖ = 1 → f x = 1 →
        letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
        HasFDerivAt (fun y : E => ‖y‖)
          (RCLike.reCLM.comp (f.restrictScalars ℝ)) x

end ExpandedFA.P1.UniformFrechetNorm.Spec
