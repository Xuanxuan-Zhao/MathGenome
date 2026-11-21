import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.GateauxNormDerivative
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import Mathlib.Analysis.Convex.StrictConvexSpace

/-! Theorem `fa2:p1:gateaux-smoothness`, paper.tex 4771–4778.
Real strict convexity uses the native strictly convex normed-space predicate.
Smoothness uses exactly the scalar-linear norming sets of the manuscript.
No completeness or nontriviality hypothesis is imposed. -/
namespace ExpandedFA.P1.GateauxSmoothness.Spec

universe u v

/-- Smoothness of the norm at every unit vector; vacuous in the zero space. -/
def Smooth (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∀ x : E, ‖x‖ = 1 → SmoothnessDefinitions.Spec.SmoothAtValue 𝕜 x

/-- Strict convexity is real convexity, including over the complex field. -/
def StrictlyConvex (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  StrictConvexSpace ℝ E

/-- Nonzero points are normalized, without a unit-vector assumption. -/
def Characterization : Prop := GateauxNormDerivative.Spec.Characterization.{u,v}

def UnitDerivativeFormula : Prop := GateauxNormDerivative.Spec.UnitDerivativeFormula.{u,v}

def StrictDualImpliesSmooth : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    StrictlyConvex 𝕜 (E →L[𝕜] 𝕜) → Smooth 𝕜 E

def SmoothDualImpliesStrict : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Smooth 𝕜 (E →L[𝕜] 𝕜) → StrictlyConvex 𝕜 E

def ReflexiveSmoothImpliesStrictDual : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
      Smooth 𝕜 E → StrictlyConvex 𝕜 (E →L[𝕜] 𝕜)

def ReflexiveStrictImpliesSmoothDual : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
      StrictlyConvex 𝕜 E → Smooth 𝕜 (E →L[𝕜] 𝕜)

end ExpandedFA.P1.GateauxSmoothness.Spec
