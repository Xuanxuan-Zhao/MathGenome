import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SmoothnessDefinitions
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Real Gâteaux differentiability of the norm, paper.tex 4771–4791.
No completeness or dimension restriction is imposed. Smoothness away from
zero means smoothness at the positively normalized vector. -/
namespace ExpandedFA.P1.GateauxNormDerivative.Spec

universe u v

/-- A continuous real-linear derivative whose value in each direction is
 the two-sided derivative along that real line. -/
def RealGateauxDifferentiable (𝕜 : Type u) {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) : Prop :=
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  ∃ L : E →L[ℝ] ℝ, ∀ h : E,
    HasDerivAt (fun t : ℝ => ‖x + (t : 𝕜) • h‖) (L h) 0

/-- The original unit-vector definition, extended by positive normalization. -/
def SmoothNonzero (𝕜 : Type u) {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) : Prop :=
  SmoothnessDefinitions.Spec.SmoothAtValue 𝕜 ((‖x‖⁻¹ : 𝕜) • x)

def Characterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E), x ≠ 0 →
      (SmoothNonzero 𝕜 x ↔ RealGateauxDifferentiable 𝕜 x)

/-- At a unit vector the real directional derivative is Re f(h), where f
 is the unique member of the original scalar-linear norming set D(x). -/
def UnitDerivativeFormula : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E), ‖x‖ = 1 →
    SmoothnessDefinitions.Spec.SmoothAtValue 𝕜 x →
    ∃ f : E →L[𝕜] 𝕜, ‖f‖ = 1 ∧ f x = 1 ∧
      (∀ g : E →L[𝕜] 𝕜, ‖g‖ = 1 → g x = 1 → g = f) ∧
      ∀ h : E, HasDerivAt (fun t : ℝ => ‖x + (t : 𝕜) • h‖) (RCLike.re (f h)) 0

end ExpandedFA.P1.GateauxNormDerivative.Spec
