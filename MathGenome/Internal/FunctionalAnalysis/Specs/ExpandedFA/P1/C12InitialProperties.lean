import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
Independent statements for the vector-topology part of
`fa2:p1:c12:initial-properties` (paper.tex 2255–2262).

`B y x` is bilinear over the original scalar field. `B.SeparatingRight`
means that only `x = 0` is annihilated by every `y`; no separation on Y
is required. Real scalar multiplication on X is obtained by restricting
the given module along ℝ → 𝕜, without a norm on X or Y.
All topological conclusions use the accepted initial pairing topology.
-/

namespace ExpandedFA.P1.C12InitialProperties.Spec

universe u v w
open scoped Topology
noncomputable section

def Hausdorff : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜), B.SeparatingRight →
    letI := C12DualPairSpec.DualPairTopologyValue 𝕜 X Y B
    T2Space X

/-- Joint continuity of vector addition. Separation is unnecessary here. -/
def AdditionContinuous : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜),
    letI := C12DualPairSpec.DualPairTopologyValue 𝕜 X Y B
    ContinuousAdd X

/-- Joint continuity for scalars in the original field, with its usual topology. -/
def ScalarMultiplicationContinuous : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜),
    letI := C12DualPairSpec.DualPairTopologyValue 𝕜 X Y B
    ContinuousSMul 𝕜 X

def LocalConvexity : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜),
    letI := Module.restrictScalars ℝ 𝕜 X
    letI := C12DualPairSpec.DualPairTopologyValue 𝕜 X Y B
    LocallyConvexSpace ℝ X

/-- Every zero neighborhood contains a convex, original-field-balanced
neighborhood. This includes an empty finite family of scalar tests. -/
def ConvexBalancedNeighborhoods : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜),
    letI := Module.restrictScalars ℝ 𝕜 X
    letI := C12DualPairSpec.DualPairTopologyValue 𝕜 X Y B
    ∀ U ∈ 𝓝 (0 : X), ∃ V ∈ 𝓝 (0 : X),
      Convex ℝ V ∧ Balanced 𝕜 V ∧ V ⊆ U


/-!
Independent statements for `fa2:p1:c12:initial-properties`, paper.tex 2255–2262.
The span is the algebraic `Submodule.span`, hence consists of finite scalar
linear combinations; no closure is taken. The general scalar-test statement
holds even without separation. The Hausdorff conclusion requires separation
only on X. The dual used in the normed-space specialization is formed using
E's original norm topology, before putting the weak topology on its carrier.
Neither completeness nor a nonzero-space hypothesis is imposed.
-/

/-- Continuous scalar-linear tests of the initial pairing topology. -/
def ContinuousIffSpan : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜) (g : X →ₗ[𝕜] 𝕜),
    @Continuous X 𝕜 (C12DualPairSpec.DualPairTopologyValue 𝕜 X Y B)
      inferInstance g ↔ g ∈ Submodule.span 𝕜 (Set.range B)

/-- The full initial-properties assertion, including vector topology. -/
def InitialProperties : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜), B.SeparatingRight →
    letI := Module.restrictScalars ℝ 𝕜 X
    letI := C12DualPairSpec.DualPairTopologyValue 𝕜 X Y B
    T2Space X ∧ LocallyConvexSpace ℝ X ∧ ContinuousAdd X ∧
      ContinuousSMul 𝕜 X ∧
      ∀ g : X →ₗ[𝕜] 𝕜, Continuous g ↔ g ∈ Submodule.span 𝕜 (Set.range B)

/-- Hahn–Banach supplies the separation hypothesis for the original dual. -/
def NormDualSeparates : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (topDualPairing 𝕜 E).SeparatingRight

/-- Equality of the weak continuous linear dual and the original norm dual,
expressed on the same algebraic linear maps. -/
def WeakContinuousDual : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (g : E →ₗ[𝕜] 𝕜),
    @Continuous E 𝕜 (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      inferInstance g ↔ ∃ f : E →L[𝕜] 𝕜, f.toLinearMap = g

/-- The point-separating initial topology applies to every normed space. -/
def WeakInitialProperties : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    letI := NormedSpace.restrictScalars ℝ 𝕜 E
    letI := C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
    T2Space E ∧ LocallyConvexSpace ℝ E ∧ ContinuousAdd E ∧ ContinuousSMul 𝕜 E

end
end ExpandedFA.P1.C12InitialProperties.Spec
