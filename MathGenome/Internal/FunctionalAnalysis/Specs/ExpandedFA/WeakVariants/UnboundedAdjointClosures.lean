import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.BanachAdjoint
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06DoubleAnnihilator
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap

/-! Independent statements for the adjoint stage of
`fa2:p2:weakstar-adjoint-closures`, paper.tex 8939–8950.

The operator includes its domain. The adjoint is the canonical scalar-linear
Banach adjoint fixed in the upstream specification, using the ambient X norm.
Weak-star closures explicitly use σ(E′, E); plain closures use the original
operator norm on the continuous dual. Reflexivity is surjectivity of the shared
canonical evaluation map. No norm-density assertion is made without it. -/

namespace ExpandedFA.WeakVariants.UnboundedAdjointClosures.Spec

universe u v w
open ExpandedFA.Unbounded ExpandedFA.P1

/-- Weak-star closure of the actual adjoint range equals the annihilator of
A's kernel, for both real and complex Banach spaces. -/
def WeakStarRangeClosure : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (A : Operator 𝕜 X Y), Dense (A.domain : Set X) → A.IsClosed →
    @closure (X →L[𝕜] 𝕜)
      (C12DualPairSpec.DualPairTopologyValue 𝕜 (X →L[𝕜] 𝕜) X
        (topDualPairing 𝕜 X).flip)
      ((BanachAdjointSpec.adjointValue A).toFun.range : Set (X →L[𝕜] 𝕜)) =
    (C04Annihilators.Spec.AnnihilatorValue 𝕜 X (A.ker : Set X) :
      Set (X →L[𝕜] 𝕜))

/-- D(A′) is weak-star dense in Y′. -/
def WeakStarDomainClosure : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (A : Operator 𝕜 X Y), Dense (A.domain : Set X) → A.IsClosed →
    @closure (Y →L[𝕜] 𝕜)
      (C12DualPairSpec.DualPairTopologyValue 𝕜 (Y →L[𝕜] 𝕜) Y
        (topDualPairing 𝕜 Y).flip)
      ((BanachAdjointSpec.adjointValue A).domain : Set (Y →L[𝕜] 𝕜)) = Set.univ

/-- Reflexivity of X permits norm closure in the range identity. -/
def NormRangeClosure : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 X →
    ∀ (A : Operator 𝕜 X Y), Dense (A.domain : Set X) → A.IsClosed →
    closure ((BanachAdjointSpec.adjointValue A).toFun.range : Set (X →L[𝕜] 𝕜)) =
    (C04Annihilators.Spec.AnnihilatorValue 𝕜 X (A.ker : Set X) :
      Set (X →L[𝕜] 𝕜))

/-- Reflexivity of Y permits norm density of D(A′) in Y′. -/
def NormDomainClosure : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 Y →
    ∀ (A : Operator 𝕜 X Y), Dense (A.domain : Set X) → A.IsClosed →
    closure ((BanachAdjointSpec.adjointValue A).domain : Set (Y →L[𝕜] 𝕜)) = Set.univ

end ExpandedFA.WeakVariants.UnboundedAdjointClosures.Spec
