import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.EberleinSmulian
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.Schur

/-!
Independent specifications for `fa2:p2:complete-continuity`, paper.tex:9602–9639.
The chapter assumes Banach spaces; the first three statements below also hold
for arbitrary normed spaces. Weak compactness uses the original continuous
scalar-linear dual, over either ℝ or ℂ. Relative norm compactness is compactness
of the closure in the original target. Sequence limits are the corresponding
images. Reflexivity is surjectivity of the shared canonical evaluation map.
No nonempty-set or nonzero-space assumption is imposed.
-/
namespace ExpandedFA.Compactness.CompleteContinuity.Spec

universe u v w
open Filter
open scoped Topology
open DefinitionsSpec

/-- The set formulation and sequential formulation of complete continuity. -/
def SetSequenceEquivalence : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y),
    (∀ K : Set X, @IsCompact X (P1.EberleinSmulian.Spec.weakTopology 𝕜 X) K →
      IsCompact (closure (T '' K))) ↔ IsCompletelyContinuousValue T

/-- Every compact operator is completely continuous. -/
def CompactCompletelyContinuous : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y),
    IsCompactLinearMapValue T.toLinearMap → IsCompletelyContinuousValue T

/-- For a reflexive domain, complete continuity is equivalent to compactness. -/
def ReflexiveEquivalence : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y],
    P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 X →
    ∀ T : X →L[𝕜] Y,
      IsCompletelyContinuousValue T ↔ IsCompactLinearMapValue T.toLinearMap

/-- The identity on the literal canonical ℓ¹ is completely continuous, is not
compact, and its domain is not reflexive. This applies to both scalar fields. -/
def L1Counterexample : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    let I := ContinuousLinearMap.id 𝕜 (P1.C01SequenceSpaces.SequenceLp 𝕜 1)
    IsCompletelyContinuousValue I ∧
      ¬ IsCompactLinearMapValue I.toLinearMap ∧
      ¬ P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜
        (P1.C01SequenceSpaces.SequenceLp 𝕜 1)

end ExpandedFA.Compactness.CompleteContinuity.Spec
