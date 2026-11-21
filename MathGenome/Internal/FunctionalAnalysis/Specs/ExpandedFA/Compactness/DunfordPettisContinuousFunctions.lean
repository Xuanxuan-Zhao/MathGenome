import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.DunfordPettisCriterion
import Mathlib.Topology.ContinuousMap.Compact

/-! The C(K) assertion of `fa2:p2:dp-classical-examples`, paper.tex:9841–9864.
K is an arbitrary compact Hausdorff space, including the empty space.
The dual and bidual are continuous scalar-linear duals. The second sequence
is weakly null against the entire bidual, not merely weak-star null.
The target Banach space has an arbitrary universe. -/
namespace ExpandedFA.Compactness.DunfordPettisContinuousFunctions.Spec
universe u w

open DunfordPettisCriterion.Spec

def ContinuousFunctionsTheorem (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K],
    WeakNullTestingPropertyValue 𝕜 C(K, 𝕜) ∧
      DunfordPettisPropertyValue.{0,u,w} 𝕜 C(K, 𝕜)

def RealTheorem : Prop := ContinuousFunctionsTheorem.{u,w} ℝ

def ComplexTheorem : Prop := ContinuousFunctionsTheorem.{u,w} ℂ

end ExpandedFA.Compactness.DunfordPettisContinuousFunctions.Spec
