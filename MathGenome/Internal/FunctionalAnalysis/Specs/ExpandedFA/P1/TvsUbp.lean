import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Topology.GDelta.Basic

/-! Independent statements of topological Banach–Steinhaus,
`paper.tex:1958–1966`. Families may have any index type, including an empty
one. The real module structures are the restrictions of the original scalar
structures. Boundedness is the manuscript's positive-real-dilation definition.
No local convexity, metrizability, or completeness is imposed in the main
statement. Equicontinuity is stated explicitly using zero neighborhoods. -/

open Set Filter
open scoped Topology

namespace ExpandedFA.P1.TvsUbpSpec

/-- A nonmeagre bounded-orbit locus implies boundedness everywhere and
uniform control on a single source zero neighborhood for each target one. -/
def TopologicalBanachSteinhaus : Prop :=
  ∀ (𝕜 E F ι : Type*) [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
    [Module 𝕜 E] [Module 𝕜 F] [Module ℝ E] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 E] [IsScalarTower ℝ 𝕜 F]
    [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [T2Space E] [T2Space F],
    ∀ A : ι → E →L[𝕜] F,
      ¬ IsMeagre {x : E | Bounded (range fun i => A i x)} →
      (∀ x : E, Bounded (range fun i => A i x)) ∧
      ∀ V ∈ 𝓝 (0 : F), ∃ U ∈ 𝓝 (0 : E), ∀ i, A i '' U ⊆ V

/-- Pointwise bounded families on an F-space are equicontinuous, including
F-spaces which are not locally convex. Completeness is the translation
completeness of the original topology, as in the shared interface. -/
def FSpaceBanachSteinhaus : Prop :=
  ∀ (𝕜 E F ι : Type*) [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
    [Module 𝕜 E] [Module 𝕜 F] [Module ℝ E] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 E] [IsScalarTower ℝ 𝕜 F]
    [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [T2Space E] [T2Space F],
    FSpace 𝕜 E → ∀ A : ι → E →L[𝕜] F,
      (∀ x : E, Bounded (range fun i => A i x)) →
      ∀ V ∈ 𝓝 (0 : F), ∃ U ∈ 𝓝 (0 : E), ∀ i, A i '' U ⊆ V

end ExpandedFA.P1.TvsUbpSpec
