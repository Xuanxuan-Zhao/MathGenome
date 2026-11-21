import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Topology.Bases

/-!
Independent statement of `fa2:p1:small-cap`, paper.tex:5718–5724.
Separability is for the original topology on K. Weak compactness and weak
closedness use σ(E,E′) for the continuous scalar-linear dual over ℝ or ℂ.
Real convexity is used in both cases. A uniform bound d < ε on all seminorm
distances expresses diameter < ε, including the singleton and zero-seminorm cases.
The proper subset may be empty, as allowed in the source.
-/

universe u v

namespace ExpandedFA.P1.SmallCapSpec

/-- The complete small-cap assertion over either manuscript scalar field. -/
def smallCapType : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [LocallyConvexSpace ℝ E] (K : Set E),
    K.Nonempty → TopologicalSpace.SeparableSpace K →
    IsCompact (toWeakSpace 𝕜 E '' K) → Convex ℝ K →
    ∀ (p : Seminorm 𝕜 E), Continuous p → ∀ ε : ℝ, 0 < ε →
      ∃ C : Set E, C ⊂ K ∧ IsClosed (toWeakSpace 𝕜 E '' C) ∧ Convex ℝ C ∧
        ∃ d : ℝ, 0 ≤ d ∧ d < ε ∧
          ∀ x ∈ K \ C, ∀ y ∈ K \ C, p (x - y) ≤ d

end ExpandedFA.P1.SmallCapSpec
