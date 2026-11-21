import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.TestFunctionBoundedSets

/-! Independent statement for the finite-order part of
`paper.tex:17120`, `fa2:p4:finite-order`. The constant and order may depend
on the compact set. A real constant is automatically finite. -/

open Set TopologicalSpace
open scoped Distributions

namespace Specs.ExpandedFA.Distributions.DistributionFiniteOrder
open _root_.ExpandedFA.Distributions

/-- A scalar-linear functional is a distribution precisely when it has a
finite-order estimate on each compact step. This includes both scalar fields,
all dimensions, and every open domain. -/
def finiteOrderCriterionType : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
    (u : Tests 𝕜 Ω →ₗ[𝕜] 𝕜),
    Continuous u ↔
      ∀ (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω),
        ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ φ : Step 𝕜 K,
          ‖u (TestFunction.ofSupportedIn hK φ)‖ ≤ C * stepSeminorm 𝕜 K m φ

end Specs.ExpandedFA.Distributions.DistributionFiniteOrder
