import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.TestFunctionLFTopology
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Topology.Metrizable.Basic

/-! Independent statements for the compact-step, bounded-set, and sequential
parts of paper.tex:17120--17166. The finite-order assertion is allocated to
`ops_distribution_order`. All spaces have their native upstream topologies. -/

open Set TopologicalSpace Filter
open scoped Topology Distributions

namespace Specs.ExpandedFA.Distributions.TestFunctionBoundedSets
open _root_.ExpandedFA.Distributions

/-- The displayed Fréchet topology is the topology induced from the LF space. -/
def stepTopologyType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω),
  Topology.IsEmbedding (TestFunction.ofSupportedIn (F := 𝕜) (n := ⊤) hK) ∧
    WithSeminorms (stepSeminorm 𝕜 K) ∧ MetrizableSpace (Step 𝕜 K)

/-- Completeness is with respect to the standard additive uniformity of the step. -/
def stepCompleteType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (K : Compacts (Domain d)), CompleteSpace (Step 𝕜 K)

/-- An image presentation expresses both common compact support and all of the
displayed derivative bounds, with no assumed boundedness certificate. -/
def boundedCriterionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (B : Set (Tests 𝕜 Ω)),
  Bornology.IsVonNBounded 𝕜 B ↔
    ∃ (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω) (S : Set (Step 𝕜 K)),
      B = TestFunction.ofSupportedIn hK '' S ∧
        ∀ m, BddAbove (stepSeminorm 𝕜 K m '' S)

/-- Uniform convergence on the common compact of every coordinate partial
derivative, with one support for the entire sequence (not just an eventual
support condition). Coordinate words include order zero. -/
def sequenceCriterionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ℕ → Tests 𝕜 Ω),
  Tendsto u atTop (𝓝 0) ↔
    ∃ (K : Compacts (Domain d)), (K : Set (Domain d)) ⊆ Ω ∧
      (∀ n, tsupport (u n) ⊆ K) ∧
      ∀ k (a : Fin k → Fin d) (ε : ℝ), 0 < ε →
        ∀ᶠ n in atTop, ∀ x ∈ (K : Set (Domain d)),
          ‖iteratedFDeriv ℝ k (u n) x (fun j => coordinateVector (a j))‖ < ε

end Specs.ExpandedFA.Distributions.TestFunctionBoundedSets
