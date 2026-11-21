import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05NormExtension
import Mathlib.Analysis.Normed.Module.Convex

/-!
Independent specifications for `fa2:p1:c12:convex-closure` (paper.tex 2419–2446)
and the identical assertion deferred from Chapter 6 (1249–1261).
The weak topology is the existing canonical σ(E,E′), with E′ computed using
its original norm topology. Convexity is over ℝ even for complex spaces.
No completeness, nonemptiness, or nontriviality assumption is imposed.
The induced-subspace topology assertion is specified below.
-/

namespace ExpandedFA.P1.C12ConvexClosure.Spec

universe u v
noncomputable section

/-- Weak and norm closures agree for every real-convex subset. -/
def ConvexClosure : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ C : Set E, Convex ℝ C →
      @closure E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) C = closure C

/-- Every norm-closed real-convex set is weakly closed. -/
def ClosedConvex : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ C : Set E, Convex ℝ C → IsClosed C →
      @IsClosed E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) C

/-- In particular every norm-closed scalar-linear subspace is weakly closed. -/
def ClosedSubspace : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E), IsClosed (M : Set E) →
      @IsClosed E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) (M : Set E)

/-- Restriction is contractive, and every subspace test has a norm-preserving
extension. Thus no closedness of the subspace is needed. -/
def ScalarTests : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M : Submodule 𝕜 E),
    (∀ F : E →L[𝕜] 𝕜, ∃ f : M →L[𝕜] 𝕜,
      (∀ m : M, f m = F (m : E)) ∧ ‖f‖ ≤ ‖F‖) ∧
    (∀ f : M →L[𝕜] 𝕜, ∃ F : E →L[𝕜] 𝕜,
      (∀ m : M, F (m : E) = f m) ∧ ‖F‖ = ‖f‖)

/-- Equality of the two families as sets of scalar-valued functions on M. -/
def TestFamilyEquality : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M : Submodule 𝕜 E),
    Set.range (fun F : E →L[𝕜] 𝕜 => fun m : M => F (m : E)) =
      Set.range (fun f : M →L[𝕜] 𝕜 => fun m : M => f m)

/-- The ambient weak topology induces exactly the inherited-norm weak
topology, on every scalar-linear subspace including nonclosed ones. -/
def InducedTopology : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M : Submodule 𝕜 E),
    TopologicalSpace.induced (fun m : M => (m : E))
        (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) =
      C12DualPairSpec.DualPairTopologyValue 𝕜 M (M →L[𝕜] 𝕜) (topDualPairing 𝕜 M)

end
end ExpandedFA.P1.C12ConvexClosure.Spec
