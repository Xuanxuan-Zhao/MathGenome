import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Independent specification of the null-sequence portion of
paper.tex:9496–9522. Complex absolute convexity means complex balancedness
and real convexity. In particular the disk is not merely the real
absolutely convex hull in a complex space. -/
namespace ExpandedFA.Compactness.NullSequenceDisksSpec

universe u v
noncomputable section
open Set Filter
open scoped Topology Pointwise

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E

/-- The closure of the real convex hull of the scalar-balanced hull. -/
def ClosedDiskValue (z : ℕ → E) : Set E :=
  closure (convexHull ℝ (balancedHull 𝕜 (range z)))

def ClosedDiskType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], (ℕ → E) → Set E

/-- A Banach realization of the entire algebraic disk span. The range and
gauge identities specify the original Minkowski space up to a linear
isometry, and the last equality records the positive-integer dilation
representation, also when the disk consists of zero. -/
def BanachDisk (C : Set E) : Prop :=
  ∃ (G : Type v) (_ : NormedAddCommGroup G) (_ : NormedSpace 𝕜 G)
    (_ : CompleteSpace G) (i : G →L[𝕜] E),
    Function.Injective i ∧ IsCompactOperator i ∧
    i '' Metric.closedBall (0 : G) 1 = C ∧
    LinearMap.range i.toLinearMap = Submodule.span 𝕜 C ∧
    (∀ x : G, ‖x‖ = gauge C (i x)) ∧
    (Submodule.span 𝕜 C : Set E) = ⋃ (n : ℕ) (_ : 1 ≤ n), (n : ℝ) • C

def NullSequenceDiskTheorem : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    ∀ z : ℕ → E, Tendsto z atTop (𝓝 0) →
      IsCompact (ClosedDiskValue (𝕜 := 𝕜) z) ∧
      BanachDisk (𝕜 := 𝕜) (ClosedDiskValue (𝕜 := 𝕜) z)

end
end ExpandedFA.Compactness.NullSequenceDisksSpec
