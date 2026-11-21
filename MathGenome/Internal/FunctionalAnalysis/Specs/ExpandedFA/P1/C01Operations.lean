import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Module.Basic

/-!
Independent statements for Proposition `fa2:p1:c01:operations`, paper.tex lines 126–133.
All distances, closures, balls and homeomorphisms use the topology induced by
this same norm. `RCLike` includes both real and complex scalars. Neither
completeness nor nontriviality of the vector space is required.
-/

namespace ExpandedFA.P1.C01Operations.Spec

/-- The norm distance has all metric axioms, including definiteness. -/
def InducedDistanceMetric : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (∀ x y : E, dist x y = ‖x - y‖) ∧
    (∀ x y : E, 0 ≤ dist x y) ∧
    (∀ x y : E, dist x y = 0 ↔ x = y) ∧
    (∀ x y : E, dist x y = dist y x) ∧
    (∀ x y z : E, dist x z ≤ dist x y + dist y z)

/-- Reverse triangle estimate and the precise Lipschitz constant. -/
def NormEstimates : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (∀ x y : E, |‖x‖ - ‖y‖| ≤ ‖x - y‖) ∧
    LipschitzWith 1 (norm : E → ℝ)

/-- Both operations are jointly continuous, with product domain topologies. -/
def OperationsContinuous : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Continuous (fun p : E × E => p.1 + p.2) ∧
    Continuous (fun p : 𝕜 × E => p.1 • p.2)

/-- Translation and its inverse are homeomorphisms on the norm topology. -/
def TranslationHomeomorphisms : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (v : E), ∃ h : E ≃ₜ E,
      (∀ x, h x = v + x) ∧ (∀ x, h.symm x = -v + x)

/-- Scalar multiplication by every nonzero scalar, with the stated inverse. -/
def NonzeroSMulHomeomorphisms : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (a : 𝕜), a ≠ 0 → ∃ h : E ≃ₜ E,
      (∀ x, h x = a • x) ∧ (∀ x, h.symm x = a⁻¹ • x)

/-- The actual topological closure is the carrier of a linear subspace. -/
def SubspaceClosureLinear : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E), ∃ N : Submodule 𝕜 E,
      (N : Set E) = closure (M : Set E)

/-- Convexity is over the underlying real space, using the canonical
restriction along `ℝ → 𝕜`. This does not assume an extra real action. -/
def NormBallsRealConvex : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    letI := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ (x : E) (r : ℝ), 0 < r →
      Convex ℝ (Metric.ball x r) ∧ Convex ℝ (Metric.closedBall x r)

/-- For each scalar of modulus at most one, its image of either zero-centered
ball is contained in that ball. This is balance over the original field. -/
def ZeroBallsBalanced : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (r : ℝ), 0 < r →
      (∀ (a : 𝕜), ‖a‖ ≤ 1 → ∀ y ∈ Metric.ball (0 : E) r,
        a • y ∈ Metric.ball (0 : E) r) ∧
      (∀ (a : 𝕜), ‖a‖ ≤ 1 → ∀ y ∈ Metric.closedBall (0 : E) r,
        a • y ∈ Metric.closedBall (0 : E) r)

end ExpandedFA.P1.C01Operations.Spec
