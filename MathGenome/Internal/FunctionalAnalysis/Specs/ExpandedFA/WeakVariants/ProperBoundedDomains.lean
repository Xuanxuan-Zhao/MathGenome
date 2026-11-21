import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.WeakVariants.NormTotalTests
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces

/-! Independent statements for `fa2:p2:source-convergence-domain-tests`.
The domain always has its subtype norm from X. Graphs live in X × Y,
with the product topology (equivalently the sum-norm topology).
No density, nonzero-space, or ambient completeness assumptions are implicit. -/
namespace ExpandedFA.WeakVariants.ProperBoundedDomains
universe u v w
noncomputable section

/-- The graph in the ambient product, including its exact domain. -/
def ambientGraph {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (D : Submodule 𝕜 X) (T : D →ₗ[𝕜] Y) : Set (X × Y) :=
  {z | ∃ d : D, (d : X) = z.1 ∧ T d = z.2}

/-- c₀₀ as an actual subspace of ℓ²; its subtype norm is the inherited ℓ² norm. -/
def finiteSupportDomain (𝕜 : Type u) [RCLike 𝕜] :
    Submodule 𝕜 (lp (fun _ : ℕ => 𝕜) 2) :=
  (P1.C01SequenceSpaces.Spec.C00ToLpValue 𝕜 2).range

namespace Spec

def NormTotalCriterion : Prop := NormTotalTests.Spec.NormTotalCriterion.{u,v}
def SeparatingTestsInsufficient : Prop := NormTotalTests.Spec.CoordinateCounterexample.{u}

def ClosedDomainClosedGraph : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (D : Submodule 𝕜 X) (T : D →L[𝕜] Y),
    IsClosed (D : Set X) → IsClosed (ambientGraph D T.toLinearMap)

def ClosedGraphClosedDomain : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (D : Submodule 𝕜 X) (T : D →L[𝕜] Y),
    IsClosed (ambientGraph D T.toLinearMap) → IsClosed (D : Set X)

def ProperDomainClosedGraphTheorem : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y]
    (D : Submodule 𝕜 X) (T : D →ₗ[𝕜] Y),
    IsClosed (D : Set X) → IsClosed (ambientGraph D T) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ d : D, ‖T d‖ ≤ C * ‖(d : X)‖

/-- Identification with precisely the finite-support sequences. -/
def FiniteSupportIdentification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : lp (fun _ : ℕ => 𝕜) 2),
    x ∈ finiteSupportDomain 𝕜 ↔ (Function.support (fun n => x n)).Finite

/-- X = ℓ², D = Y = c₀₀, T = id. Both norms are inherited, and T has bound one.
Its graph in X × Y is closed, while D is not closed and Y is incomplete. -/
def IncompleteTargetCounterexample : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    let X := lp (fun _ : ℕ => 𝕜) 2
    let D := finiteSupportDomain 𝕜
    (∀ d : D, ‖ContinuousLinearMap.id 𝕜 D d‖ = ‖(d : X)‖) ∧
    IsClosed (ambientGraph D (LinearMap.id : D →ₗ[𝕜] D)) ∧
    ¬ IsClosed (D : Set X) ∧ ¬ CompleteSpace D

end Spec
end
end ExpandedFA.WeakVariants.ProperBoundedDomains
