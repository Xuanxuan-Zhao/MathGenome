import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.StabilityDefinitions

/-! Stability of C¹ equilibria, paper.tex d13:12:definitions.

The predicates explicitly require a complete forward lifespan in the shared
partial flow. Regularity, domain membership and the equilibrium equation are
inputs, so none of these properties is silently inferred from a curve's name.
At a general equilibrium every bound measures distance to that equilibrium;
the last theorem checks the specialization to the source's origin formulas.
-/
noncomputable section

namespace D13Unified.Ch12.StabilityDefinitions
open Specs.D13Unified.Ch12.StabilityDefinitions
universe u

/-- Existence of the canonical solution for every real t ≥ 0. -/
def ForwardComplete : ForwardCompleteType.{u} := forwardCompleteValue

/-- Lyapunov stability at an arbitrary admissible equilibrium. -/
def LyapunovStableAt : EquilibriumPredicateType.{u} := lyapunovStableAtValue

/-- Lyapunov stability and attraction of a neighborhood of the equilibrium. -/
def LocallyAsymptoticallyStableAt : EquilibriumPredicateType.{u} :=
  locallyAsymptoticallyStableAtValue

/-- A uniform exponential estimate and complete forward existence nearby. -/
def LocallyExponentiallyStableAt : EquilibriumPredicateType.{u} :=
  locallyExponentiallyStableAtValue

/-- Instability means failure of Lyapunov stability at the equilibrium. -/
def UnstableAt : EquilibriumPredicateType.{u} := unstableAtValue

/-- The origin is Lyapunov stable, including forward existence. -/
def LyapunovStable : OriginPredicateType.{u} := lyapunovStableValue

/-- The origin is stable and attracts every sufficiently near initial point. -/
def LocallyAsymptoticallyStable : OriginPredicateType.{u} :=
  locallyAsymptoticallyStableValue

/-- Uniform local exponential stability of the origin. -/
def LocallyExponentiallyStable : OriginPredicateType.{u} :=
  locallyExponentiallyStableValue

/-- Failure of stability of the origin. -/
def Unstable : OriginPredicateType.{u} := unstableValue

/-- Translating the center back to zero recovers exactly the norm formulas. -/
theorem origin_specializations : OriginSpecializations.{u} := by
  intro E _ _ _ F hF h0 heq
  simp only [lyapunovStableAtValue, lyapunovStableValue,
    locallyAsymptoticallyStableAtValue, locallyAsymptoticallyStableValue,
    locallyExponentiallyStableAtValue, locallyExponentiallyStableValue,
    unstableAtValue, unstableValue, dist_zero_right, iff_self, and_self]

end D13Unified.Ch12.StabilityDefinitions
