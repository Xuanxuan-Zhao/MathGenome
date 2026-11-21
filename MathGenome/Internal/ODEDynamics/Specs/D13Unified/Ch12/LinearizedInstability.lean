import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.StabilityDefinitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! Independent statement of the unstable assertion of paper.tex,
Theorem d13:12:linearized-stability. The matrix below represents the actual
Fréchet derivative in an arbitrary real basis. Its complexification is used
only for the spectral hypothesis. No restrictions are placed on the other
eigenvalues, and no complementary invariant space is assumed to be nonzero.
-/
noncomputable section
open Set

namespace Specs.D13Unified.Ch12.LinearizedInstability
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters Ch12.StabilityDefinitions
universe u v

/-- Escape at an actual nonnegative time in the canonical maximal interval.
The radius is fixed before the arbitrarily small initial perturbation. -/
def EscapeWitness {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : AutonomousODE E) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
    ∃ x ∈ F.domain, ‖x‖ < δ ∧ ∃ t : ℝ,
      0 ≤ t ∧ t ∈ (flowInterval F x).carrier ∧ ε ≤ ‖flow F t x‖

/-- Full original conclusion, including the explicit fixed-radius witness
and failure of the shared Lyapunov stability predicate. -/
def linearizedInstabilityType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : Type v} [Fintype n] [DecidableEq n]
    (basis : Module.Basis n ℝ E) (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (h0 : (0 : E) ∈ F.domain) (heq : autonomousEvalValue F 0 = 0),
    (∃ μ : ℂ, 0 < μ.re ∧ Module.End.HasEigenvalue
      (Matrix.toLinAlgEquiv'
        ((LinearMap.toMatrix basis basis
          (fderiv ℝ (autonomousEvalValue F) 0).toLinearMap).map Complex.ofReal)) μ) →
      EscapeWitness F ∧ unstableValue F hF h0 heq

/-- A local Chetaev criterion for the same partial flow. This is an auxiliary
reduction, not a replacement for the spectral hypothesis in the main target.
Its scalar function may be indefinite and its positive set approaches zero. -/
def ChetaevCriterion : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (h0 : (0 : E) ∈ F.domain) (heq : autonomousEvalValue F 0 = 0)
    (V : E → ℝ) (r c M : ℝ),
    0 < r → 0 < c →
    (∀ x, ‖x‖ < r → DifferentiableAt ℝ V x) →
    (∀ x, ‖x‖ < r → V x ≤ M) →
    (∀ x ∈ F.domain, ‖x‖ < r → 0 < V x →
      c * V x ≤ (fderiv ℝ V x) (autonomousEvalValue F x)) →
    (∀ δ : ℝ, 0 < δ → ∃ x ∈ F.domain, ‖x‖ < δ ∧ 0 < V x) →
      unstableValue F hF h0 heq

def EscapeImpliesUnstable : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (h0 : (0 : E) ∈ F.domain) (heq : autonomousEvalValue F 0 = 0),
    EscapeWitness F → unstableValue F hF h0 heq

/-- Compact continuation makes failure of stability equivalent to actual
escape; the forward-existence requirement cannot create a spurious witness. -/
def UnstableIffEscape : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (h0 : (0 : E) ∈ F.domain) (heq : autonomousEvalValue F 0 = 0),
    unstableValue F hF h0 heq ↔ EscapeWitness F

/-- Precise analytic output needed from the finite-dimensional spectral
construction. It is a predicate, not an assumed existence theorem. -/
def LinearGrowthCertificate {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) : Prop :=
  ∃ (V : E → ℝ) (C c : ℝ), 0 < C ∧ 0 < c ∧
    Differentiable ℝ V ∧
    (∀ x, |V x| ≤ C * ‖x‖ ^ 2) ∧
    (∀ x, ‖fderiv ℝ V x‖ ≤ C * ‖x‖) ∧
    (∀ x, 0 < V x → c * ‖x‖ ^ 2 ≤ (fderiv ℝ V x) (A x)) ∧
    (∀ δ : ℝ, 0 < δ → ∃ x : E, ‖x‖ < δ ∧ 0 < V x)

def CertificateImpliesEscape : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (h0 : (0 : E) ∈ F.domain) (heq : autonomousEvalValue F 0 = 0),
    LinearGrowthCertificate (fderiv ℝ (autonomousEvalValue F) 0) →
      EscapeWitness F ∧ unstableValue F hF h0 heq

end Specs.D13Unified.Ch12.LinearizedInstability
