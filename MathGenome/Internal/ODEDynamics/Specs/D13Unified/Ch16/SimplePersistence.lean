import Mathlib.Analysis.Calculus.ImplicitContDiff
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.LinearizedStability
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.LinearizedInstability

/-! Scalar families are written parameter first: `f (μ,x)` represents
`x' = f(x,μ)` or `xₙ₊₁ = F_μ(xₙ)`. The open set is the actual local
parameter/state domain. No assumption is imposed outside it. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Specs.D13Unified.Ch16.SimplePersistence

/-- The state partial derivative, with the parameter held fixed. -/
def stateDerivative (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  fderiv ℝ f z (0, 1)

/-- All zeros in one fixed product neighborhood, including existence for every
parameter in its interval and C¹ regularity on that whole interval. -/
def IsLocalZeroGraph (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ))
    (ψ : ℝ → ℝ) (a b : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ ψ 0 = 0 ∧
  Metric.ball 0 a ×ˢ Metric.ball 0 b ⊆ U ∧
  ContDiffOn ℝ 1 ψ (Metric.ball 0 a) ∧
  ∀ μ ∈ Metric.ball 0 a,
    ψ μ ∈ Metric.ball 0 b ∧
    ∀ x ∈ Metric.ball 0 b, f (μ,x) = 0 ↔ x = ψ μ


def stateDerivativeType := (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
def stateDerivativeValue : stateDerivativeType := fun f z => fderiv ℝ f z (0,1)
def localZeroGraphType := (ℝ × ℝ → ℝ) → Set (ℝ × ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop
def localZeroGraphValue : localZeroGraphType := fun f U ψ a b =>
  0 < a ∧ 0 < b ∧ ψ 0 = 0 ∧
  Metric.ball 0 a ×ˢ Metric.ball 0 b ⊆ U ∧
  ContDiffOn ℝ 1 ψ (Metric.ball 0 a) ∧
  ∀ μ ∈ Metric.ball 0 a, ψ μ ∈ Metric.ball 0 b ∧
    ∀ x ∈ Metric.ball 0 b, f (μ,x) = 0 ↔ x = ψ μ

/-- Persistence and constancy of the scalar linearized flow type. The last
clause records that both derivatives have the same nonzero sign. -/
def flowPersistence : Prop :=
  ∀ (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)),
    IsOpen U → (0,0) ∈ U → ContDiffOn ℝ 1 f U → f (0,0) = 0 →
    stateDerivative f (0,0) ≠ 0 →
    ∃ ψ : ℝ → ℝ, ∃ a b : ℝ, IsLocalZeroGraph f U ψ a b ∧
      ∀ μ ∈ Metric.ball 0 a,
        stateDerivative f (μ,ψ μ) * stateDerivative f (0,0) > 0

/-- For maps only multiplier 1 is excluded. Strict attraction and repulsion
inequalities persist when they held initially. In particular nothing asserts
hyperbolicity or constant stability when the initial multiplier is -1. -/
def mapPersistence : Prop :=
  ∀ (F : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)),
    IsOpen U → (0,0) ∈ U → ContDiffOn ℝ 1 F U → F (0,0) = 0 →
    stateDerivative F (0,0) ≠ 1 →
    ∃ ψ : ℝ → ℝ, ∃ a b : ℝ,
      IsLocalZeroGraph (fun z => F z - z.2) U ψ a b ∧
      ∀ μ ∈ Metric.ball 0 a,
        stateDerivative F (μ,ψ μ) ≠ 1 ∧
        (|stateDerivative F (0,0)| < 1 → |stateDerivative F (μ,ψ μ)| < 1) ∧
        (1 < |stateDerivative F (0,0)| → 1 < |stateDerivative F (μ,ψ μ)|)

/-- The partial derivative really is the derivative of the scalar state slice. -/
def stateDerivativeSlice : Prop :=
  ∀ (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ), DifferentiableAt ℝ f z →
    HasDerivAt (fun x => f (z.1,x)) (stateDerivative f z) z.2

/-- Negative and positive scalar derivatives give the expected local directions
of the actual nonlinear vector field, on both sides of its equilibrium. -/
def flowDirections : Prop :=
  ∀ (g : ℝ → ℝ) (p l : ℝ), g p = 0 → HasDerivAt g l p → l ≠ 0 →
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, |x-p| < r → x ≠ p →
      (l < 0 → g x * (x-p) < 0) ∧ (0 < l → 0 < g x * (x-p))

/-- Strict scalar multiplier criteria for the nonlinear map, in the actual
open domain. Repulsion is expressed by uniform radial expansion until exit. -/
def mapStability : Prop :=
  ∀ (G : ℝ → ℝ) (V : Set ℝ) (p l : ℝ), IsOpen V → p ∈ V →
    G p = p → HasDerivAt G l p →
    (|l| < 1 →
      (∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-p| < δ → ∀ n : ℕ, G^[n] x ∈ V) ∧
      Specs.D13Unified.Ch15.DiscreteDefinitions.LocallyExponentiallyStable G p ∧
      Specs.D13Unified.Ch15.DiscreteDefinitions.AsymptoticallyStable G p) ∧
    (1 < |l| → ∃ q r : ℝ, 1 < q ∧ 0 < r ∧ Metric.ball p r ⊆ V ∧
      ∀ x, |x-p| < r → q * |x-p| ≤ |G x-p|)

/-- The scalar stability tests on the canonical partial flow, including actual
forward existence in the stable case and actual finite-time escape in the
unstable case. Coordinates are centered at the equilibrium. -/
def scalarFlowStability : Prop :=
  ∀ (F : _root_.D13Unified.AutonomousODE ℝ)
    (hF : ContDiffOn ℝ 1 (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F) F.domain)
    (h0 : (0 : ℝ) ∈ F.domain)
    (heq : Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F 0 = 0),
    let l := deriv (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F) 0
    (l < 0 → Specs.D13Unified.Ch12.StabilityDefinitions.locallyExponentiallyStableValue F hF h0 heq) ∧
    (0 < l → Specs.D13Unified.Ch12.LinearizedInstability.EscapeWitness F ∧
      Specs.D13Unified.Ch12.StabilityDefinitions.unstableValue F hF h0 heq)

/-- A genuine local realization of the family at a shifted equilibrium.
`y` denotes `x-p`; its domain is exactly the original parameter slice. -/
def flowBranchStability : Prop :=
  ∀ (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)),
    IsOpen U → (0,0) ∈ U → ContDiffOn ℝ 1 f U → f (0,0) = 0 →
    stateDerivative f (0,0) ≠ 0 →
    ∃ ψ : ℝ → ℝ, ∃ a b : ℝ, IsLocalZeroGraph f U ψ a b ∧
      ∀ μ ∈ Metric.ball 0 a,
        ∃ F : _root_.D13Unified.AutonomousODE ℝ,
          F.domain = {y | (μ,ψ μ+y) ∈ U} ∧
          (∀ y ∈ F.domain,
            Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F y = f (μ,ψ μ+y)) ∧
          ∃ (hF : ContDiffOn ℝ 1
            (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F) F.domain)
            (h0 : (0 : ℝ) ∈ F.domain)
            (heq : Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F 0 = 0),
          (stateDerivative f (0,0) < 0 →
            Specs.D13Unified.Ch12.StabilityDefinitions.locallyExponentiallyStableValue F hF h0 heq) ∧
          (0 < stateDerivative f (0,0) →
            Specs.D13Unified.Ch12.LinearizedInstability.EscapeWitness F ∧
            Specs.D13Unified.Ch12.StabilityDefinitions.unstableValue F hF h0 heq)

/-- The strict multiplier tests apply to the actual state slice, whose
iterates remain in that slice until the stated first exit. -/
def mapBranchStability : Prop :=
  ∀ (F : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)),
    IsOpen U → (0,0) ∈ U → ContDiffOn ℝ 1 F U → F (0,0) = 0 →
    stateDerivative F (0,0) ≠ 1 →
    ∃ ψ : ℝ → ℝ, ∃ a b : ℝ,
      IsLocalZeroGraph (fun z => F z - z.2) U ψ a b ∧
      ∀ μ ∈ Metric.ball 0 a,
        (|stateDerivative F (0,0)| < 1 →
          (∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-ψ μ| < δ → ∀ n : ℕ,
            (μ, (fun y => F (μ,y))^[n] x) ∈ U) ∧
          Specs.D13Unified.Ch15.DiscreteDefinitions.LocallyExponentiallyStable
            (fun x => F (μ,x)) (ψ μ) ∧
          Specs.D13Unified.Ch15.DiscreteDefinitions.AsymptoticallyStable
            (fun x => F (μ,x)) (ψ μ)) ∧
        (1 < |stateDerivative F (0,0)| →
          _root_.D13Unified.Ch15.LinearizedInstability.LocallyUnstable
            (fun x => F (μ,x)) {x | (μ,x) ∈ U} (ψ μ))

end Specs.D13Unified.Ch16.SimplePersistence
