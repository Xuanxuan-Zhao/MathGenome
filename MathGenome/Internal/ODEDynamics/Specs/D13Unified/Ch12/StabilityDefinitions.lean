import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Flow

/-!
Independent specification for paper.tex, Chapter 12, d13:12:definitions.

We use the shared canonical maximal flow, never a new solution selection.
Every stability predicate takes the C¹ hypothesis and the admissible
equilibrium as inputs. Thus its application is restricted to precisely the
setting of the source. The arbitrary finite-dimensional norm is retained.
Forward completeness means membership in the actual flow domain at every
nonnegative time; an ambient representative alone does not imply existence.
The versions at an arbitrary equilibrium use distance to that equilibrium.
-/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D13Unified.Ch12.StabilityDefinitions
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters
universe u

/-- A predicate on admissible initial points of the existing partial flow. -/
def ForwardCompleteType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : AutonomousODE E),
    ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain → E → Prop

/-- The entire half-line belongs to the actual domain, including time zero. -/
def forwardCompleteValue : ForwardCompleteType.{u} :=
  fun F _ x => ∀ t : ℝ, 0 ≤ t → (t, x) ∈ flowDomain F

/-- The hypotheses are inputs, not conclusions or assumed certificates of
stability. In particular a point outside Ω cannot be supplied as an equilibrium. -/
def EquilibriumPredicateType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : AutonomousODE E),
    ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    (p : E) → p ∈ F.domain → autonomousEvalValue F p = 0 → Prop

def OriginPredicateType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : AutonomousODE E),
    ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    (0 : E) ∈ F.domain → autonomousEvalValue F 0 = 0 → Prop

/-- ε and δ are independent of the initial point and of time. -/
def lyapunovStableAtValue : EquilibriumPredicateType.{u} := by
  intro E _ _ _ F hF p _ _
  exact ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ F.domain, dist x p < δ →
      forwardCompleteValue F hF x ∧ ∀ t : ℝ, 0 ≤ t → dist (flow F t x) p < ε

/-- Stability plus attraction of every admissible point in one fixed ball.
Convergence uses the real-time filter t → +∞, not an integer subsequence. -/
def locallyAsymptoticallyStableAtValue : EquilibriumPredicateType.{u} := by
  intro E _ _ _ F hF p hp heq
  exact lyapunovStableAtValue F hF p hp heq ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ F.domain, dist x p < δ →
      forwardCompleteValue F hF x ∧ Tendsto (fun t : ℝ => flow F t x) atTop (𝓝 p)

/-- All three positive constants are uniform in initial point and time. -/
def locallyExponentiallyStableAtValue : EquilibriumPredicateType.{u} := by
  intro E _ _ _ F hF p _ _
  exact ∃ C α δ : ℝ, 0 < C ∧ 0 < α ∧ 0 < δ ∧
    ∀ x ∈ F.domain, dist x p < δ → forwardCompleteValue F hF x ∧
      ∀ t : ℝ, 0 ≤ t → dist (flow F t x) p ≤ C * Real.exp (-α * t) * dist x p

/-- Failure of Lyapunov stability, for the same C¹ field and equilibrium. -/
def unstableAtValue : EquilibriumPredicateType.{u} := by
  intro E _ _ _ F hF p hp heq
  exact ¬ lyapunovStableAtValue F hF p hp heq

/-- The source's origin formulation, with the original strict norm bounds. -/
def lyapunovStableValue : OriginPredicateType.{u} := by
  intro E _ _ _ F hF _ _
  exact ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ F.domain, ‖x‖ < δ →
      forwardCompleteValue F hF x ∧ ∀ t : ℝ, 0 ≤ t → ‖flow F t x‖ < ε

def locallyAsymptoticallyStableValue : OriginPredicateType.{u} := by
  intro E _ _ _ F hF h0 heq
  exact lyapunovStableValue F hF h0 heq ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ F.domain, ‖x‖ < δ →
      forwardCompleteValue F hF x ∧ Tendsto (fun t : ℝ => flow F t x) atTop (𝓝 (0 : E))

def locallyExponentiallyStableValue : OriginPredicateType.{u} := by
  intro E _ _ _ F hF _ _
  exact ∃ C α δ : ℝ, 0 < C ∧ 0 < α ∧ 0 < δ ∧
    ∀ x ∈ F.domain, ‖x‖ < δ → forwardCompleteValue F hF x ∧
      ∀ t : ℝ, 0 ≤ t → ‖flow F t x‖ ≤ C * Real.exp (-α * t) * ‖x‖

def unstableValue : OriginPredicateType.{u} := by
  intro E _ _ _ F hF h0 heq
  exact ¬ lyapunovStableValue F hF h0 heq

/-- The distance-based versions specialize to the norm-based versions at zero. -/
def OriginSpecializations : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (h0 : (0 : E) ∈ F.domain) (heq : autonomousEvalValue F 0 = 0),
    (lyapunovStableAtValue F hF 0 h0 heq ↔ lyapunovStableValue F hF h0 heq) ∧
    (locallyAsymptoticallyStableAtValue F hF 0 h0 heq ↔
      locallyAsymptoticallyStableValue F hF h0 heq) ∧
    (locallyExponentiallyStableAtValue F hF 0 h0 heq ↔
      locallyExponentiallyStableValue F hF h0 heq) ∧
    (unstableAtValue F hF 0 h0 heq ↔ unstableValue F hF h0 heq)

end Specs.D13Unified.Ch12.StabilityDefinitions
