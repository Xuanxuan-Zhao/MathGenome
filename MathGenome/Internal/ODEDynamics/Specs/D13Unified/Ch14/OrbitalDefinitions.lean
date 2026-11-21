import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Orbits
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Independent definitions for paper.tex, d13:14:orbital-definition and the
estimate in d13:14:orbital-stability.

The solution is the canonical partial autonomous flow, with its actual maximal
interval. The stability predicates below can be applied to any set; their
source application is a compact nonconstant periodic orbit, expressed by
`compactPeriodicOrbitValue`. In particular one uses `Orbits.orbit F p`, rather
than a parametrized orbit with a prescribed phase. The state space can be any
finite-dimensional real normed space with any fixed norm.
-/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D13Unified.Ch14.OrbitalDefinitions
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open _root_.D13Unified.Ch11.Orbits

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The source orbit hypothesis, using the shared orbit and least-period
notions, including two-sided completeness of the periodic trajectory. -/
def compactPeriodicOrbitValue (F : AutonomousODE E) (Γ : Set E) : Prop :=
  IsCompact Γ ∧ ∃ p ∈ F.domain,
    ¬ IsConstant F p ∧ HasLeastPeriod F p ∧ Γ = orbit F p

def orbitPredicateType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    AutonomousODE E → Set E → Prop

/-- Forward completeness includes admissibility of the initial point and
containment of every nonnegative real time in the actual maximal interval. -/
def forwardCompleteValue (F : AutonomousODE E) (x : E) : Prop :=
  x ∈ F.domain ∧ Ici (0 : ℝ) ⊆ (flowInterval F x).carrier

def forwardCompleteType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    AutonomousODE E → E → Prop

/-- All nearby admissible initial states have complete forward solutions and
stay within ε of the entire set Γ at every nonnegative time. -/
def orbitalLyapunovStableValue (F : AutonomousODE E) (Γ : Set E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ F.domain, Metric.infDist x Γ < δ →
      forwardCompleteValue F x ∧
        ∀ t : ℝ, 0 ≤ t → Metric.infDist (flow F t x) Γ < ε

/-- Stability together with attraction of a single neighborhood of Γ.
The limit is of distance to Γ, with no choice of phase. -/
def orbitalAsymptoticallyStableValue (F : AutonomousODE E) (Γ : Set E) : Prop :=
  orbitalLyapunovStableValue F Γ ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ F.domain, Metric.infDist x Γ < δ →
      forwardCompleteValue F x ∧
        Tendsto (fun t : ℝ => Metric.infDist (flow F t x) Γ) atTop (𝓝 0)

/-- Instability is precisely failure of orbital Lyapunov stability. -/
def orbitalUnstableValue (F : AutonomousODE E) (Γ : Set E) : Prop :=
  ¬ orbitalLyapunovStableValue F Γ

/-- Uniform local exponential decay of distance, in actual elapsed time,
including initial states on Γ and time zero. Forward existence is required. -/
def exponentiallyOrbitallyStableValue (F : AutonomousODE E) (Γ : Set E) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ α : ℝ, 0 < α ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ F.domain, Metric.infDist x Γ < δ →
      forwardCompleteValue F x ∧ ∀ t : ℝ, 0 ≤ t →
        Metric.infDist (flow F t x) Γ ≤
          C * Real.exp (-α * t) * Metric.infDist x Γ

/-- Equivalent domain formulation of forward completeness. -/
def ForwardCompleteDomain : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : AutonomousODE E) (x : E),
    forwardCompleteValue F x ↔ ∀ t : ℝ, 0 ≤ t → (t, x) ∈ flowDomain F

end Specs.D13Unified.Ch14.OrbitalDefinitions
