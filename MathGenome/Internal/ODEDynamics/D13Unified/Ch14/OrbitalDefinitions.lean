import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.OrbitalDefinitions

/-!
Orbital stability for the canonical partial flow (paper.tex, Chapter 14).

For a compact nonconstant periodic orbit Γ, the four predicates measure
`Metric.infDist` to Γ. They quantify over initial states in the actual open
state domain. All nonnegative times must belong to the actual maximal solution
interval. No convergence to any prescribed moving phase is required.

The predicates also make sense for other sets; `IsCompactPeriodicOrbit` records
the precise source application using the existing canonical orbit objects.
-/
noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch14.OrbitalDefinitions
open Ch06.StateDerivative

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Γ is a compact nonconstant periodic orbit of the canonical partial flow. -/
def IsCompactPeriodicOrbit (F : AutonomousODE E) (Γ : Set E) : Prop :=
  IsCompact Γ ∧ ∃ p ∈ F.domain,
    ¬ Ch11.Orbits.IsConstant F p ∧ Ch11.Orbits.HasLeastPeriod F p ∧
      Γ = Ch11.Orbits.orbit F p

/-- Existence for all nonnegative elapsed times on the actual maximal domain. -/
def IsForwardComplete (F : AutonomousODE E) (x : E) : Prop :=
  x ∈ F.domain ∧ Ici (0 : ℝ) ⊆ (flowInterval F x).carrier

/-- Orbital Lyapunov stability. The same δ controls every nearby admissible
initial point and every future real time. -/
def IsOrbitallyStable (F : AutonomousODE E) (Γ : Set E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ F.domain, Metric.infDist x Γ < δ →
      IsForwardComplete F x ∧
        ∀ t : ℝ, 0 ≤ t → Metric.infDist (flow F t x) Γ < ε

/-- Orbital asymptotic stability: stability and attraction of a neighborhood
in distance to the whole orbit. -/
def IsOrbitallyAsymptoticallyStable (F : AutonomousODE E) (Γ : Set E) : Prop :=
  IsOrbitallyStable F Γ ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ F.domain, Metric.infDist x Γ < δ →
      IsForwardComplete F x ∧
        Tendsto (fun t : ℝ => Metric.infDist (flow F t x) Γ) atTop (𝓝 0)

/-- Orbital instability is the negation of orbital Lyapunov stability. -/
def IsOrbitallyUnstable (F : AutonomousODE E) (Γ : Set E) : Prop :=
  ¬ IsOrbitallyStable F Γ

/-- Local exponential orbital stability, with positive constants common to
all nearby admissible initial states and all nonnegative elapsed times. -/
def IsLocallyExponentiallyOrbitallyStable (F : AutonomousODE E) (Γ : Set E) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ α : ℝ, 0 < α ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ F.domain, Metric.infDist x Γ < δ →
      IsForwardComplete F x ∧ ∀ t : ℝ, 0 ≤ t →
        Metric.infDist (flow F t x) Γ ≤
          C * Real.exp (-α * t) * Metric.infDist x Γ

/-- A domain test for forward completeness: all future evaluations are in the
canonical flow domain, not merely values of an ambient representative. -/
theorem forwardComplete_iff_domain :
    Specs.D13Unified.Ch14.OrbitalDefinitions.ForwardCompleteDomain.{u} := by
  intro E _ _ F x
  constructor
  · rintro ⟨hx, ht⟩ t hnonneg
    exact ⟨hx, ht hnonneg⟩
  · intro h
    exact ⟨(h 0 le_rfl).1, fun t ht => (h t ht).2⟩

end D13Unified.Ch14.OrbitalDefinitions
