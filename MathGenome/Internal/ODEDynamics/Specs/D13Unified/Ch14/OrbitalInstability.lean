import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.OrbitalStability
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.Multipliers

/-! Independent statements of paper.tex, d13:14:orbital-instability.
The escape conclusion includes actual flow-domain membership and a fixed
positive distance, for arbitrarily small perturbations of the base point.
The planar test leaves the zero divergence integral unclassified. -/
noncomputable section
open Set
open scoped ContDiff

namespace Specs.D13Unified.Ch14.OrbitalInstability
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open _root_.D13Unified.Ch11.Orbits _root_.D13Unified.Ch08.MatrixPowerCriteria
open Ch01.AutonomousParameters Ch14.ReturnMap Ch14.OrbitalDefinitions Ch14.Multipliers

/-- Arbitrarily small initial perturbations reach a uniform distance at an
allowed positive elapsed time. -/
def distanceEscapeValue {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : AutonomousODE E) (p : E) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → ∃ x ∈ F.domain,
    ‖x - p‖ < δ ∧ ∃ t : ℝ, 0 < t ∧ (t,x) ∈ flowDomain F ∧
      ε ≤ Metric.infDist (flow F t x) (orbit F p)

def OrbitalInstabilityExpected : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ F : AutonomousODE E,
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, ∀ T : ℝ, 0 < T → IsComplete F p →
    Function.Periodic (fun t => flow F t p) T →
    (∀ R : ℝ, 0 < R → Function.Periodic (fun t => flow F t p) R → T ≤ R) →
    ¬ IsConstant F p → ∀ (ℓ : E →L[ℝ] ℝ) (d : FirstReturnData k F p T ℓ),
    (∃ z : ℂ, Module.End.HasEigenvalue
      (complexify (LinearMap.toMatrix (Module.finBasis ℝ ℓ.ker)
        (Module.finBasis ℝ ℓ.ker) (fderiv ℝ (d.P : ℓ.ker → ℓ.ker) 0).toLinearMap)).toLin' z ∧
        1 < ‖z‖) →
    distanceEscapeValue F p ∧ orbitalUnstableValue F (orbit F p)

/-- In real dimension two the divergence integral decides the two strict
cases, with exponential orbital attraction in the negative case. -/
def PlanarCriteriaExpected : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
    Module.finrank ℝ E = 2 → ∀ (k : ℕ), 1 ≤ k → ∀ F : AutonomousODE E,
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, ∀ T : ℝ, 0 < T → IsComplete F p →
    Function.Periodic (fun t => flow F t p) T →
    (∀ R : ℝ, 0 < R → Function.Periodic (fun t => flow F t p) R → T ≤ R) →
    ¬ IsConstant F p → ∀ (ℓ : E →L[ℝ] ℝ) (_d : FirstReturnData k F p T ℓ),
    ((∫ t in (0 : ℝ)..T, divergence F (flow F t p)) < 0 →
      exponentiallyOrbitallyStableValue F (orbit F p) ∧
        orbitalAsymptoticallyStableValue F (orbit F p)) ∧
    (0 < (∫ t in (0 : ℝ)..T, divergence F (flow F t p)) →
      distanceEscapeValue F p ∧ orbitalUnstableValue F (orbit F p))

end Specs.D13Unified.Ch14.OrbitalInstability
