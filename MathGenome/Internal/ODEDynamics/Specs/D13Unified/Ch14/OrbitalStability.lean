import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.OrbitalDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.SectionDecay

/-! Independent original statement of paper.tex, Theorem d13:14:orbital-stability.
The affine section, derivative and spectrum are the shared first-return objects.
The conclusion uses distance to the entire canonical orbit, with actual maximal
forward existence, uniformly for every sufficiently close admissible state.
There are no section-entry assumptions in this original specification. -/
noncomputable section
open Set
open scoped ContDiff

namespace Specs.D13Unified.Ch14.OrbitalStability
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open _root_.D13Unified.Ch08.MatrixPowerCriteria
open Ch01.AutonomousParameters Ch14.ReturnMap Ch14.OrbitalDefinitions
universe u

/-- Transverse contraction implies the full real-time exponential bound and
orbital asymptotic stability, including points lying on the periodic orbit. -/
def OrbitalStabilityExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ F : AutonomousODE E,
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, ∀ T : ℝ, 0 < T →
    _root_.D13Unified.Ch11.Orbits.IsComplete F p →
    Function.Periodic (fun t => flow F t p) T →
    (∀ R : ℝ, 0 < R → Function.Periodic (fun t => flow F t p) R → T ≤ R) →
    ¬ _root_.D13Unified.Ch11.Orbits.IsConstant F p →
    ∀ (ℓ : E →L[ℝ] ℝ) (d : FirstReturnData k F p T ℓ),
    StrictSpectrum (complexify (LinearMap.toMatrix (Module.finBasis ℝ ℓ.ker)
      (Module.finBasis ℝ ℓ.ker) (fderiv ℝ (d.P : ℓ.ker → ℓ.ker) 0).toLinearMap)) →
      exponentiallyOrbitallyStableValue F (_root_.D13Unified.Ch11.Orbits.orbit F p) ∧
      orbitalAsymptoticallyStableValue F (_root_.D13Unified.Ch11.Orbits.orbit F p)

end Specs.D13Unified.Ch14.OrbitalStability
