import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.ReturnMap
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.MatrixPowerCriteria
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Independent statement of the section stage in d13:14:orbital-stability.
The section coordinates are the actual affine chart v ↦ p+v from ReturnMap.
In particular zero in ker ℓ corresponds to p, not to the ambient origin. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch14.SectionDecay
open Ch06.StateDerivative
open Specs.D13Unified.Ch14.ReturnMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Time of the j-th return, with the zeroth return at time zero. -/
def cumulativeTime {k : ℕ} {F : AutonomousODE E} {p : E} {T : ℝ}
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ) (v : ℓ.ker) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, d.τ ((d.P : ℓ.ker → ℓ.ker)^[i] v)

end D13Unified.Ch14.SectionDecay

namespace Specs.D13Unified.Ch14.SectionDecay
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open _root_.D13Unified.Ch14.SectionDecay
open _root_.D13Unified.Ch08.MatrixPowerCriteria
open Ch14.ReturnMap
open Ch01.AutonomousParameters
universe u

/-- Complete original obligation. The complex spectrum is taken after writing
the real section derivative in a basis; it includes all transverse eigenvalues.
All flow assertions use the canonical maximal interval. The constants and
compact neighborhood are chosen before the initial point. -/
def SectionDecayExpected : Prop :=
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
    ∃ U : Set ℓ.ker, IsOpen U ∧ (0 : ℓ.ker) ∈ U ∧ U ⊆ d.P.source ∧
      MapsTo d.P U U ∧
      ∃ C θ C' α : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ 0 < C' ∧ 0 < α ∧
      ∃ K : Set E, IsCompact K ∧
        _root_.D13Unified.Ch11.Orbits.orbit F p ⊆ interior K ∧ K ⊆ F.domain ∧
      ∀ v ∈ U,
        (∀ j : ℕ, (d.P : ℓ.ker → ℓ.ker)^[j] v ∈ U ∧
          ‖(d.P : ℓ.ker → ℓ.ker)^[j] v‖ ≤ C * θ ^ j * ‖v‖) ∧
        Tendsto (fun j => (d.P : ℓ.ker → ℓ.ker)^[j] v) atTop (𝓝 0) ∧
        (∀ w ∈ U, T / 2 < d.τ w ∧ d.τ w < 3 * T / 2) ∧
        (∀ j : ℕ, (j : ℝ) * (T / 2) ≤ cumulativeTime d v j ∧
          cumulativeTime d v j ≤ (j : ℝ) * (3 * T / 2)) ∧
        Tendsto (cumulativeTime d v) atTop atTop ∧
        (∀ j : ℕ, ∀ s ∈ Icc 0 (d.τ ((d.P : ℓ.ker → ℓ.ker)^[j] v)),
          (cumulativeTime d v j + s, p + (v : E)) ∈ flowDomain F ∧
          flow F (cumulativeTime d v j + s) (p + (v : E)) =
            flow F s (p + ((d.P : ℓ.ker → ℓ.ker)^[j] v : E))) ∧
        (∀ t : ℝ, 0 ≤ t → (t, p + (v : E)) ∈ flowDomain F ∧
          flow F t (p + (v : E)) ∈ K ∧
          Metric.infDist (flow F t (p + (v : E))) (_root_.D13Unified.Ch11.Orbits.orbit F p) ≤
            C' * Real.exp (-α * t) * ‖v‖)

end Specs.D13Unified.Ch14.SectionDecay
