import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Orbits
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Independent specification for the all-nearby entry stage in the proof of
paper.tex, d13:14:orbital-stability, lines 3117–3128. -/
noncomputable section
open Set
open scoped ContDiff

namespace Specs.D13Unified.Ch14.NearbySectionEntry
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open _root_.D13Unified.Ch11.Orbits
open Ch01.AutonomousParameters
universe u

/-- The entry time is strictly positive, has a uniform upper bound, and all
pre-entry flow evaluations are in the actual maximal domain. The prescribed
section neighborhood is specified in its canonical affine coordinates. -/
def EntryBounds {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : AutonomousODE E) (p : E) (ℓ : E →L[ℝ] ℝ) (S : Set ℓ.ker)
    (δ A L₁ L₂ : ℝ) : Prop :=
  ∀ x : E, Metric.infDist x (orbit F p) < δ →
    x ∈ F.domain ∧ ∃ t : ℝ, 0 < t ∧ t ≤ A ∧
      (∀ s ∈ Icc 0 t, (s,x) ∈ flowDomain F) ∧
      (∃ v ∈ S, flow F t x = p + (v : E)) ∧
      ‖flow F t x - p‖ ≤ L₁ * Metric.infDist x (orbit F p) ∧
      ∀ s ∈ Icc 0 t,
        Metric.infDist (flow F s x) (orbit F p) ≤ L₂ * Metric.infDist x (orbit F p)

/-- A positive period, completeness and a transverse section suffice; leastness
of the period is unnecessary. In particular this covers the original least
period of every nonconstant periodic orbit. No phase map is an input. -/
def NearbySectionEntryExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, ∀ T : ℝ, 0 < T → IsComplete F p →
      Function.Periodic (fun t => flow F t p) T →
    ∀ ℓ : E →L[ℝ] ℝ, ℓ (autonomousEvalValue F p) ≠ 0 →
    ∀ S : Set ℓ.ker, IsOpen S → (0 : ℓ.ker) ∈ S →
      ∃ δ A L₁ L₂ : ℝ, 0 < δ ∧ 0 < A ∧ 0 < L₁ ∧ 0 < L₂ ∧
        EntryBounds F p ℓ S δ A L₁ L₂

end Specs.D13Unified.Ch14.NearbySectionEntry
