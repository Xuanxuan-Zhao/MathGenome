import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.OmegaTopology
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Independent full statement of paper.tex, d13:11:omega. The omega-limit
set and partial flow are the shared canonical objects. Completeness and
invariance are conclusions, with no compact invariant set assumed. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D13Unified.Ch11.Omega
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters Ch11.OmegaTopology Ch11.Invariant
universe u

/-- Compact closure of a positive orbit inside the original open domain gives
all the omega-limit conclusions, including the entire two-sided maximal orbit
of each limit point and equality under every real time map. -/
def CompactOmega : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, IsCompact (closure (positiveOrbit F x)) →
    closure (positiveOrbit F x) ⊆ F.domain →
      Ici 0 ⊆ (flowInterval F x).carrier ∧
      (omegaValue F x).Nonempty ∧ IsCompact (omegaValue F x) ∧
      IsConnected (omegaValue F x) ∧ omegaValue F x ⊆ closure (positiveOrbit F x) ∧
      invariantValue F (omegaValue F x) ∧
      (∀ y ∈ omegaValue F x, (flowInterval F y).carrier = univ ∧
        ∀ t : ℝ, flow F t y ∈ omegaValue F x) ∧
      (∀ t : ℝ, (flow F t) '' omegaValue F x = omegaValue F x) ∧
      (∀ y : E, y ∈ omegaValue F x ↔ ∃ t : ℕ → ℝ,
        (∀ j, t j ∈ (flowInterval F x).carrier ∧ 0 ≤ t j) ∧
        Tendsto t atTop atTop ∧ Tendsto (fun j => flow F (t j) x) atTop (𝓝 y)) ∧
      Tendsto (fun t : ℝ => Metric.infDist (flow F t x) (omegaValue F x))
        atTop (𝓝 0)

end Specs.D13Unified.Ch11.Omega
