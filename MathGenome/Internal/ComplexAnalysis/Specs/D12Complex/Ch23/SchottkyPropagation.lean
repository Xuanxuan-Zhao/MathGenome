import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
Schottky propagation for the bounded-center subfamily in the proof of
paper.tex:4247–4262 (D12.23.04). Functions are total representatives, with
holomorphy and the two omitted values required only on the given domain.
The same bound works simultaneously for every function in this family.
-/

namespace Specs.D12Complex.Ch23.SchottkyPropagation
open _root_.D12Complex Metric

/-- Uniform bounds on a closed disk about each point, inside the domain. -/
def local_bound_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ), IsDomain Ω → a ∈ Ω →
    ∀ b ∈ Ω, ∃ r : ℝ, 0 < r ∧ closedBall b r ⊆ Ω ∧
      ∃ M : ℝ, 0 < M ∧ ∀ f : ℂ → ℂ,
        HolomorphicOn Ω f →
        (∀ z ∈ Ω, f z ≠ 0) → (∀ z ∈ Ω, f z ≠ 1) →
        ‖f a‖ ≤ 1 → ∀ z ∈ closedBall b r, ‖f z‖ ≤ M

/-- A finite real bound on each compact subset, uniform over the whole family. -/
def compact_bound_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ), IsDomain Ω → a ∈ Ω →
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ M : ℝ, 0 < M ∧ ∀ f : ℂ → ℂ,
        HolomorphicOn Ω f →
        (∀ z ∈ Ω, f z ≠ 0) → (∀ z ∈ Ω, f z ≠ 1) →
        ‖f a‖ ≤ 1 → ∀ z ∈ K, ‖f z‖ ≤ M

end Specs.D12Complex.Ch23.SchottkyPropagation
