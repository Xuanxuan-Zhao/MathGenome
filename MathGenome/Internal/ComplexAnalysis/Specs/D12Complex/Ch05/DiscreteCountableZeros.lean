import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.DiscreteSubset

/-!
Independent statements for paper.tex:1323–1338, `d12:05-03-discrete`.
The zero set is restricted to the stated open set. Nonvanishing somewhere
in the domain (or in the selected component) is an explicit hypothesis.
Compact sets must be contained in that domain or component; accumulation
at its boundary is allowed.
-/

open Set

namespace Specs.D12Complex.Ch05.DiscreteCountableZeros
open _root_.D12Complex

/-- Every zero has an isolating disk contained in the domain. -/
def zeros_isolated_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → HolomorphicOn Ω f →
    ¬ EqOn f (fun _ => 0) Ω →
    ∀ a ∈ Ω, f a = 0 → ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ Ω ∧
      ∀ z ∈ Metric.ball a r, f z = 0 → z = a

/-- Discreteness uses the subspace topology on the actual zero set. -/
def zeroSet_isDiscrete_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → HolomorphicOn Ω f →
    ¬ EqOn f (fun _ => 0) Ω → IsDiscrete {z | z ∈ Ω ∧ f z = 0}

def zeros_finite_on_compact_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → HolomorphicOn Ω f →
    ¬ EqOn f (fun _ => 0) Ω →
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → {z | z ∈ K ∧ f z = 0}.Finite

def zeros_countable_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → HolomorphicOn Ω f →
    ¬ EqOn f (fun _ => 0) Ω → {z | z ∈ Ω ∧ f z = 0}.Countable

/-- On an arbitrary open set, each component on which the function is
not identically zero has all the preceding properties. No condition is
imposed on any other component. -/
def zeros_componentwise_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f → ∀ a ∈ Ω,
    ¬ EqOn f (fun _ => 0) (connectedComponentIn Ω a) →
    (∀ b ∈ connectedComponentIn Ω a, f b = 0 →
      ∃ r : ℝ, 0 < r ∧ Metric.ball b r ⊆ connectedComponentIn Ω a ∧
        ∀ z ∈ Metric.ball b r, f z = 0 → z = b) ∧
    IsDiscrete {z | z ∈ connectedComponentIn Ω a ∧ f z = 0} ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ connectedComponentIn Ω a →
      {z | z ∈ K ∧ f z = 0}.Finite) ∧
    {z | z ∈ connectedComponentIn Ω a ∧ f z = 0}.Countable

end Specs.D12Complex.Ch05.DiscreteCountableZeros
