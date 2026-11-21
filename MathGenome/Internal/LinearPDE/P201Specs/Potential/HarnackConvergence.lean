import MathGenome.Internal.LinearPDE.P201Specs.Potential.Harnack
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! The full Harnack corollary, paper.tex:900–949. Sequence members may
have either sign. Monotonicity and boundedness concern values in the domain.
Uniform convergence is asserted separately on every compact subset. -/
noncomputable section
open Set Filter
open scoped Topology

namespace P201Specs.HarnackConvergence

/-- Boundedness above at any one point selects the finite harmonic limit. -/
def BoundedConvergenceStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n), IsConnected (Ω : Set (Space n)) →
    ∀ (u : ℕ → Space n → ℝ), (∀ j, MeanValues.IsHarmonic Ω (u j)) →
    (∀ x ∈ Ω, Monotone (fun j => u j x)) →
    ∀ a₀ ∈ Ω, BddAbove (range (fun j => u j a₀)) →
    ∃ f : Space n → ℝ, MeanValues.IsHarmonic Ω f ∧
      ∀ K : Set (Space n), IsCompact K → K ⊆ (Ω : Set _) →
        TendstoUniformlyOn u f atTop K

/-- The increasing harmonic sequence either diverges everywhere to positive
infinity or converges on every compact subset to a harmonic function. -/
def MonotoneAlternativeStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n), IsConnected (Ω : Set (Space n)) →
    ∀ (u : ℕ → Space n → ℝ), (∀ j, MeanValues.IsHarmonic Ω (u j)) →
    (∀ x ∈ Ω, Monotone (fun j => u j x)) →
    (∀ x ∈ Ω, Tendsto (fun j => u j x) atTop atTop) ∨
      ∃ f : Space n → ℝ, MeanValues.IsHarmonic Ω f ∧
        ∀ K : Set (Space n), IsCompact K → K ⊆ (Ω : Set _) →
          TendstoUniformlyOn u f atTop K

end P201Specs.HarnackConvergence
