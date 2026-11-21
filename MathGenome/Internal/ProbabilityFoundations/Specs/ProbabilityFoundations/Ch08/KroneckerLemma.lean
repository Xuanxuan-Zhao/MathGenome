import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Filter
open scoped Topology BigOperators

namespace ProbabilityFoundations.Ch08.Specs

/-- Kronecker's lemma for sequences indexed by the positive integers.
`range n` with the shift `k + 1` is the ordered sum from 1 through n.
No condition is imposed on the unused zeroth entries. -/
def KroneckerLemma : Prop :=
  ∀ (a b : ℕ → ℝ),
    (∀ n, 1 ≤ n → 0 < b n) →
    MonotoneOn b (Set.Ici 1) →
    Tendsto b atTop atTop →
    (∃ c : ℝ, Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n, a (k + 1) / b (k + 1))
      atTop (𝓝 c)) →
    Tendsto (fun n : ℕ ↦ (b n)⁻¹ * ∑ k ∈ Finset.range n, a (k + 1)) atTop (𝓝 0)

end ProbabilityFoundations.Ch08.Specs
