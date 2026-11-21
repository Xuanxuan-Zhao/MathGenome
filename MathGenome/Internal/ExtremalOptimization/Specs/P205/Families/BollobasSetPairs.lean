import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace Specs.P205

/-- Bollobás's inequality for a finite indexed collection of finite set pairs.
The ambient and index types need not be finite. -/
def BollobasSetPairs : Prop :=
  ∀ {α ι : Type*} [DecidableEq α] (I : Finset ι) (A B : ι → Finset α),
    (∀ i ∈ I, Disjoint (A i) (B i)) →
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → ((A i) ∩ (B j)).Nonempty) →
    (∑ i ∈ I, ((Nat.choose ((A i).card + (B i).card) (A i).card : ℝ)⁻¹)) ≤ 1

end Specs.P205
