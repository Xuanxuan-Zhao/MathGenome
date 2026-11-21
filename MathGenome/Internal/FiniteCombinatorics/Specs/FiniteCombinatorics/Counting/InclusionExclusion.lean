import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Independent statements for finite inclusion–exclusion (paper.tex, Theorem p204:W02).
The ambient and index types need not be finite: the finite index set and its
finite constituent sets are represented by `Finset`s. The subtype in the sum
consists exactly of the nonempty subsets of `I`. Its membership proof supplies
the nonemptiness needed for `inf'`, so no empty intersection is taken.
-/

open scoped BigOperators

namespace Specs.FiniteCombinatorics.Counting

/-- The integer identity, including `I = ∅`. -/
def inclusionExclusionInteger : Prop :=
  ∀ (ι α : Type*) [DecidableEq α] (I : Finset ι) (A : ι → Finset α),
    ((I.biUnion A).card : ℤ) =
      ∑ J : I.powerset.filter (·.Nonempty),
        (-1 : ℤ) ^ (J.val.card + 1) *
          ((J.val.inf' (Finset.mem_filter.mp J.property).2 A).card : ℤ)

/-- The same counting identity after mapping integer coefficients into a ring. -/
def inclusionExclusionRing : Prop :=
  ∀ (ι α R : Type*) [DecidableEq α] [Ring R] (I : Finset ι) (A : ι → Finset α),
    ((I.biUnion A).card : R) =
      ∑ J : I.powerset.filter (·.Nonempty),
        (-1 : R) ^ (J.val.card + 1) *
          ((J.val.inf' (Finset.mem_filter.mp J.property).2 A).card : R)

end Specs.FiniteCombinatorics.Counting
