import MathGenome.Internal.Specs.D07.Ch08.IdealDefinition
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Order.Preorder.Chain

/-!
Independent specification of K07.08.ideal_sum_intersection,
paper.tex:1357–1366. `Ideal R` is a left ideal; every construction below
explicitly retains right absorption. All general assertions allow
noncommutative rings and the zero ring. The lattice operations refer to
inclusion of the underlying subsets, and the sum has its explicit
set-theoretic description.
-/

universe u

namespace Specs.D07.Ch08.IdealSumIntersection

/-- Every set-indexed intersection is two-sided and is the greatest lower
bound. The displayed membership formula identifies the actual intersection. -/
def ArbitraryIntersections : Prop :=
  ∀ (R : Type u) [Ring R] (S : Set (Ideal R)),
    (∀ I ∈ S, I.IsTwoSided) →
      (sInf S).IsTwoSided ∧
      (∀ x : R, x ∈ sInf S ↔ ∀ I ∈ S, x ∈ I) ∧
      (∀ K : Ideal R, K ≤ sInf S ↔ ∀ I ∈ S, K ≤ I)

/-- The empty intersection is the full ambient ring, including in the zero ring. -/
def EmptyIntersection : Prop :=
  ∀ (R : Type u) [Ring R],
    sInf (∅ : Set (Ideal R)) = ⊤ ∧
      (↑(sInf (∅ : Set (Ideal R))) : Set R) = Set.univ

/-- Binary intersection gives the meet within the two-sided ideals. -/
def BinaryIntersection : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R),
    I.IsTwoSided → J.IsTwoSided →
      (I ⊓ J).IsTwoSided ∧
      (∀ x : R, x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J) ∧
      (∀ K : Ideal R, K ≤ I ⊓ J ↔ K ≤ I ∧ K ≤ J)

/-- The sums i+j form a two-sided ideal, represented by the canonical join. -/
def SumDescription : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R),
    I.IsTwoSided → J.IsTwoSided →
      (I ⊔ J).IsTwoSided ∧
      (∀ x : R, x ∈ I ⊔ J ↔ ∃ i ∈ I, ∃ j ∈ J, i + j = x)

/-- The sum contains both summands and is their least upper bound. -/
def SumLeastUpperBound : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R),
    I.IsTwoSided → J.IsTwoSided →
      I ≤ I ⊔ J ∧ J ≤ I ⊔ J ∧
      (∀ K : Ideal R, I ⊔ J ≤ K ↔ I ≤ K ∧ J ≤ K)

/-- The specific failure of closure under addition for (2) ∪ (3) in ℤ. -/
def UnionCounterexample : Prop :=
  let I : Ideal ℤ := Ideal.span {2}
  let J : Ideal ℤ := Ideal.span {3}
  (2 : ℤ) ∈ (↑I : Set ℤ) ∪ ↑J ∧
  (3 : ℤ) ∈ (↑I : Set ℤ) ∪ ↑J ∧
  (5 : ℤ) ∉ (↑I : Set ℤ) ∪ ↑J ∧
  ¬ ∃ K : Ideal ℤ, (↑K : Set ℤ) = (↑I : Set ℤ) ∪ ↑J

/-- A nonempty chain union is a two-sided ideal. Its exact underlying set
is the union of the members, and it is their least upper bound. -/
def ChainUnion : Prop :=
  ∀ (R : Type u) [Ring R] (S : Set (Ideal R)),
    S.Nonempty → IsChain (· ≤ ·) S → (∀ I ∈ S, I.IsTwoSided) →
      ∃ U : Ideal R, U.IsTwoSided ∧
        (↑U : Set R) = ⋃₀ ((fun I : Ideal R => (↑I : Set R)) '' S) ∧
        (∀ K : Ideal R, U ≤ K ↔ ∀ I ∈ S, I ≤ K)

end Specs.D07.Ch08.IdealSumIntersection
