import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.FareyMediants

/-! Independent specification of `paper.tex`, §Farey fractions, theorem
“Neighbors, mediants, and insertion” (lines 2303–2335). The encoding,
reduction convention, order and neighbor relation are the upstream ones. -/
namespace P203Specs.Ch05

/-- The initial Farey set retains both endpoints. -/
def FareyInitial : Prop := farey 1 = {(0, 1), (1, 1)}

/-- Consecutive members have determinant one and denominator sum exceeding
 the order, for every positive integer order. -/
def NeighborProperties : Prop :=
  ∀ N : ℤ, 1 ≤ N → ∀ x y : Fraction, orderedNeighbors N x y →
    x.2 * y.1 - x.1 * y.2 = 1 ∧ N < x.2 + y.2

/-- The mediant is the unique reduced interior fraction of least denominator. -/
def NeighborUniqueMinimum : Prop :=
  ∀ N : ℤ, 1 ≤ N → ∀ x y : Fraction, orderedNeighbors N x y →
    ∀ z : Fraction,
      (Reduced z ∧ fractionValue x < fractionValue z ∧
        fractionValue z < fractionValue y ∧
        ∀ w : Fraction, Reduced w →
          fractionValue x < fractionValue w → fractionValue w < fractionValue y →
          z.2 ≤ w.2) ↔ z = (x.1 + y.1, x.2 + y.2)

/-- In each old neighboring interval there is exactly the mediant at the next
order when the denominator sum is N+1, and there are no other insertions. -/
def IntervalInsertion : Prop :=
  ∀ N : ℤ, 1 ≤ N → ∀ x y : Fraction, orderedNeighbors N x y →
    ∀ z : Fraction,
      (z ∈ farey (N+1) ∧ fractionValue x < fractionValue z ∧
        fractionValue z < fractionValue y) ↔
      (x.2 + y.2 = N+1 ∧ z = (x.1+y.1, x.2+y.2))

/-- Completeness of the passage to the next order: every member is either
an old member or the specified mediant in an old neighboring interval. -/
def FareyInsertion : Prop :=
  ∀ N : ℤ, 1 ≤ N → ∀ z : Fraction,
    z ∈ farey (N+1) ↔ z ∈ farey N ∨
      ∃ x y : Fraction, orderedNeighbors N x y ∧
        x.2 + y.2 = N+1 ∧ z = (x.1+y.1, x.2+y.2)

end P203Specs.Ch05
