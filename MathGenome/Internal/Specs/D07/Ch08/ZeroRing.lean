import MathGenome.Internal.Specs.D07.Ch08.RingDefinition
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Group.Units.Defs

/-!
Independent specifications for K07.08.zero_ring, paper.tex:1179–1190.
`Ring` retains the source's associative, unital, possibly noncommutative
convention. A ring is inhabited by zero, so `Subsingleton R` says that it
has exactly one element; the second characterization also states this
with an explicit unique-existence quantifier.

`IsDomain` includes nontriviality (and, together with `CommRing`, expresses
an integral domain). `IsField` includes nontriviality, commutativity and
inverses. Excluding these predicates for every subsingleton ring therefore
includes the source's exclusions of integral domains and fields.
The later construction of the quotient R/R belongs to K07.09.quotient_trivial.
-/

universe u

namespace Specs.D07.Ch08.ZeroRing

def ZeroEqOneIffSubsingleton : Prop :=
  ∀ (R : Type u) [Ring R], (0 : R) = 1 ↔ Subsingleton R

def ZeroEqOneIffUniqueElement : Prop :=
  ∀ (R : Type u) [Ring R], (0 : R) = 1 ↔ ∃! _ : R, True

/-- The one-element ring is permitted, even among commutative rings. -/
def OneElementRingExists : Prop :=
  ∃ (R : Type u) (_ : CommRing R), ∃! _ : R, True

def NotDomain : Prop :=
  ∀ (R : Type u) [Ring R] [Subsingleton R], ¬ IsDomain R

def NotField : Prop :=
  ∀ (R : Type u) [Ring R] [Subsingleton R], ¬ IsField R

/-- Zero is its own multiplicative inverse, and the unique element is a unit. -/
def UnitsOfOneElementRing : Prop :=
  ∀ (R : Type u) [Ring R] [Subsingleton R],
    (0 : R) * 0 = 1 ∧ ∀ a : R, IsUnit a

end Specs.D07.Ch08.ZeroRing
