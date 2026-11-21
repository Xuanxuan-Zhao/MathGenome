import MathGenome.Internal.Specs.D07.Ch08.PrincipalDivisibility
import MathGenome.Internal.Specs.D07.Ch10.Divisibility
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Polynomial.Basic

/-!
Independent statements for K07.10.associates (paper.tex:1818–1834).
The chapter assumes a commutative nontrivial domain. Mathlib's `Associated`
uses multiplication by a unit on the right, in the opposite orientation
from the source's `a = u * b`; the first statement supplies the bridge.
Principal ideals use the canonical two-sided span of the upstream chapter.
No element, including a polynomial, is required to be nonzero.
-/

universe u

namespace Specs.D07.Ch10.Associates

def AssociateCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b : R),
    Associated a b ↔ ∃ u : Rˣ, a = (u : R) * b

def AssociateEquivalence : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    Equivalence (Associated : R → R → Prop)

def AssociatesIffMutualDivisibility : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b : R),
    Associated a b ↔ a ∣ b ∧ b ∣ a

def MutualDivisibilityIffPrincipalIdeals : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b : R),
    (a ∣ b ∧ b ∣ a) ↔ TwoSidedIdeal.span {a} = TwoSidedIdeal.span {b}

def AssociatesIffPrincipalIdeals : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b : R),
    Associated a b ↔ TwoSidedIdeal.span {a} = TwoSidedIdeal.span {b}

def ZeroAssociates : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (b : R),
    Associated (0 : R) b ↔ b = 0

def IntegerAssociates : Prop :=
  ∀ a b : ℤ, Associated a b ↔ a = b ∨ a = -b

def PolynomialAssociates : Prop :=
  ∀ (F : Type u) [Field F] (f g : Polynomial F),
    Associated f g ↔ ∃ c : F, c ≠ 0 ∧ f = Polynomial.C c * g

end Specs.D07.Ch10.Associates
