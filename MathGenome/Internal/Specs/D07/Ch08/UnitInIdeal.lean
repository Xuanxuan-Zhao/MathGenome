import MathGenome.Internal.Specs.D07.Ch08.PrincipalDivisibility
import MathGenome.Internal.Specs.D07.Ch08.Units

/-!
Independent statements for K07.08.unit_in_ideal (paper.tex:1393–1405).
`Ideal R` is a left ideal, so the first three statements require neither
commutativity nor two-sidedness. The principal ideal in the last statement
uses the canonical two-sided span from PrincipalDivisibility. All statements
allow the zero ring.
-/

universe u

namespace Specs.D07.Ch08.UnitInIdeal

def LeftIdealTopIffOne : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R),
    I = ⊤ ↔ (1 : R) ∈ I

def LeftIdealOneIffContainsUnit : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R),
    (1 : R) ∈ I ↔ ∃ a : R, a ∈ I ∧ IsUnit a

def LeftIdealTopIffContainsUnit : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R),
    I = ⊤ ↔ ∃ a : R, a ∈ I ∧ IsUnit a

def PrincipalIdealTopIffIsUnit : Prop :=
  ∀ (R : Type u) [CommRing R] (a : R),
    TwoSidedIdeal.span {a} = ⊤ ↔ IsUnit a

end Specs.D07.Ch08.UnitInIdeal
