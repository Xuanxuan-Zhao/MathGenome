import MathGenome.Internal.Specs.D07.Ch10.IrreducibleNonprime
import MathGenome.Internal.Specs.D07.Ch10.UfdDefinition

/-! Independent statements for K07.10.nonufd_domain (paper.tex:2043–2056).
We use the same quadratic ring as the earlier example; its injective complex
realization and norm are supplied by that example's interface. The two finite
multisets retain multiplicities, and `Multiset.Rel Associated` permits reordering
and replacement of factors by associates. -/

namespace Specs.D07.Ch10.NonufdDomain

open IrreducibleNonprime (R)

def NormTwoImpossible : Prop := ∀ a b : ℤ, a ^ 2 + 5 * b ^ 2 ≠ 2

def WitnessIdentity : Prop :=
  (6 : R) = 2 * 3 ∧
  (6 : R) = (1 + Zsqrtd.sqrtd) * (1 - Zsqrtd.sqrtd)

def WitnessNorms : Prop :=
  Zsqrtd.norm (2 : R) = 4 ∧ Zsqrtd.norm (3 : R) = 9 ∧
  Zsqrtd.norm (1 + Zsqrtd.sqrtd : R) = 6 ∧
  Zsqrtd.norm (1 - Zsqrtd.sqrtd : R) = 6

def WitnessIrreducible : Prop :=
  Irreducible (2 : R) ∧ Irreducible (3 : R) ∧
  Irreducible (1 + Zsqrtd.sqrtd : R) ∧
  Irreducible (1 - Zsqrtd.sqrtd : R)

def Units : Prop := ∀ z : R, IsUnit z ↔ z = 1 ∨ z = -1

/-- Every element with nonzero square-root coordinate fails to be associate
to an integer. In particular this covers all four cross-pairs in the example. -/
def IntegerNotAssociated : Prop :=
  ∀ (n : ℤ) (z : R), z.im ≠ 0 → ¬Associated (n : R) z

def CrossNonassociated : Prop :=
  ¬Associated (2 : R) (1 + Zsqrtd.sqrtd) ∧
  ¬Associated (2 : R) (1 - Zsqrtd.sqrtd) ∧
  ¬Associated (3 : R) (1 + Zsqrtd.sqrtd) ∧
  ¬Associated (3 : R) (1 - Zsqrtd.sqrtd)

def DistinctIrreducibleFactorizations : Prop :=
  (∀ p ∈ ({2, 3} : Multiset R), Irreducible p) ∧
  (∀ p ∈ ({1 + Zsqrtd.sqrtd, 1 - Zsqrtd.sqrtd} : Multiset R), Irreducible p) ∧
  ({2, 3} : Multiset R).prod = 6 ∧
  ({1 + Zsqrtd.sqrtd, 1 - Zsqrtd.sqrtd} : Multiset R).prod = 6 ∧
  ¬Multiset.Rel Associated ({2, 3} : Multiset R)
    ({1 + Zsqrtd.sqrtd, 1 - Zsqrtd.sqrtd} : Multiset R)

def DomainNotUfd : Prop := IsDomain R ∧ ¬UniqueFactorizationMonoid R

end Specs.D07.Ch10.NonufdDomain
