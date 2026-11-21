import MathGenome.Internal.Specs.D07.Ch01.SubgroupDefinitionTest
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Basic.ExistsUnique
import Mathlib.Basic.Finite.Defs
import Mathlib.Algebra.Group.Equiv.Defs

/-!
Independent specification of `K07.02.subgroups_of_integer_group`
(paper.tex:453–459, chapters/M07.02.tex:31–37).

The subgroup is an arbitrary additive subgroup of ℤ. Nonnegativity belongs
inside the uniqueness predicate. `zmultiples d` has precisely the carrier
`{d * k | k : ℤ}`, as the first assertion records. The positive case includes
infinitude, cyclicity, and the explicit additive isomorphism used in the paper.
-/

namespace Specs.D07.Ch02.SubgroupsOfIntegerGroup

/-- The canonical generated subgroup is the source's set of integer multiples. -/
def MultiplesCarrier : Prop :=
  ∀ d : ℤ, (AddSubgroup.zmultiples d : Set ℤ) = {a : ℤ | ∃ k : ℤ, a = d * k}

/-- Every subgroup has exactly one nonnegative integer generator. -/
def IntegerSubgroupClassification : Prop :=
  ∀ H : AddSubgroup ℤ, ∃! d : ℤ, 0 ≤ d ∧ H = AddSubgroup.zmultiples d

/-- For a positive generator, the subgroup is infinite cyclic, and the
isomorphism from ℤ is exactly multiplication by that generator. -/
def PositiveInfiniteCyclic : Prop :=
  ∀ (H : AddSubgroup ℤ) (d : ℤ), H = AddSubgroup.zmultiples d → 0 < d →
    Infinite H ∧ IsAddCyclic H ∧
      ∃ e : ℤ ≃+ H, ∀ k : ℤ, (e k : ℤ) = d * k

/-- Zero multiples form the zero subgroup, whose carrier is the singleton zero. -/
def ZeroMultiples : Prop :=
  AddSubgroup.zmultiples (0 : ℤ) = ⊥ ∧
    (AddSubgroup.zmultiples (0 : ℤ) : Set ℤ) = {0}

end Specs.D07.Ch02.SubgroupsOfIntegerGroup
