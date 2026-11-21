import MathGenome.Internal.Specs.D07.Ch06.SmallOrderExamplesOrderSix
import MathGenome.Internal.Specs.D07.Ch06.SmallOrderExamplesOrderEight
import MathGenome.Internal.Specs.D07.Ch04.NormalityNotTransitive
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Sylow

/-! Independent statements for paper.tex:1078–1100.
The order-six and order-eight model types are the shared source models.
`A₄` acts on `Fin 4`, with source letters 1,…,4 represented by 0,…,3.
-/
namespace Specs.D07.Ch06.SmallOrderExamples

universe u

def OrderSixClassification : Prop :=
  SmallOrderExamplesOrderSix.Classification.{u}

def OrderSixModels : Prop := SmallOrderExamplesOrderSix.Models

def OrderEightClassification : Prop :=
  SmallOrderExamplesOrderEight.Classification.{u}

def OrderEightModels : Prop :=
  SmallOrderExamplesOrderEight.ModelCardinalities ∧
    SmallOrderExamplesOrderEight.PairwiseNonisomorphic

abbrev A4 := alternatingGroup (Fin 4)

/-- The literal double-transposition subgroup is normal, has order four and
exponent dividing two, and is the underlying subgroup of every Sylow 2-subgroup.
In particular this specifies the Klein four subgroup inside the original A₄,
and asserts uniqueness among all Sylow 2-subgroups. -/
def AlternatingFourSylowTwo : Prop :=
  ∃ V : Subgroup A4,
    (∀ g : A4, g ∈ V ↔
      (g : Equiv.Perm (Fin 4)) ∈ Ch04.NormalityNotTransitive.vCarrier) ∧
    V.Normal ∧ Nat.card V = 4 ∧ (∀ x : V, x ^ 2 = 1) ∧
    (∃ P : Sylow 2 A4, P.toSubgroup = V) ∧
    (∀ P : Sylow 2 A4, P.toSubgroup = V)

/-- The number of distinct Sylow 3-subgroups of A₄. -/
def AlternatingFourSylowThreeCount : Prop := Nat.card (Sylow 3 A4) = 4

end Specs.D07.Ch06.SmallOrderExamples
