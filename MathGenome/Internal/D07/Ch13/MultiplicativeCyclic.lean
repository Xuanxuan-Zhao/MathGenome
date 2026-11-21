import MathGenome.Internal.D07.Ch12.FiniteMultiplicativeCyclic
import MathGenome.Internal.D07.Ch02.FiniteCyclicSubgroupClassification
import MathGenome.Internal.Specs.D07.Ch13.MultiplicativeCyclic
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
Cyclic unit groups and their generators (paper.tex:3915–3921).

Apply the finite multiplicative-subgroup theorem to the whole unit group.
Units in a field correspond bijectively to its nonzero elements, so their
cardinality is q-1. The finite cyclic generator-count theorem then counts
exactly those units whose integer powers fill the group. Positivity of the
unit-group cardinality follows from its identity, including when q = 2.
-/

namespace D07.Ch13.MultiplicativeCyclic

universe u

theorem finite_multiplicative_subgroup_is_cyclic :
    Specs.D07.Ch13.MultiplicativeCyclic.FiniteMultiplicativeSubgroupIsCyclic.{u} :=
  D07.Ch12.FiniteMultiplicativeCyclic.finite_multiplicative_subgroup_is_cyclic

theorem finite_field_units :
    Specs.D07.Ch13.MultiplicativeCyclic.FiniteFieldUnits.{u} := by
  intro K _ _ q hq
  have htop : IsCyclic (⊤ : Subgroup Kˣ) :=
    finite_multiplicative_subgroup_is_cyclic K ⊤
  have hcyclic : IsCyclic Kˣ := Subgroup.topEquiv.isCyclic.mp htop
  have hcard : Nat.card Kˣ = q - 1 := by
    rw [Nat.card_units, hq]
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyclic
  refine ⟨hcyclic, hcard, ?_⟩
  exact D07.Ch02.FiniteCyclicSubgroupClassification.generator_count Kˣ g (q - 1)
    hg (hcard ▸ Nat.card_pos) hcard

end D07.Ch13.MultiplicativeCyclic
