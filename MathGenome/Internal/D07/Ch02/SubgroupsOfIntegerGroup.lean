import MathGenome.Internal.D07.Ch01.SubgroupDefinitionTest
import MathGenome.Internal.Specs.D07.Ch02.SubgroupsOfIntegerGroup
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
# Subgroups of the additive group of integers

`K07.02.subgroups_of_integer_group` (paper.tex:453–459).
Mathlib's subgroup-of-cyclic theorem supplies an integer generator. Taking
its absolute value makes it nonnegative; mutual divisibility proves uniqueness.
For a positive generator, the torsion-free generated-subgroup equivalence
provides the explicit isomorphism k ↦ d*k.
-/

namespace D07.Ch02.SubgroupsOfIntegerGroup

theorem multiples_carrier (d : ℤ) :
    (AddSubgroup.zmultiples d : Set ℤ) = {a : ℤ | ∃ k : ℤ, a = d * k} := by
  ext a
  change a ∈ AddSubgroup.zmultiples d ↔ ∃ k : ℤ, a = d * k
  exact Int.mem_zmultiples_iff.trans dvd_def

theorem integer_subgroup_classification (H : AddSubgroup ℤ) :
    ∃! d : ℤ, 0 ≤ d ∧ H = AddSubgroup.zmultiples d := by
  obtain ⟨a, ha⟩ := H.isAddCyclic_iff_exists_zmultiples_eq_top.mp H.isAddCyclic
  refine ⟨(a.natAbs : ℤ), ⟨Int.natCast_nonneg _, ?_⟩, ?_⟩
  · exact ha.symm.trans (Int.zmultiples_natAbs a).symm
  · intro d hd
    have heq : AddSubgroup.zmultiples d = AddSubgroup.zmultiples (a.natAbs : ℤ) :=
      hd.2.symm.trans (ha.symm.trans (Int.zmultiples_natAbs a).symm)
    exact Int.dvd_antisymm hd.1 (Int.natCast_nonneg _)
      (Int.zmultiples_le_zmultiples_iff.mp heq.ge)
      (Int.zmultiples_le_zmultiples_iff.mp heq.le)

theorem positive_infinite_cyclic (H : AddSubgroup ℤ) (d : ℤ)
    (hH : H = AddSubgroup.zmultiples d) (hd : 0 < d) :
    Infinite H ∧ IsAddCyclic H ∧
      ∃ e : ℤ ≃+ H, ∀ k : ℤ, (e k : ℤ) = d * k := by
  subst H
  let e : ℤ ≃+ AddSubgroup.zmultiples d :=
    (AddSubgroup.zmultiplesEquivInt (ne_of_gt hd)).symm
  refine ⟨Infinite.of_injective e e.injective, inferInstance, e, ?_⟩
  intro k
  simp [e, mul_comm]

theorem zero_multiples :
    AddSubgroup.zmultiples (0 : ℤ) = ⊥ ∧
      (AddSubgroup.zmultiples (0 : ℤ) : Set ℤ) = {0} := by
  constructor
  · exact AddSubgroup.zmultiples_zero_eq_bot
  · ext a
    simp

end D07.Ch02.SubgroupsOfIntegerGroup
