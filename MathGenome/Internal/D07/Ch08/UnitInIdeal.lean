import MathGenome.Internal.Specs.D07.Ch08.UnitInIdeal
import MathGenome.Internal.D07.Ch08.PrincipalDivisibility
import MathGenome.Internal.D07.Ch08.Units

/-! Ideals containing units, with no nontriviality hypothesis. -/

universe u

namespace D07.Ch08.UnitInIdeal

open Specs.D07.Ch08.UnitInIdeal

theorem leftIdealTopIffOne : LeftIdealTopIffOne.{u} := by
  intro R _ I
  exact I.eq_top_iff_one

theorem leftIdealOneIffContainsUnit : LeftIdealOneIffContainsUnit.{u} := by
  intro R _ I
  constructor
  · intro h
    exact ⟨1, h, isUnit_one⟩
  · rintro ⟨a, ha, hu⟩
    obtain ⟨b, _, hba⟩ := (D07.Ch08.Units.unitCharacterization R a).mp hu
    simpa only [hba] using I.mul_mem_left b ha

theorem leftIdealTopIffContainsUnit : LeftIdealTopIffContainsUnit.{u} := by
  intro R _ I
  exact (leftIdealTopIffOne R I).trans (leftIdealOneIffContainsUnit R I)

theorem principalIdealTopIffIsUnit : PrincipalIdealTopIffIsUnit.{u} := by
  intro R _ a
  constructor
  · intro h
    have h1 : (1 : R) ∈ TwoSidedIdeal.span {a} := by
      rw [h]
      exact TwoSidedIdeal.mem_top R
    obtain ⟨r, hr⟩ :=
      (D07.Ch08.PrincipalDivisibility.principalIdealFormula R a 1).mp h1
    apply (D07.Ch08.Units.unitCharacterization R a).mpr
    exact ⟨r, (mul_comm a r).trans hr.symm, hr.symm⟩
  · intro ha
    apply (TwoSidedIdeal.orderIsoIdeal (R := R)).injective
    change (TwoSidedIdeal.span {a}).asIdeal = (⊤ : TwoSidedIdeal R).asIdeal
    rw [TwoSidedIdeal.top_asIdeal]
    apply (leftIdealTopIffContainsUnit R _).mpr
    exact ⟨a, TwoSidedIdeal.subset_span (Set.mem_singleton a), ha⟩

end D07.Ch08.UnitInIdeal
