import MathGenome.Internal.Specs.D07.Ch08.DomainField
import MathGenome.Internal.D07.Ch08.RingDefinition
import MathGenome.Internal.D07.Ch08.Units
import MathGenome.Internal.D07.Ch08.DomainFieldQuaternionDivisionExample

/-! Domains, division rings, and fields (K07.08.domain_field).
The existential structure characterizations keep the original operations;
the noncommutative example is the upstream real quaternion algebra.
-/

universe u

namespace D07.Ch08.DomainField

open Specs.D07.Ch08.DomainField

theorem divisionRingCharacterization : DivisionRingCharacterization.{u} := by
  intro R s
  constructor
  · rintro ⟨h01, hunit⟩
    let : Nontrivial R := ⟨⟨0, 1, h01⟩⟩
    classical
    exact ⟨DivisionRing.ofIsUnitOrEqZero (fun a =>
      if ha : a = 0 then Or.inr ha else Or.inl (hunit a ha)), rfl⟩
  · rintro ⟨d, rfl⟩
    let := d
    exact ⟨zero_ne_one, fun a ha => isUnit_iff_ne_zero.mpr ha⟩

theorem fieldCharacterization : FieldCharacterization.{u} := by
  intro R s
  constructor
  · rintro ⟨h01, hunit, hcomm⟩
    obtain ⟨d, hd⟩ := (divisionRingCharacterization R s).mp ⟨h01, hunit⟩
    subst s
    exact ⟨{ d with mul_comm := hcomm }, rfl⟩
  · rintro ⟨f, rfl⟩
    let := f
    exact ⟨zero_ne_one, fun a ha => isUnit_iff_ne_zero.mpr ha, mul_comm⟩

theorem commutativeDivisionRingCharacterization :
    CommutativeDivisionRingCharacterization.{u} := by
  intro R d
  constructor
  · intro hcomm
    exact ⟨{ d with mul_comm := hcomm }, rfl⟩
  · rintro ⟨f, rfl⟩
    let := f
    exact mul_comm

theorem integralDomainCharacterization : IntegralDomainCharacterization.{u} := by
  intro R _
  constructor
  · intro h
    let := h
    exact ⟨zero_ne_one, fun _ _ hab => eq_zero_or_eq_zero_of_mul_eq_zero hab⟩
  · rintro ⟨h01, hzero⟩
    let : Nontrivial R := ⟨⟨0, 1, h01⟩⟩
    let : NoZeroDivisors R := ⟨hzero _ _⟩
    exact NoZeroDivisors.to_isDomain R

theorem divisionRingLeftZeroProduct : DivisionRingLeftZeroProduct.{u} := by
  intro R _ a b ha hab
  calc
    b = 1 * b := (one_mul b).symm
    _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel₀ ha]
    _ = a⁻¹ * (a * b) := mul_assoc _ _ _
    _ = 0 := by rw [hab, mul_zero]

theorem fieldIsDomain : FieldIsDomain.{u} := by
  intro R _
  apply (integralDomainCharacterization R).mpr
  refine ⟨zero_ne_one, ?_⟩
  intro a b hab
  by_cases ha : a = 0
  · exact Or.inl ha
  · exact Or.inr (divisionRingLeftZeroProduct R a b ha hab)

theorem quaternionDivisionRing : QuaternionDivisionRing :=
  DomainFieldQuaternionDivisionExample.divisionRingExample

theorem quaternionRelations : QuaternionRelations := by
  obtain ⟨_, _, _, hij, hji, hanti⟩ := DomainFieldQuaternionDivisionExample.unitRelations
  exact ⟨hij, hji, hanti⟩

theorem quaternionConjugateAndInverse : QuaternionConjugateAndInverse :=
  ⟨DomainFieldQuaternionDivisionExample.conjugateProducts,
    DomainFieldQuaternionDivisionExample.positiveDenominator,
    DomainFieldQuaternionDivisionExample.inverseFormula⟩

theorem quaternionMatrixConstruction : QuaternionMatrixConstruction :=
  ⟨DomainFieldQuaternionDivisionExample.coordinateExpansion,
    DomainFieldQuaternionDivisionExample.matrixRealization,
    DomainFieldQuaternionDivisionExample.matrixAlgebraEquivalence,
    DomainFieldQuaternionDivisionExample.matrixClosure,
    DomainFieldQuaternionDivisionExample.ringLaws⟩

end D07.Ch08.DomainField
