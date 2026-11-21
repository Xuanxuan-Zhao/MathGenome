import MathGenome.Internal.Specs.D07.Ch08.Units
import MathGenome.Internal.D07.Ch08.RingDefinition
import MathGenome.Internal.D07.Ch08.UnitsOneSidedInverseCounterexample
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
K07.08.units (paper.tex:1210–1228): units, uniqueness of inverses,
their group structure, the one-sided shift example, and dependence on
the ambient ring. No commutativity or nontriviality is imposed on `R`.
-/

universe u

namespace D07.Ch08.Units

open Specs.D07.Ch08.Units

theorem unitCharacterization : UnitCharacterization.{u} := by
  intro R _ a
  exact isUnit_iff_exists

theorem leftRightInverseUnique : LeftRightInverseUnique.{u} :=
  UnitsOneSidedInverseCounterexample.leftRightInverseUnique

theorem inverseUnique : InverseUnique.{u} := by
  intro R _ a b c _ hba hac _
  exact leftRightInverseUnique R a b c hba hac

theorem unitsFormGroup : UnitsFormGroup.{u} := by
  intro R _
  exact ⟨inferInstance, rfl, rfl⟩

theorem unitsValueLaws : UnitsValueLaws.{u} := by
  intro R _ a b
  exact ⟨rfl, rfl, a.val_inv, a.inv_val⟩

theorem inverseProduct : InverseProduct.{u} := by
  intro R _ a b
  exact mul_inv_rev a b

theorem shiftCounterexample : ShiftCounterexample.{u} := by
  intro K _
  exact ⟨UnitsOneSidedInverseCounterexample.standardBasisVectors K,
    UnitsOneSidedInverseCounterexample.shiftOnBasis K,
    UnitsOneSidedInverseCounterexample.backwardShiftZero K,
    UnitsOneSidedInverseCounterexample.backwardShiftOnSucc K,
    UnitsOneSidedInverseCounterexample.backwardShiftMulShift K,
    UnitsOneSidedInverseCounterexample.shiftMulBackwardShiftAtZero K,
    UnitsOneSidedInverseCounterexample.basisZeroNeZero K,
    UnitsOneSidedInverseCounterexample.shiftMulBackwardShiftNeOne K,
    UnitsOneSidedInverseCounterexample.shiftNotIsUnit K,
    UnitsOneSidedInverseCounterexample.backwardShiftNotIsUnit K⟩

theorem rationalTwoIsUnit : RationalTwoIsUnit := by
  exact isUnit_iff_ne_zero.mpr (by decide)

theorem integerUnits : IntegerUnits := by
  intro a
  exact Int.isUnit_iff

theorem integerTwoNotIsUnit : IntegerTwoNotIsUnit := by
  intro h
  have h' := (integerUnits 2).mp h
  exact (by decide : ¬ ((2 : ℤ) = 1 ∨ (2 : ℤ) = -1)) h'

end D07.Ch08.Units
