import MathGenome.Internal.Specs.D07.Ch10.Divisibility
import MathGenome.Internal.D07.Ch08.Units
import Mathlib.Algebra.Divisibility.Units

/-! Divisibility in a commutative nontrivial domain, K07.10.divisibility.
The basic laws follow from the defining factor witnesses. The ambient-ring
examples reuse the corresponding upstream facts about units.
-/

universe u

namespace D07.Ch10.Divisibility

open Specs.D07.Ch10.Divisibility

theorem divisibilityCharacterization : DivisibilityCharacterization.{u} := by
  intro R _ _ a b
  rfl

theorem dividesZero : DividesZero.{u} := by
  intro R _ _ a
  exact ⟨0, (mul_zero a).symm⟩

theorem zeroDividesIff : ZeroDividesIff.{u} := by
  intro R _ _ b
  constructor
  · rintro ⟨c, hc⟩
    exact hc.trans (zero_mul c)
  · intro hb
    subst b
    exact dividesZero R 0

theorem divisibilityReflexive : DivisibilityReflexive.{u} := by
  intro R _ _ a
  exact ⟨1, (mul_one a).symm⟩

theorem divisibilityTransitive : DivisibilityTransitive.{u} := by
  intro R _ _ a b d hab hbd
  obtain ⟨c, hc⟩ := hab
  obtain ⟨e, he⟩ := hbd
  refine ⟨c * e, ?_⟩
  calc
    d = b * e := he
    _ = (a * c) * e := by rw [hc]
    _ = a * (c * e) := mul_assoc a c e

theorem unitDivides : UnitDivides.{u} := by
  intro R _ _ a b ha
  exact ha.dvd

theorem dividesOneIffIsUnit : DividesOneIffIsUnit.{u} := by
  intro R _ _ a
  exact isUnit_iff_dvd_one.symm

theorem rationalTwoDividesOne : RationalTwoDividesOne :=
  (dividesOneIffIsUnit ℚ 2).mpr D07.Ch08.Units.rationalTwoIsUnit

theorem integerTwoNotDividesOne : IntegerTwoNotDividesOne := by
  intro h
  exact D07.Ch08.Units.integerTwoNotIsUnit
    ((dividesOneIffIsUnit ℤ 2).mp h)

end D07.Ch10.Divisibility
