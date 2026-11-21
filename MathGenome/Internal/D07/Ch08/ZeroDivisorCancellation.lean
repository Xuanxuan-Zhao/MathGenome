import MathGenome.Internal.Specs.D07.Ch08.ZeroDivisorCancellation
import MathGenome.Internal.D07.Ch08.DomainField
import MathGenome.Internal.D07.Ch08.Units
import Mathlib.Algebra.Ring.Basic

/-! Zero divisors and cancellation, K07.08.zero_divisor_cancellation. -/

universe u

namespace D07.Ch08.ZeroDivisorCancellation

open Specs.D07.Ch08.ZeroDivisorCancellation

theorem zeroDivisorCharacterization : ZeroDivisorCharacterization.{u} := by
  intro R _ a
  rfl

theorem unitZeroProducts : UnitZeroProducts.{u} := by
  intro R _ a ha
  obtain ⟨v, hav, hva⟩ := (Units.unitCharacterization R a).mp ha
  constructor
  · intro x hx
    calc
      x = 1 * x := (one_mul x).symm
      _ = (v * a) * x := by rw [hva]
      _ = v * (a * x) := mul_assoc _ _ _
      _ = 0 := by rw [hx, mul_zero]
  · intro x hx
    calc
      x = x * 1 := (mul_one x).symm
      _ = x * (a * v) := by rw [hav]
      _ = (x * a) * v := (mul_assoc _ _ _).symm
      _ = 0 := by rw [hx, zero_mul]

theorem unitNotZeroDivisor : UnitNotZeroDivisor.{u} := by
  intro R _ a ha hdiv
  obtain ⟨_, b, hb, hab⟩ := hdiv
  obtain ⟨hleft, hright⟩ := unitZeroProducts R a ha
  rcases hab with hab | hba
  · exact hb (hleft b hab)
  · exact hb (hright b hba)

theorem leftCancellation : LeftCancellation.{u} := by
  intro R _ a ha b c habc
  have hsub : a * (b - c) = 0 := by rw [mul_sub, habc, sub_self]
  exact sub_eq_zero.mp (ha (b - c) hsub)

theorem rightCancellation : RightCancellation.{u} := by
  intro R _ a ha b c habc
  have hsub : (b - c) * a = 0 := by rw [sub_mul, habc, sub_self]
  exact sub_eq_zero.mp (ha (b - c) hsub)

theorem domainCancellation : DomainCancellation.{u} := by
  intro R _ _ a b c ha
  have hz := ((DomainField.integralDomainCharacterization R).mp inferInstance).2
  constructor
  · constructor
    · exact leftCancellation R a (fun x hx => (hz a x hx).resolve_left ha) b c
    · intro h
      rw [h]
  · constructor
    · exact rightCancellation R a (fun x hx => (hz x a hx).resolve_right ha) b c
    · intro h
      rw [h]

theorem zeroProducts : ZeroProducts.{u} := by
  intro R _ b c
  exact ⟨(zero_mul b).trans (zero_mul c).symm,
    (mul_zero b).trans (mul_zero c).symm⟩

theorem zeroCancellationFailure : ZeroCancellationFailure.{u} := by
  intro R _ _
  exact ⟨0, 1, zero_ne_one, zeroProducts R 0 1⟩

theorem integerTwoNeither : IntegerTwoNeither := by
  refine ⟨by decide, Units.integerTwoNotIsUnit, ?_⟩
  rintro ⟨_, b, hb, hab | hba⟩
  · have h := (domainCancellation ℤ 2 b 0 (by decide)).1.mp
      (hab.trans (mul_zero 2).symm)
    exact hb h
  · have h := (domainCancellation ℤ 2 b 0 (by decide)).2.mp
      (hba.trans (zero_mul 2).symm)
    exact hb h

end D07.Ch08.ZeroDivisorCancellation
