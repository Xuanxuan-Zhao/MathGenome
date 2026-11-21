import MathGenome.Internal.Specs.D07.Ch01.ArithmeticExamples
import MathGenome.Internal.D07.Ch01.IntegerPowerLaws
import MathGenome.Internal.D07.Foundations.IntegerArithmetic
import Mathlib.Data.ZMod.Units

/-! Arithmetic groups, integer congruence, and all modulus boundary cases
in `K07.01.arithmetic_examples` (paper.tex:351–356). -/

namespace D07.Ch01.ArithmeticExamples

universe u

open Specs.D07.Ch01.ArithmeticExamples

private theorem additive_abelian_laws (A : Type*) [AddCommGroup A] :
    AdditiveAbelianLaws A :=
  ⟨add_assoc, zero_add, add_zero, add_neg_cancel, neg_add_cancel, add_comm⟩

private theorem multiplicative_abelian_laws (A : Type*) [CommGroup A] :
    Specs.D07.Ch01.GroupDefinition.groupAxiomsValue A (· * ·) 1 Inv.inv ∧
      ∀ a b : A, a * b = b * a :=
  ⟨⟨mul_assoc, one_mul, mul_one, mul_inv_cancel, inv_mul_cancel⟩, mul_comm⟩

theorem additive_arithmetic_groups : AdditiveArithmeticGroups :=
  ⟨additive_abelian_laws ℤ, additive_abelian_laws ℚ,
    additive_abelian_laws ℝ, additive_abelian_laws ℂ⟩

theorem field_nonzero_operations : FieldNonzeroOperations.{u} := by
  intro F _
  exact ⟨one_ne_zero, fun _ _ ha hb => mul_ne_zero ha hb,
    fun a ha => ⟨inv_ne_zero ha, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩⟩

theorem field_units_correspondence : FieldUnitsCorrespondence.{u} := by
  intro F _ a
  change IsUnit a ↔ a ≠ 0
  exact isUnit_iff_ne_zero

theorem field_units_group : FieldUnitsGroup.{u} := by
  intro F _
  exact multiplicative_abelian_laws Fˣ

theorem congruence_bridge : CongruenceBridge := by
  intro n a b
  exact ZMod.intCast_eq_intCast_iff_dvd_sub a b n

theorem congruence_addition : CongruenceAddition := by
  intro n a b c d hab hcd
  apply (congruence_bridge n (a + c) (b + d)).mp
  simpa only [Int.cast_add] using
    congrArg₂ (· + ·) ((congruence_bridge n a b).mpr hab)
      ((congruence_bridge n c d).mpr hcd)

theorem residue_additive_group : ResidueAdditiveGroup := by
  intro n _
  exact additive_abelian_laws (ZMod n)

theorem residue_one_generates : ResidueOneGenerates := by
  intro n _ a
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
  exact ⟨k, by simp⟩

theorem unique_representatives : UniqueRepresentatives := by
  intro n hn a
  have : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  refine ⟨a.val, ⟨ZMod.val_lt a, ZMod.natCast_zmod_val a⟩, ?_⟩
  intro r hr
  have h := congrArg ZMod.val hr.2
  simpa only [ZMod.val_natCast_of_lt hr.1] using h

theorem bezout_inverse : BezoutInverse := by
  intro n a x y h
  have hc := congrArg (fun z : ℤ => (z : ZMod n)) h
  have hx : (x : ZMod n) * (a : ZMod n) = 1 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      mul_zero, add_zero, Int.cast_one] using hc
  exact ⟨(mul_comm _ _).trans hx, hx⟩

theorem inverse_common_divisor : InverseCommonDivisor := by
  intro n a b h d ha hn
  have hprod : d ∣ a * b := dvd_mul_of_dvd_left ha b
  have hsub : d ∣ a * b - 1 := dvd_trans hn h
  have h1 := dvd_sub hprod hsub
  simpa only [sub_sub_cancel] using h1

theorem residue_unit_criterion : ResidueUnitCriterion := by
  intro n _ a
  rw [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm,
    Int.isCoprime_iff_gcd_eq_one]

theorem residue_inverse_criterion : ResidueInverseCriterion := by
  intro n hn a
  exact isUnit_iff_exists.symm.trans (residue_unit_criterion n hn a)

theorem residue_units_correspondence : ResidueUnitsCorrespondence := by
  intro n a
  exact isUnit_iff_exists

theorem residue_units_group : ResidueUnitsGroup := by
  intro n
  exact multiplicative_abelian_laws (ZMod n)ˣ

theorem residue_invertibility_closed : ResidueInvertibilityClosed := by
  intro n
  exact ⟨isUnit_one, fun _ _ ha hb => ha.mul hb, fun u => u⁻¹.isUnit⟩

theorem modulus_one_trivial : ModulusOneTrivial := by
  refine ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _, ?_⟩
  intro a
  simp

theorem modulus_greater_one : ModulusGreaterOne := by
  intro n hn
  have : Fact (1 < n) := ⟨hn⟩
  have hz : ¬ ∃ b : ZMod n, (0 : ZMod n) * b = 1 := by
    rintro ⟨b, hb⟩
    exact zero_ne_one (by simpa only [zero_mul] using hb)
  refine ⟨hz, ?_⟩
  rintro ⟨g, hmul, hone⟩
  apply hz
  refine ⟨g.inv 0, ?_⟩
  have h := @mul_inv_cancel (ZMod n) g 0
  change g.mul 0 (g.inv 0) = g.one at h
  simpa only [hmul, hone] using h

theorem modulus_zero_congruence : ModulusZeroCongruence := by
  intro a b
  simp only [zero_dvd_iff, sub_eq_zero]

theorem modulus_zero_identification : ModulusZeroIdentification := by
  exact ⟨⟨RingEquiv.refl ℤ, fun _ => rfl⟩, inferInstance⟩

theorem modulus_zero_no_finite_list : ModulusZeroNoFiniteList := by
  intro N h
  obtain ⟨r, _, hr⟩ := h (-1)
  change (r : ℤ) = -1 at hr
  have hp : (0 : ℤ) ≤ r := Int.natCast_nonneg r
  rw [hr] at hp
  exact (by decide : ¬ (0 : ℤ) ≤ -1) hp

end D07.Ch01.ArithmeticExamples
