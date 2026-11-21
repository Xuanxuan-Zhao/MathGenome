import MathGenome.Internal.Specs.D07.Ch13.PowerIdentity
import MathGenome.Internal.D07.Ch03.FiniteElementOrders
import Mathlib.FieldTheory.Finite.Basic

/-! Finite-field power identities and the complete simple-root factorization. -/

universe u

namespace D07.Ch13.PowerIdentity

open Polynomial
open Specs.D07.Ch13.PowerIdentity

theorem nonzero_power_identity : NonzeroPowerIdentity.{u} := by
  intro F _ _ q hq a ha
  classical
  have h := D07.Ch03.FiniteElementOrders.power_card_eq_one Fˣ (Units.mk0 a ha)
  have hcard : Nat.card Fˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hq]
  have hv := congrArg (fun x : Fˣ => (x : F)) h
  simpa only [hcard, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] using hv

theorem power_identity : AllElementPower.{u} := by
  intro F _ _ q hq a
  have hqpos : 0 < q := hq ▸ Fintype.card_pos
  by_cases ha : a = 0
  · simp [ha, Nat.ne_of_gt hqpos]
  · calc
      a ^ q = a ^ (q - 1 + 1) := by rw [Nat.sub_add_cancel hqpos]
      _ = a := by rw [pow_succ, nonzero_power_identity F q hq a ha, one_mul]

theorem factorization : Factorization.{u} := by
  intro F _ _ q hq
  classical
  subst q
  have hm : (X ^ Fintype.card F - X : Polynomial F).Monic := by
    apply monic_X_pow_sub
    simpa using Fintype.one_lt_card (α := F)
  have hr := FiniteField.roots_X_pow_card_sub_X (K := F)
  have hc : (X ^ Fintype.card F - X : Polynomial F).roots.card =
      (X ^ Fintype.card F - X : Polynomial F).natDegree := by
    rw [hr, ← Finset.card_def, Finset.card_univ,
      FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
  have hf := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc
  rw [hr] at hf
  exact hf.symm

theorem derivative : Derivative.{u} := by
  intro F _ _ q hq
  subst q
  rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
    Polynomial.derivative_X, Nat.cast_card_eq_zero F]
  simp

theorem separable : Specs.D07.Ch13.PowerIdentity.Separable.{u} := by
  intro F _ _ q hq
  rw [Polynomial.separable_def, derivative F q hq]
  exact isCoprime_one_right.neg_right

theorem simple_roots : SimpleRoots.{u} := by
  intro F _ _ q hq a
  classical
  subst q
  rw [← Polynomial.count_roots,
    FiniteField.roots_X_pow_card_sub_X]
  simp

end D07.Ch13.PowerIdentity
