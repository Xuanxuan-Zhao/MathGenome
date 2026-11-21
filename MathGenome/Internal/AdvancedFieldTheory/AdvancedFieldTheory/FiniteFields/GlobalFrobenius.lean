import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.GlobalFrobenius

/-!
# Global arithmetic Frobenius (FT-E04A)

The q-power endomorphism of an algebraic extension of a finite field is an
automorphism. No positive power of it can fix the entire algebraic closure:
otherwise the nonzero polynomial X^(q^d)-X would vanish on an infinite field.
-/

universe u v
noncomputable section
namespace AdvancedFieldTheory

/-- Arithmetic Frobenius on the specified algebraic closure, as a member of Gal(Ω/k). -/
abbrev globalFrobenius (k : Type u) (Ω : Type v) [Field k] [Fintype k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] : Ω ≃ₐ[k] Ω :=
  FiniteField.frobeniusAlgEquivOfAlgebraic k Ω

variable (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]

@[simp] theorem globalFrobenius_apply (x : Ω) :
    globalFrobenius k Ω x = x ^ Fintype.card k := rfl

theorem globalFrobenius_fixes_base (a : k) :
    globalFrobenius k Ω (algebraMap k Ω a) = algebraMap k Ω a :=
  (globalFrobenius k Ω).commutes a

theorem globalFrobenius_bijective : Function.Bijective (globalFrobenius k Ω) :=
  (globalFrobenius k Ω).bijective

@[simp] theorem globalFrobenius_pow_apply (d : ℕ) (x : Ω) :
    (globalFrobenius k Ω ^ d) x = x ^ (Fintype.card k ^ d) := by
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

open Polynomial in
theorem globalFrobenius_pow_ne_one (d : ℕ) (hd : 0 < d) :
    globalFrobenius k Ω ^ d ≠ 1 := by
  intro h
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hfix (x : Ω) : x ^ (Fintype.card k ^ d) = x := by
    simpa only [globalFrobenius_pow_apply, AlgEquiv.one_apply] using
      DFunLike.congr_fun h x
  have hzero : (X ^ (Fintype.card k ^ d) - X : Polynomial Ω) = 0 := by
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_pow, eval_X, eval_zero, sub_eq_zero]
    exact hfix x
  exact FiniteField.X_pow_card_pow_sub_X_ne_zero Ω hd.ne' Fintype.one_lt_card hzero

theorem globalFrobenius_exists_moved (d : ℕ) (hd : 0 < d) :
    ∃ x : Ω, (globalFrobenius k Ω ^ d) x ≠ x := by
  by_contra! h
  apply globalFrobenius_pow_ne_one k Ω d hd
  exact DFunLike.ext _ _ h

theorem globalFrobenius_orderOf : orderOf (globalFrobenius k Ω) = 0 :=
  orderOf_eq_zero_iff'.mpr (globalFrobenius_pow_ne_one k Ω)

end AdvancedFieldTheory
