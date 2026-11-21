import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.PolynomialDimension
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! Polynomial dimension over arbitrary fields. We use the Noetherian
polynomial dimension theorem and the strict dimension drop for a quotient
whose kernel contains a non-zero-divisor. This is an alternative to the
source's monic-coordinate induction, with the same hypotheses. -/
namespace P103.Ch06.PolynomialDimension

open P103.Specs.Ch06.PolynomialDimension
open scoped nonZeroDivisors

universe u

theorem polynomial_dimension : polynomial_dimensionType.{u} := by
  intro k _ n
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field]
  simp

theorem nonzero_prime_quotient_dimension :
    nonzero_prime_quotient_dimensionType.{u} := by
  intro k _ n P _ hP
  obtain ⟨f, hfP, hf⟩ := (Submodule.ne_bot_iff P).mp hP
  have h := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk P)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hf)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hfP)
  exact h.trans_eq (polynomial_dimension k n)

theorem zero_variables_prime : zero_variables_primeType.{u} := by
  intro k _ P hP
  by_contra hne
  have : P.IsPrime := hP
  have h := nonzero_prime_quotient_dimension k 0 P hP hne
  have hnonneg := ringKrullDim_nonneg_of_nontrivial
    (R := MvPolynomial (Fin 0) k ⧸ P)
  have hone : (1 : WithBot ℕ∞) ≤ 0 := calc
    1 = 0 + 1 := by simp
    _ ≤ ringKrullDim (MvPolynomial (Fin 0) k ⧸ P) + 1 := by gcongr
    _ ≤ 0 := h
  exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hone

end P103.Ch06.PolynomialDimension
