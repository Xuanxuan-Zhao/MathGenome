import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.Substitution
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.CoefficientAlgebra

/-! Formal substitution and its laws, paper.tex, p204:W12. -/

noncomputable section

universe u

namespace FiniteCombinatorics.Series

open scoped BigOperators

/-- Formal substitution A(B). Its coefficientwise expansion and algebraic laws
below apply whenever the constant coefficient of B is zero. -/
def compose {R : Type u} [CommRing R] (A B : PowerSeries R) : PowerSeries R :=
  A.subst B

/-- Powers of a zero-constant series have no coefficients below their exponent. -/
theorem coeff_pow_eq_zero_of_lt {R : Type u} [CommRing R] (B : PowerSeries R)
    (hB : PowerSeries.constantCoeff B = 0) (n j : ℕ) (hnj : n < j) :
    PowerSeries.coeff n (B ^ j) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hnj)
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero j hB)

/-- Each coefficient of A(B) is a finite sum, even when A has infinitely many
nonzero coefficients. This includes degree zero. -/
theorem coeff_compose {R : Type u} [CommRing R] (A B : PowerSeries R)
    (hB : PowerSeries.constantCoeff B = 0) (n : ℕ) :
    PowerSeries.coeff n (compose A B) =
      ∑ j ∈ Finset.range (n + 1),
        PowerSeries.coeff j A * PowerSeries.coeff n (B ^ j) := by
  rw [compose, PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hB)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  apply Finset.mem_coe.mpr
  apply Finset.mem_range.mpr
  by_contra h
  have hjn : n < j := by omega
  have hz := coeff_pow_eq_zero_of_lt B hB n j hjn
  exact hj (by simp [hz])

/-- Substitution by a zero-constant series preserves the outer constant term. -/
theorem constantCoeff_compose {R : Type u} [CommRing R] (A B : PowerSeries R)
    (hB : PowerSeries.constantCoeff B = 0) :
    PowerSeries.constantCoeff (compose A B) = PowerSeries.constantCoeff A := by
  simpa [compose, PowerSeries.constantCoeff_eq] using
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero hB A

/-- Substitution preserves sums. -/
theorem compose_add {R : Type u} [CommRing R] (A D B : PowerSeries R)
    (hB : PowerSeries.constantCoeff B = 0) :
    compose (A + D) B = compose A B + compose D B :=
  PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero' hB) A D

/-- Substitution preserves products. -/
theorem compose_mul {R : Type u} [CommRing R] (A D B : PowerSeries R)
    (hB : PowerSeries.constantCoeff B = 0) :
    compose (A * D) B = compose A B * compose D B :=
  PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hB) A D

/-- Associativity requires both inner series to have zero constant term. -/
theorem compose_assoc {R : Type u} [CommRing R] (A B C : PowerSeries R)
    (hB : PowerSeries.constantCoeff B = 0) (hC : PowerSeries.constantCoeff C = 0) :
    compose (compose A B) C = compose A (compose B C) :=
  PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hB)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hC) A

/-- Substituting the variable leaves every series unchanged. -/
theorem compose_X {R : Type u} [CommRing R] (A : PowerSeries R) :
    compose A PowerSeries.X = A :=
  PowerSeries.X_subst A

/-- Substituting into the variable returns the inner series. -/
theorem X_compose {R : Type u} [CommRing R] (B : PowerSeries R)
    (hB : PowerSeries.constantCoeff B = 0) : compose PowerSeries.X B = B :=
  PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hB)

/-- Constants are fixed under substitution. -/
theorem compose_C {R : Type u} [CommRing R] (r : R) (B : PowerSeries R)
    (_hB : PowerSeries.constantCoeff B = 0) :
    compose (PowerSeries.C r) B = PowerSeries.C r :=
  PowerSeries.subst_C r

/-- The formal chain rule needs no division and no invertible linear term. -/
theorem derivative_compose {R : Type u} [CommRing R] (A B : PowerSeries R)
    (hB : PowerSeries.constantCoeff B = 0) :
    PowerSeries.derivative (compose A B) =
      compose (PowerSeries.derivative A) B * PowerSeries.derivative B :=
  PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hB)

end FiniteCombinatorics.Series
