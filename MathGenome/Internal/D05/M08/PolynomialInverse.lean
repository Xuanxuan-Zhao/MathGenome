import MathGenome.Internal.Specs.D05.M08.PolynomialInverse
import MathGenome.Internal.D05.M08.Minpoly
import MathGenome.Internal.D05.M03.Isomorphism
import Mathlib.Tactic.Ring

/-! K05.08.polynomial_inverse: the inverse criterion and polynomial inverse,
valid over every field and including the zero-dimensional space. -/

noncomputable section

namespace D05.M08.PolynomialInverse

open Polynomial

/-- An explicit Bézout identity for X and a polynomial with nonzero constant term. -/
theorem bezout_X {K : Type*} [Field K] (m : Polynomial K) (h : m.eval 0 ≠ 0) :
    ∃ a b : Polynomial K, a * X + b * m = 1 := by
  have hc : m.coeff 0 ≠ 0 := by
    rwa [coeff_zero_eq_eval_zero]
  refine ⟨-C (m.coeff 0)⁻¹ * m.divX, C (m.coeff 0)⁻¹, ?_⟩
  calc
    _ = C (m.coeff 0)⁻¹ * (m - m.divX * X) := by ring
    _ = C (m.coeff 0)⁻¹ * C (m.coeff 0) := by
      have hm : m - m.divX * X = C (m.coeff 0) := by
        rw [sub_eq_iff_eq_add, add_comm]
        exact (divX_mul_X_add m).symm
      rw [hm]
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hc, C_1]

/-- Evaluate Bézout in the possibly noncommutative endomorphism algebra.
The reverse product follows from commutation of polynomials in one operator. -/
theorem polynomial_inverse_of_constant_ne_zero {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (T : Module.End K V)
    (h : (Minpoly.minimalPolynomial K V T).eval 0 ≠ 0) :
    ∃ p : Polynomial K, aeval T p * T = 1 ∧ T * aeval T p = 1 := by
  obtain ⟨a, b, hab⟩ := bezout_X (Minpoly.minimalPolynomial K V T) h
  have hleft : aeval T a * T = 1 := by
    have heval := congrArg (aeval T) hab
    simpa only [map_add, map_mul, aeval_X, Minpoly.minimalPolynomial,
      minpoly.aeval, mul_zero, add_zero, map_one] using heval
  refine ⟨a, hleft, ?_⟩
  calc
    T * aeval T a = aeval T a * T := by
      have hc := Evaluation.polynomials_commute T X a
      change aeval T X * aeval T a = aeval T a * aeval T X at hc
      simpa only [aeval_X] using hc
    _ = 1 := hleft

/-- If X divides the minimal polynomial, an inverse of T would cancel T
from the annihilating equation and produce an annihilator of smaller degree. -/
theorem constant_ne_zero_of_isUnit {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (T : Module.End K V) (hT : IsUnit T) :
    (Minpoly.minimalPolynomial K V T).eval 0 ≠ 0 := by
  intro hz
  have hcoeff : (Minpoly.minimalPolynomial K V T).coeff 0 = 0 := by
    rwa [coeff_zero_eq_eval_zero]
  obtain ⟨q, hq⟩ := X_dvd_iff.mpr hcoeff
  have hq0 : q ≠ 0 := by
    intro hzero
    apply Minpoly.ne_zero T
    change Minpoly.minimalPolynomial K V T = 0
    simpa [hzero] using hq
  have heval : aeval T q = 0 := by
    apply hT.mul_right_eq_zero.mp
    have hann := Minpoly.annihilates T
    change aeval T (Minpoly.minimalPolynomial K V T) = 0 at hann
    rw [hq, map_mul, aeval_X] at hann
    exact hann
  have hle := Minpoly.least_degree T q heval hq0
  change (Minpoly.minimalPolynomial K V T).natDegree ≤ q.natDegree at hle
  have hdeg : (Minpoly.minimalPolynomial K V T).natDegree = q.natDegree + 1 := by
    rw [hq, natDegree_X_mul hq0]
  rw [hdeg] at hle
  exact Nat.not_succ_le_self _ hle

theorem invertible_iff_bijective :
    Specs.D05.M08.PolynomialInverse.invertible_iff_bijective := by
  intro K V _ _ _ T
  exact Module.End.isUnit_iff T

theorem invertible_iff : Specs.D05.M08.PolynomialInverse.invertible_iff := by
  intro K V _ _ _ _ T
  constructor
  · exact constant_ne_zero_of_isUnit T
  · intro h
    obtain ⟨p, hp, hp'⟩ := polynomial_inverse_of_constant_ne_zero T h
    exact ⟨⟨T, aeval T p, hp', hp⟩, rfl⟩

theorem polynomial_inverse : Specs.D05.M08.PolynomialInverse.polynomial_inverse := by
  intro K V _ _ _ _ T hT
  exact polynomial_inverse_of_constant_ne_zero T ((invertible_iff T).mp hT)

theorem inverse_eq_polynomial : Specs.D05.M08.PolynomialInverse.inverse_eq_polynomial := by
  intro K V _ _ _ _ T
  have hT : IsUnit T.toLinearMap := (invertible_iff_bijective T.toLinearMap).mpr T.bijective
  obtain ⟨p, hp, _⟩ := polynomial_inverse T.toLinearMap hT
  refine ⟨p, ?_⟩
  change aeval T.toLinearMap p * T.toLinearMap = 1 at hp
  change aeval T.toLinearMap p = T.symm.toLinearMap
  have hright : T.toLinearMap * T.symm.toLinearMap = 1 :=
    (D05.M03.Isomorphism.inverse_laws T).2
  calc
    _ = (aeval T.toLinearMap p * T.toLinearMap) * T.symm.toLinearMap := by
      rw [mul_assoc, hright, mul_one]
    _ = T.symm.toLinearMap := by rw [hp, one_mul]

theorem zero_dimension : Specs.D05.M08.PolynomialInverse.zero_dimension := by
  intro K V _ _ _ _ T hdim
  have hm := Minpoly.zero_dimension T hdim
  have hc : (Specs.D05.M08.Minpoly.minimalPolynomial_value K V T).eval 0 ≠ 0 := by
    rw [hm, eval_one]
    exact one_ne_zero
  have hzero := D05.M02.Dimension.dimension_zero_iff_zero_space.mp hdim
  have ht : T = 0 := by
    ext v
    exact hzero (T v)
  have hprod : T * T = 1 := by
    ext v
    exact (hzero ((T * T) v)).trans (hzero ((1 : Module.End K V) v)).symm
  exact ⟨hm, hc, ht, hprod, (invertible_iff T).mpr hc⟩

end D05.M08.PolynomialInverse
