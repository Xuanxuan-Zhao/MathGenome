import MathGenome.Internal.Specs.D07.Ch11.MultiplicityDerivative
import MathGenome.Internal.D07.Ch11.DegreeArithmetic
import MathGenome.Internal.D07.Ch11.FactorRemainder
import MathGenome.Internal.D07.Ch11.RootBound

/-!
Formal derivatives and repeated roots, K07.11.multiplicity_derivative.

We reuse the upstream maximal-power characterization of root multiplicity.
Factoring off this maximal power leaves a polynomial nonvanishing at a.
The product rule then distinguishes multiplicity one from multiplicity at
least two by evaluation, in arbitrary characteristic. All differentiation
is on formal coefficient sequences.
-/

universe u

namespace D07.Ch11.MultiplicityDerivative

open Polynomial
open Specs.D07.Ch11.MultiplicityDerivative

theorem power_divisor_bound : PowerDivisorBound.{u} := by
  intro F _ f hf a k hk
  have hdeg := Polynomial.natDegree_le_of_dvd hk hf
  simpa using hdeg

theorem multiplicity_maximum : MultiplicityMaximum.{u} := by
  intro F _ f hf a
  have hmax := RootBound.multiplicity_characterization F f hf a
  refine ⟨hmax, (hmax _).mpr le_rfl, ?_⟩
  intro hnext
  exact Nat.not_succ_le_self _ ((hmax _).mp hnext)

theorem multiplicity_factorization : MultiplicityFactorization.{u} := by
  intro F _ f hf a
  obtain ⟨g, hfg, hnot⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf a
  exact ⟨g, hfg, fun hg => hnot ((FactorRemainder.factor_iff F g a).mp hg)⟩

theorem nonroot_multiplicity : NonrootMultiplicity.{u} := by
  intro F _ f hf a
  constructor
  · exact Polynomial.rootMultiplicity_eq_zero
  · intro hm ha
    have hpos := (Polynomial.rootMultiplicity_pos hf).mpr ha
    simp [hm] at hpos

theorem derivative_coefficients : DerivativeCoefficients.{u} := by
  intro R _ f n
  simpa only [nsmul_eq_mul', Nat.cast_add, Nat.cast_one]
    using Polynomial.coeff_derivative f n

theorem derivative_expansion : DerivativeExpansion.{u} := by
  intro R _ f
  simpa only [Polynomial.sum, nsmul_eq_mul'] using Polynomial.derivative_apply f

theorem derivative_additive : DerivativeAdditive.{u} := by
  intro R _ f g
  exact Polynomial.derivative_add

theorem derivative_monomial : DerivativeMonomial.{u} := by
  intro R _ a i
  simpa only [nsmul_eq_mul'] using Polynomial.derivative_C_mul_X_pow a i

theorem derivative_product : DerivativeProduct.{u} := by
  intro R _ f g
  exact Polynomial.derivative_mul

theorem derivative_linear_factorization : DerivativeLinearFactorization.{u} := by
  intro R _ f g a m _ hfg
  rw [hfg, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C_pow]

theorem simple_root_derivative : SimpleRootDerivative.{u} := by
  intro F _ f g a hfg hg
  have heval : f.derivative.eval a = g.eval a := by
    rw [hfg, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C]
    simp
  exact ⟨heval, heval ▸ hg⟩

theorem higher_multiplicity_derivative : HigherMultiplicityDerivative.{u} := by
  intro F _ f g a m hm hfg
  have hm0 : m ≠ 0 := by omega
  have hm1 : m - 1 ≠ 0 := by omega
  rw [derivative_linear_factorization F f g a m (by omega) hfg]
  simp [hm0, hm1]

theorem repeated_root_criterion : RepeatedRootCriterion.{u} := by
  intro F _ f hf a
  obtain ⟨g, hfg, hg⟩ := multiplicity_factorization F f hf a
  constructor
  · intro hm
    have hroot : f.eval a = 0 :=
      (Polynomial.rootMultiplicity_pos hf).mp (by omega)
    exact ⟨hroot, higher_multiplicity_derivative F f g a _ (by omega) hfg⟩
  · rintro ⟨hroot, hderiv⟩
    have hpos : 0 < f.rootMultiplicity a :=
      (Polynomial.rootMultiplicity_pos hf).mpr hroot
    by_contra hm
    have hone : f.rootMultiplicity a = 1 := by omega
    have hfg' : f = (X - C a) * g := by simpa [hone] using hfg
    exact (simple_root_derivative F f g a hfg' hg).2 hderiv

theorem multiplicity_at_least_two : MultiplicityAtLeastTwo.{u} := by
  intro F _ f hf a
  exact repeated_root_criterion F f hf a

theorem positive_characteristic_example : PositiveCharacteristicExample.{u} := by
  intro F _ p hp _
  refine ⟨Polynomial.derivative_X_pow p, ?_, by simp, ?_⟩
  · rw [Polynomial.derivative_X_pow, CharP.cast_eq_zero F p]
    simp
  · intro c hc
    have hdeg := congrArg Polynomial.natDegree hc
    have : p = 0 := by simpa using hdeg
    exact hp.ne_zero this

theorem zero_has_no_maximum : ZeroHasNoMaximum.{u} := by
  intro F _ a
  exact (RootBound.zero_polynomial_exception F a).2

end D07.Ch11.MultiplicityDerivative
