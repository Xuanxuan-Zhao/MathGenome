import MathGenome.Internal.Specs.D07.Ch10.UfdNotPid
import MathGenome.Internal.D07.Ch11.PolynomialUfd
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.NormNum

/-!
The integer polynomial ring is a UFD but is not a PID.
A generator of (2,X) would divide 2, hence be constant by degree.
Dividing X then forces that constant to divide its coefficient 1,
so the generator would be a unit, contradicting properness.
-/

namespace D07.Ch10.UfdNotPid

open Polynomial
open Specs.D07.Ch10.UfdNotPid

local notation "I₂X" => (Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X]))

theorem integerPolynomialUfd : IntegerPolynomialUfd := by
  exact (D07.Ch11.PolynomialUfd.polynomialUfdIff ℤ).mp inferInstance

theorem evenConstantCoefficient : EvenConstantCoefficient := by
  intro f hf
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hf
  simp only [coeff_add, mul_coeff_zero, coeff_ofNat_zero, coeff_X_zero, mul_zero,
    add_zero]
  exact dvd_mul_left 2 (a.coeff 0)

theorem twoXIdealProper : TwoXIdealProper := by
  intro htop
  have hone : (1 : ℤ[X]) ∈ I₂X := by rw [htop]; trivial
  have h := evenConstantCoefficient 1 hone
  norm_num at h

theorem twoXIdealNotPrincipal : TwoXIdealNotPrincipal := by
  rintro ⟨h, hh⟩
  have htwo : h ∣ (2 : ℤ[X]) := by
    apply Ideal.mem_span_singleton.mp
    rw [← hh]
    exact Ideal.subset_span (by simp)
  have hX : h ∣ (X : ℤ[X]) := by
    apply Ideal.mem_span_singleton.mp
    rw [← hh]
    exact Ideal.subset_span (by simp)
  have hd : h.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa using Polynomial.natDegree_le_of_dvd htwo (by norm_num : (2 : ℤ[X]) ≠ 0)
  have hc : h = C (h.coeff 0) := eq_C_of_natDegree_eq_zero hd
  have hunit : IsUnit (h.coeff 0) := by
    apply isUnit_iff_dvd_one.mpr
    have hdvd := (C_dvd_iff_dvd_coeff (h.coeff 0) X).mp (hc ▸ hX) 1
    simpa using hdvd
  apply twoXIdealProper
  rw [hh]
  apply Ideal.span_singleton_eq_top.mpr
  rw [hc]
  exact hunit.map C

theorem integerPolynomialNotPid : IntegerPolynomialNotPid := by
  intro hpid
  let : IsPrincipalIdealRing ℤ[X] := hpid
  exact twoXIdealNotPrincipal (Submodule.IsPrincipal.principal I₂X)

end D07.Ch10.UfdNotPid
