import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.GenericCubic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.IsIntegral

open Polynomial

namespace GaloisFormalization.IG.GenericCubic

noncomputable abbrev polynomial {R : Type*} [CommRing R] (a : R) : R[X] :=
  Specs.GaloisFormalization.IG.GenericCubic.polynomial a

theorem polynomial_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : R) :
    (polynomial a).map f = polynomial (f a) := by
  simp [Specs.GaloisFormalization.IG.GenericCubic.polynomial]

private theorem cubic_toPoly_eq {R : Type*} [CommRing R] (a : R) :
    (⟨1, 0, -1, -a⟩ : Cubic R).toPoly = polynomial a := by
  simp [Cubic.toPoly, Specs.GaloisFormalization.IG.GenericCubic.polynomial, sub_eq_add_neg]

theorem polynomial_monic_degree {R : Type*} [CommRing R] [Nontrivial R] (a : R) :
    (polynomial a).Monic ∧ (polynomial a).degree = 3 := by
  rw [← cubic_toPoly_eq]
  exact ⟨Cubic.monic_of_a_eq_one', Cubic.degree_of_a_ne_zero' one_ne_zero⟩

theorem polynomial_discr {R : Type*} [CommRing R] [Nontrivial R] (a : R) :
    (polynomial a).discr = 4 - 27 * a ^ 2 := by
  rw [Polynomial.discr_of_degree_eq_three (polynomial_monic_degree a).2, ← cubic_toPoly_eq]
  simp only [Cubic.coeff_eq_a, Cubic.coeff_eq_b, Cubic.coeff_eq_c, Cubic.coeff_eq_d]
  ring

theorem cubic_toPoly_discr {R : Type*} [CommRing R] [Nontrivial R] (a : R) :
    (⟨1, 0, -1, -a⟩ : Cubic R).toPoly = polynomial a ∧
      (⟨1, 0, -1, -a⟩ : Cubic R).discr = (polynomial a).discr := by
  refine ⟨cubic_toPoly_eq a, ?_⟩
  rw [polynomial_discr, Cubic.discr]
  ring

private theorem generic_not_isRoot {K : Type*} [Field K] (r : RatFunc K) :
    ¬ IsRoot (polynomial (RatFunc.X : RatFunc K)) r := by
  intro hr
  have heq : r ^ 3 - r - RatFunc.X = 0 := by
    simpa [Polynomial.IsRoot, Specs.GaloisFormalization.IG.GenericCubic.polynomial] using hr
  -- A root satisfies the monic equation over the coefficient polynomial ring.
  have hint : IsIntegral K[X] r := by
    refine ⟨polynomial (X : K[X]), (polynomial_monic_degree _).1, ?_⟩
    simpa [Specs.GaloisFormalization.IG.GenericCubic.polynomial] using heq
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hpEq : p ^ 3 - p = X := by
    apply RatFunc.algebraMap_injective K
    simpa [hp] using sub_eq_zero.mp heq
  by_cases hdegree : p.natDegree = 0
  · have heval := congrArg natDegree hpEq
    have hle : (p ^ 3 - p).natDegree ≤ 0 :=
      (natDegree_sub_le _ _).trans (by simp [natDegree_pow, hdegree])
    rw [heval, natDegree_X] at hle
    omega
  · have hlt : p.natDegree < (p ^ 3).natDegree := by
      rw [natDegree_pow]
      omega
    have heval := congrArg natDegree hpEq
    rw [natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_pow, natDegree_X] at heval
    omega

theorem generic_irreducible (K : Type*) [Field K] :
    Irreducible (polynomial (RatFunc.X : RatFunc K)) := by
  have hdegree := natDegree_eq_of_degree_eq_some (polynomial_monic_degree (RatFunc.X : RatFunc K)).2
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [hdegree]
  · exact generic_not_isRoot

theorem generic_separable (K : Type*) [Field K] [CharZero K] :
    (polynomial (RatFunc.X : RatFunc K)).Separable :=
  (generic_irreducible K).separable

theorem generic_discr_nonsquare (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] :
    ¬ IsSquare (polynomial (RatFunc.X : RatFunc K)).discr := by
  rintro ⟨r, hr⟩
  let D : K[X] := C 4 - C 27 * X ^ 2
  have hrSq : algebraMap K[X] (RatFunc K) D = r ^ 2 := by
    simpa only [D, map_sub, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      map_ofNat, polynomial_discr, pow_two] using hr
  -- Integral closedness puts a putative square root back in the polynomial ring.
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (by decide : 0 < (2 : ℕ)) (hrSq ▸ isIntegral_algebraMap (x := D))
  have hD : D = p ^ 2 := by
    apply RatFunc.algebraMap_injective K
    rw [map_pow, hp, hrSq]
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq ((4 : K) / 27) zero_lt_two
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at ha
    exact (div_ne_zero (by norm_num) (by norm_num)) ha.symm
  have hDa : D.eval a = 0 := by
    simp only [D, eval_sub, eval_C, eval_mul, eval_pow, eval_X, ha]
    rw [show (27 : K) * (4 / 27) = 4 by field_simp, sub_self]
  have hpa : p.eval a = 0 := by
    have h := hDa
    rw [hD, eval_pow, pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)] at h
    exact h
  -- A square and its derivative both vanish at a root, but D has a simple root at a.
  have hderiv : D.derivative.eval a = 0 := by
    rw [hD, pow_two, derivative_mul]
    simp [hpa]
  have hderivValue : D.derivative.eval a = -54 * a := by
    simp [D, derivative_pow]
    ring
  rw [hderivValue] at hderiv
  exact (mul_ne_zero (by norm_num) ha0) hderiv

theorem geometric :
    let t : RatFunc (AlgebraicClosure ℚ) := RatFunc.X
    (polynomial t).Monic ∧ Irreducible (polynomial t) ∧ (polynomial t).Separable ∧
      (polynomial t).discr = 4 - 27 * t ^ 2 ∧ ¬ IsSquare (polynomial t).discr := by
  dsimp only
  exact ⟨(polynomial_monic_degree _).1, generic_irreducible _, generic_separable _,
    polynomial_discr _, generic_discr_nonsquare _⟩

theorem arithmetic_discr :
    let t : RatFunc ℚ := RatFunc.X
    (polynomial t).discr = 4 - 27 * t ^ 2 :=
  polynomial_discr _

theorem generic_coefficients (K : Type*) [Field K] :
    (polynomial (X : K[X])).map (algebraMap K[X] (RatFunc K)) =
      polynomial (RatFunc.X : RatFunc K) := by
  rw [polynomial_map, RatFunc.algebraMap_X]

theorem specialization {K : Type*} [Field K] (a : K) :
    let f := (polynomial (X : K[X])).map (evalRingHom a)
    f = polynomial a ∧ f.discr = 4 - 27 * a ^ 2 := by
  have hf : (polynomial (X : K[X])).map (evalRingHom a) = polynomial a := by
    rw [polynomial_map]
    simp
  exact ⟨hf, hf ▸ polynomial_discr a⟩

end GaloisFormalization.IG.GenericCubic
