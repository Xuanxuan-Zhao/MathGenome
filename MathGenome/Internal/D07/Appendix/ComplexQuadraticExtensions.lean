import MathGenome.Internal.Specs.D07.Appendix.ComplexQuadraticExtensions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
The complex square-root lemma and its quadratic consequences, proved without
complex algebraic closedness, complex logarithms, or complex exponentials.
-/

universe u

namespace D07.Appendix.ComplexQuadraticExtensions

open Polynomial
open Specs.D07.Appendix.ComplexQuadraticExtensions

/-- The real-coordinate construction in the source, including the real-axis cases. -/
theorem square_root_exists : SquareRootExists := by
  rintro ⟨a, b⟩
  by_cases hb : b = 0
  · subst b
    by_cases ha : 0 ≤ a
    · refine ⟨⟨Real.sqrt a, 0⟩, ?_⟩
      apply Complex.ext <;> simp [pow_two, Real.mul_self_sqrt ha]
    · have ha' : 0 ≤ -a := by linarith
      refine ⟨⟨0, Real.sqrt (-a)⟩, ?_⟩
      apply Complex.ext <;> simp [pow_two, Real.mul_self_sqrt ha']
  · let r := Real.sqrt (a ^ 2 + b ^ 2)
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hrr : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
    have hbb : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    have hra : 0 < r + a := by nlinarith
    let u := Real.sqrt ((r + a) / 2)
    have hu : 0 < u := Real.sqrt_pos.mpr (by positivity)
    have huu : u ^ 2 = (r + a) / 2 := Real.sq_sqrt (by positivity)
    have huv : 2 * u ≠ 0 := by positivity
    have hvv : (b / (2 * u)) ^ 2 = (r - a) / 2 := by
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero 2 huv)).mpr
      nlinarith [hrr]
    refine ⟨⟨u, b / (2 * u)⟩, ?_⟩
    apply Complex.ext <;> simp only [pow_two, Complex.mul_re, Complex.mul_im]
    · nlinarith [huu, hvv]
    · field_simp
      nlinarith

/-- A square root of the discriminant gives a root by field arithmetic. -/
theorem quadratic_root_exists (A B D : ℂ) (hA : A ≠ 0) :
    ∃ r : ℂ, A * r ^ 2 + B * r + D = 0 := by
  obtain ⟨w, hw⟩ := square_root_exists (discrim A B D)
  simpa only [← pow_two] using
    exists_quadratic_eq_zero hA ⟨w, by simpa only [pow_two] using hw.symm⟩

/-- Both linear factors are retained even when their roots coincide. -/
theorem quadratic_factorization : QuadraticFactorization := by
  intro A B D hA
  obtain ⟨r, hr⟩ := quadratic_root_exists A B D hA
  let s := -B / A - r
  have hB : -(A * r + A * s) = B := by
    dsimp [s]
    field_simp
    ring
  have hD : A * r * s = D := by
    dsimp [s]
    field_simp
    linear_combination -hr
  refine ⟨r, s, ?_⟩
  calc
    C A * X ^ 2 + C B * X + C D =
        C A * X ^ 2 - C (A * r + A * s) * X + C (A * r * s) := by
      rw [hD, ← hB, map_neg]
      ring
    _ = C A * (X - C r) * (X - C s) := by
      simp only [map_add, map_mul]
      ring

/-- In particular the quadratic splits over the original complex field. -/
theorem quadratic_splits : QuadraticSplits := by
  intro A B D hA
  obtain ⟨r, s, h⟩ := quadratic_factorization A B D hA
  rw [h]
  exact ((Splits.C A).mul (Splits.X_sub_C r)).mul (Splits.X_sub_C s)

/-- In a putative quadratic extension a non-scalar element would have an
irreducible quadratic minimal polynomial, contradicting the quadratic root. -/
theorem no_quadratic_extension : NoQuadraticExtension.{u} := by
  intro E _ _ _ hdim
  have hsurj : Function.Surjective (algebraMap ℂ E) := by
    intro x
    by_contra hx
    have hint : IsIntegral ℂ x := IsIntegral.of_finite ℂ x
    have hlow : 2 ≤ (minpoly ℂ x).natDegree :=
      (minpoly.two_le_natDegree_iff hint).mpr hx
    have hupp := minpoly.natDegree_le x (A := ℂ)
    have hdeg : (minpoly ℂ x).natDegree = 2 := by omega
    let p := minpoly ℂ x
    have hpdeg : p.natDegree = 2 := hdeg
    have hp : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
      calc
        p = ∑ i ∈ Finset.range 3, C (p.coeff i) * X ^ i :=
          p.as_sum_range_C_mul_X_pow' (by omega)
        _ = _ := by simp [Finset.sum_range_succ]; ring
    have hA : p.coeff 2 ≠ 0 := by
      rw [← hpdeg, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (minpoly.ne_zero hint)
    obtain ⟨r, hr⟩ := quadratic_root_exists (p.coeff 2) (p.coeff 1) (p.coeff 0) hA
    have hroot : p.IsRoot r := by
      rw [Polynomial.IsRoot, hp]
      simpa only [eval_add, eval_mul, eval_pow, eval_C, eval_X] using hr
    exact (minpoly.irreducible hint).not_isRoot_of_natDegree_ne_one (by omega) hroot
  have hone : Module.finrank ℂ E = 1 :=
    Module.finrank_of_bijective_algebraMap ⟨(algebraMap ℂ E).injective, hsurj⟩
  omega

/-- A cardinal degree of two itself supplies finite-dimensionality. -/
theorem no_cardinal_quadratic_extension : NoCardinalQuadraticExtension.{u} := by
  intro E _ _ hdim
  have hdim' : Module.rank ℂ E = (2 : ℕ) := by simpa using hdim
  let : FiniteDimensional ℂ E := Module.finite_of_rank_eq_nat hdim'
  apply no_quadratic_extension E
  exact Module.finrank_eq_of_rank_eq hdim'

end D07.Appendix.ComplexQuadraticExtensions
