import MathGenome.Internal.Specs.D05.M09.Existence.IrreducibleDegree
import MathGenome.Internal.D05.M09.Existence.QuotientFieldBasis
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace D05.M09.Existence.IrreducibleDegree

open Polynomial

theorem degree_dvd_kernel :
    Specs.D05.M09.Existence.IrreducibleDegree.degree_dvd_kernel := by
  intro K V _ _ _ _ T p hp
  let : Fact (Irreducible p) := ⟨hp⟩
  obtain ⟨m, hm⟩ := QuotientFieldBasis.quotient_module T p
  let := m
  exact ⟨Module.finrank (AdjoinRoot p)
      (Specs.D05.M09.Existence.QuotientFieldBasis.Kernel T p),
    QuotientFieldBasis.dimension_formula T p hm⟩

theorem quadratic_complete_square :
    Specs.D05.M09.Existence.IrreducibleDegree.quadratic_complete_square := by
  intro b c x
  ring

theorem quadratic_no_real_root :
    Specs.D05.M09.Existence.IrreducibleDegree.quadratic_no_real_root := by
  intro b c h x
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
  rw [quadratic_complete_square b c x]
  have hs := sq_nonneg (x + b / 2)
  nlinarith

/-- Its leading term has degree two, independently of b and c. -/
theorem quadratic_natDegree (b c : ℝ) :
    (X ^ 2 + C b * X + C c).natDegree = 2 := by
  rw [natDegree_add_C, natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · have h := natDegree_mul_le (p := C b) (q := (X : ℝ[X]))
    simp only [natDegree_C, natDegree_X, zero_add, natDegree_X_pow] at *
    exact lt_of_le_of_lt h (by decide)

theorem quadratic_irreducible :
    Specs.D05.M09.Existence.IrreducibleDegree.quadratic_irreducible := by
  intro b c h
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, quadratic_natDegree]
    decide
  · exact quadratic_no_real_root b c h

/-- Evaluation identifies the polynomial kernel with the stated operator kernel. -/
theorem quadratic_aeval {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V) (b c : ℝ) :
    aeval T (X ^ 2 + C b * X + C c) = T ^ 2 + b • T + c • 1 := by
  simp [Algebra.algebraMap_eq_smul_one]

theorem quadratic_kernel_even :
    Specs.D05.M09.Existence.IrreducibleDegree.quadratic_kernel_even := by
  intro V _ _ _ T b c h
  have hd := degree_dvd_kernel T
    (X ^ 2 + C b * X + C c) (quadratic_irreducible b c h)
  rw [quadratic_natDegree, quadratic_aeval] at hd
  exact even_iff_two_dvd.mpr hd

end D05.M09.Existence.IrreducibleDegree
