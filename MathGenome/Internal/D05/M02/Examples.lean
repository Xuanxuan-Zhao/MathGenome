import MathGenome.Internal.Specs.D05.M02.Examples
import MathGenome.Internal.D05.M02.Basis
import MathGenome.Internal.D05.M02.Dimension
import MathGenome.Internal.D05.Foundations.FormalPolynomials
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.FieldTheory.Finite.Basic

/-! K05.02.examples: standard bases, their coordinates and dimensions,
and infinite independent families in polynomial and sequence spaces. -/

noncomputable section

namespace D05.M02.Examples

theorem coordinate_basis : Specs.D05.M02.Examples.coordinate_basis := by
  intro K _ n
  refine ⟨D05.Foundations.FormalPolynomials.coordinateBasis K n, ?_, ?_⟩
  · exact Pi.basisFun_apply K (Fin n)
  · exact Pi.basisFun_repr K (Fin n)

theorem coordinate_expansion : Specs.D05.M02.Examples.coordinate_expansion := by
  intro K _ n x
  simpa only [D05.Specs.FormalPolynomials.coordinateBasisValue, Pi.basisFun_apply] using
    D05.Foundations.FormalPolynomials.coordinateExpansion K n x

theorem coordinate_dimension : Specs.D05.M02.Examples.coordinate_dimension := by
  intro K _ n
  exact ⟨(Pi.basisFun K (Fin n)).finiteDimensional_of_finite,
    by simpa only [Fintype.card_fin] using
      Module.finrank_eq_card_basis (Pi.basisFun K (Fin n))⟩

theorem matrix_basis : Specs.D05.M02.Examples.matrix_basis := by
  intro K _ m n
  refine ⟨Matrix.stdBasis K (Fin m) (Fin n), ?_, ?_⟩
  · intro ij
    exact Matrix.stdBasis_eq_single K ij.1 ij.2
  · intro A ij
    rfl

theorem matrix_expansion : Specs.D05.M02.Examples.matrix_expansion := by
  intro K _ m n A
  obtain ⟨b, hb, hr⟩ := matrix_basis K m n
  simpa only [hr, hb] using (b.sum_repr A).symm

theorem matrix_dimension : Specs.D05.M02.Examples.matrix_dimension := by
  intro K _ m n
  let b := Matrix.stdBasis K (Fin m) (Fin n)
  exact ⟨b.finiteDimensional_of_finite, by simpa using Module.finrank_eq_card_basis b⟩

theorem degree_bound : Specs.D05.M02.Examples.degree_bound := by
  intro K _ d p
  exact ⟨by rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE],
    (Polynomial.degreeLT K (d + 1)).zero_mem⟩

theorem bounded_polynomial_basis : Specs.D05.M02.Examples.bounded_polynomial_basis := by
  intro K _ d
  exact ⟨Polynomial.degreeLT.basis K (d + 1), Polynomial.degreeLT.basis_val,
    fun p i => Polynomial.degreeLT.basis_repr i p⟩

theorem bounded_polynomial_expansion :
    Specs.D05.M02.Examples.bounded_polynomial_expansion := by
  intro K _ d p
  obtain ⟨b, hb, hr⟩ := bounded_polynomial_basis K d
  have h := congrArg (fun q : Polynomial.degreeLT K (d + 1) => (q : Polynomial K))
    (b.sum_repr p).symm
  simpa only [Submodule.coe_sum, Submodule.coe_smul, hr, hb] using h

theorem bounded_polynomial_dimension :
    Specs.D05.M02.Examples.bounded_polynomial_dimension := by
  intro K _ d
  let b := Polynomial.degreeLT.basis K (d + 1)
  exact ⟨b.finiteDimensional_of_finite, by simpa using Module.finrank_eq_card_basis b⟩

theorem monomials_independent : Specs.D05.M02.Examples.monomials_independent := by
  intro K _
  simpa only [Polynomial.coe_basisMonomials, ← Polynomial.X_pow_eq_monomial] using
    (Polynomial.basisMonomials K).linearIndependent

theorem polynomial_infinite_dimensional :
    Specs.D05.M02.Examples.polynomial_infinite_dimensional := by
  intro K _ h
  have := h
  exact Module.Finite.not_linearIndependent_of_infinite _ (monomials_independent K)

theorem standard_sequences_independent :
    Specs.D05.M02.Examples.standard_sequences_independent := by
  intro K _
  exact Pi.linearIndependent_single_one ℕ K

theorem sequences_infinite_dimensional :
    Specs.D05.M02.Examples.sequences_infinite_dimensional := by
  intro K _ h
  have := h
  exact Module.Finite.not_linearIndependent_of_infinite _ (standard_sequences_independent K)

theorem finite_field_evaluation : Specs.D05.M02.Examples.finite_field_evaluation := by
  intro K _ _
  have hn := FiniteField.X_pow_card_sub_X_ne_zero K (p := Fintype.card K)
    Fintype.one_lt_card
  have he : ∀ a : K, Polynomial.eval a
      (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K) = 0 := by
    intro a
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      FiniteField.pow_card, sub_self]
  refine ⟨hn, he, ?_⟩
  intro hi
  apply hn
  apply hi
  funext a
  exact (he a).trans Polynomial.eval_zero.symm

end D05.M02.Examples
