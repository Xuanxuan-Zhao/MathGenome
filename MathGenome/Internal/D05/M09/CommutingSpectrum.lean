import MathGenome.Internal.Specs.D05.M09.CommutingSpectrum
import MathGenome.Internal.D05.M10.SimultaneousTriangular
import MathGenome.Internal.D05.Foundations.Fta
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! Spectra of sums and products in a common triangular basis. Complex splitting
comes from the upstream FTA; simultaneous triangularization supplies the basis.
The polynomial factorizations record algebraic multiplicity, including dimension zero. -/

noncomputable section
open Polynomial
namespace D05.M09.CommutingSpectrum

/-- All off-diagonal summands have a factor strictly below a diagonal. -/
theorem upper_triangular_mul_diagonal {K : Type*} [Field K] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) K}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

/-- A factorization into linear factors lists precisely the eigenvalues,
including repetitions in the characteristic polynomial. -/
theorem eigenvalues_of_factorization {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {n : ℕ} (U : Module.End K V) (d : Fin n → K)
    (h : U.charpoly = ∏ i, (X - C (d i))) (μ : K) :
    U.HasEigenvalue μ ↔ ∃ i, μ = d i := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, h]
  simp [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

theorem paired_in_basis : Specs.D05.M09.CommutingSpectrum.paired_in_basis := by
  intro K V _ _ _ _ n b S T hS hT
  let A := LinearMap.toMatrix b b S
  let B := LinearMap.toMatrix b b T
  have hsum : (LinearMap.toMatrix b b (S + T)).IsUpperTriangular := by
    simpa only [map_add] using hS.add hT
  have hprod : (LinearMap.toMatrix b b (S * T)).IsUpperTriangular := by
    simpa only [LinearMap.toMatrix_mul] using hS.mul hT
  have hadd (i : Fin n) : LinearMap.toMatrix b b (S + T) i i = A i i + B i i := by
    simp [A, B]
  have hmul (i : Fin n) : LinearMap.toMatrix b b (S * T) i i = A i i * B i i := by
    rw [LinearMap.toMatrix_mul]
    exact upper_triangular_mul_diagonal hS hT i
  have hc (U : Module.End K V) (hu : (LinearMap.toMatrix b b U).IsUpperTriangular) :
      U.charpoly = ∏ i, (X - C (LinearMap.toMatrix b b U i i)) := by
    rw [← LinearMap.charpoly_toMatrix U b]
    exact Matrix.charpoly_of_isUpperTriangular _ hu
  have hcS := hc S hS
  have hcT := hc T hT
  have hcadd : (S + T).charpoly = ∏ i, (X - C (A i i + B i i)) := by
    simpa only [hadd] using hc (S + T) hsum
  have hcmul : (S * T).charpoly = ∏ i, (X - C (A i i * B i i)) := by
    simpa only [hmul] using hc (S * T) hprod
  exact ⟨hS, hT, hadd, hmul, hcS, hcT, hcadd, hcmul,
    eigenvalues_of_factorization S _ hcS, eigenvalues_of_factorization T _ hcT,
    eigenvalues_of_factorization (S + T) _ hcadd,
    eigenvalues_of_factorization (S * T) _ hcmul⟩

theorem commuting_spectrum : Specs.D05.M09.CommutingSpectrum.commuting_spectrum := by
  intro V _ _ _ S T hST
  let F : Bool → Module.End ℂ V := fun i => if i then T else S
  have hc : Pairwise fun i j => Commute (F i) (F j) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hST
    · exact hST.symm
    · exact (hij rfl).elim
  have ht (i : Bool) : Specs.D05.M10.Triangularization.HasUpperTriangularBasis (F i) :=
    D05.M10.Triangularization.triangularization (F i) |>.1.mpr
      (D05.Foundations.Fta.splits _)
  obtain ⟨n, b, hb⟩ := D05.M10.SimultaneousTriangular.finite_simultaneous_triangular F hc ht
  exact ⟨n, b, paired_in_basis b S T (hb false) (hb true)⟩

open Specs.D05.M09.CommutingSpectrum (diagonalExample) in
theorem arbitrary_pairing_counterexample :
    Specs.D05.M09.CommutingSpectrum.arbitrary_pairing_counterexample := by
  refine ⟨Commute.refl _, ?_, ?_, ?_⟩
  · rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    simp [diagonalExample, Matrix.charpoly_toLin', Matrix.charpoly_diagonal,
      Fin.prod_univ_two, Polynomial.IsRoot]
  · rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    simp [diagonalExample, Matrix.charpoly_toLin', Matrix.charpoly_diagonal,
      Fin.prod_univ_two, Polynomial.IsRoot]
  · rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
      ← LinearMap.charpoly_toMatrix (diagonalExample + diagonalExample) (Pi.basisFun ℂ (Fin 2))]
    simp [diagonalExample, LinearMap.toMatrix_eq_toMatrix', ← map_add,
      Matrix.charpoly_fin_two, Polynomial.IsRoot]

end D05.M09.CommutingSpectrum
