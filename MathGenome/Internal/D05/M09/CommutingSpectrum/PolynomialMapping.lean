import MathGenome.Internal.Specs.D05.M09.CommutingSpectrum.PolynomialMapping
import MathGenome.Internal.D05.M10.Triangularization
import MathGenome.Internal.D05.M08.EigenRoots
import MathGenome.Internal.D05.M08.Evaluation
import MathGenome.Internal.D05.M09.FieldDependence
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.FinCases

/-! Polynomial spectral mapping over the original field. Splitting supplies an
upper triangular basis through the upstream criterion. Polynomial evaluation
then gives both the characteristic polynomial with multiplicities and the
set of eigenvalues. The final example records the failure over the real field
without splitting. -/

noncomputable section
namespace D05.M09.CommutingSpectrum.PolynomialMapping
open Polynomial Module

/-- In a diagonal entry of a product of upper triangular matrices,
only the summand at the diagonal index survives. -/
theorem triangular_mul_diagonal {K : Type*} [Field K] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) K} (hA : A.IsUpperTriangular)
    (hB : B.IsUpperTriangular) (j : Fin n) :
    (A * B) j j = A j j * B j j := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · intro k _ hkj
    rcases lt_or_gt_of_ne hkj with hlt | hgt
    · rw [hA hlt, zero_mul]
    · rw [hB hgt, mul_zero]
  · simp

/-- Polynomial evaluation preserves triangularity and evaluates each diagonal
entry in the scalar field. -/
theorem triangular_matrix_aeval {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : A.IsUpperTriangular) (p : K[X]) :
    (aeval A p).IsUpperTriangular ∧
    ∀ j, aeval A p j j = p.eval (A j j) := by
  classical
  induction p using Polynomial.induction_on with
  | C a =>
    constructor
    · simpa only [aeval_C] using (Matrix.blockTriangular_algebraMap (b := id) a)
    · intro j
      simp [Matrix.algebraMap_eq_diagonal]
  | add p q hp hq =>
    constructor
    · simpa only [map_add] using hp.1.add hq.1
    · intro j
      simp [hp.2 j, hq.2 j]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc]
    constructor
    · simpa only [map_mul, aeval_X] using ih.1.mul hA
    · intro j
      rw [map_mul, aeval_X, triangular_mul_diagonal ih.1 hA, ih.2 j]
      simp

theorem eigenvector_polynomial :
    Specs.D05.M09.CommutingSpectrum.PolynomialMapping.eigenvector_polynomial := by
  intro K V _ _ _ T p μ v hv
  exact Module.End.aeval_apply_of_mem_apply_eq_smul hv

theorem spectral_inclusion :
    Specs.D05.M09.CommutingSpectrum.PolynomialMapping.spectral_inclusion := by
  rintro K V _ _ _ T p _ ⟨μ, hμ, rfl⟩
  obtain ⟨v, hv, hn⟩ := hμ.exists_hasEigenvector
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr
      (Module.End.aeval_apply_of_hasEigenvector ⟨hv, hn⟩), hn⟩

theorem triangular_polynomial :
    Specs.D05.M09.CommutingSpectrum.PolynomialMapping.triangular_polynomial := by
  intro K V _ _ _ n b T p hT
  have hmap : LinearMap.toMatrix b b (aeval T p) =
      aeval (LinearMap.toMatrix b b T) p :=
    (Polynomial.aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b) T p).symm
  rw [hmap]
  exact triangular_matrix_aeval _ hT p

theorem charpoly_in_triangular_basis :
    Specs.D05.M09.CommutingSpectrum.PolynomialMapping.charpoly_in_triangular_basis := by
  intro K V _ _ _ _ n b T p hT
  obtain ⟨htri, hdiag⟩ := triangular_polynomial b T p hT
  rw [← LinearMap.charpoly_toMatrix (aeval T p) b,
    Matrix.charpoly_of_isUpperTriangular _ htri]
  simp_rw [hdiag]

/-- Roots of the triangular characteristic polynomial are precisely the
listed diagonal scalars; the list is allowed to be empty. -/
theorem eigenvalue_iff_diagonal {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {n : ℕ}
    (b : Basis (Fin n) K V) (T : End K V)
    (hT : (LinearMap.toMatrix b b T).IsUpperTriangular) (μ : K) :
    T.HasEigenvalue μ ↔ ∃ j, μ = LinearMap.toMatrix b b T j j := by
  classical
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
    ← LinearMap.charpoly_toMatrix T b, Matrix.charpoly_of_isUpperTriangular _ hT]
  simp [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

theorem spectral_mapping :
    Specs.D05.M09.CommutingSpectrum.PolynomialMapping.spectral_mapping := by
  intro K V _ _ _ _ T p hs
  classical
  obtain ⟨n, b, hb⟩ := (D05.M10.Triangularization.triangularization T).1.mpr hs
  obtain ⟨htri, hdiag⟩ := triangular_polynomial b T p hb
  apply Set.Subset.antisymm
  · intro μ hμ
    obtain ⟨j, hj⟩ := (eigenvalue_iff_diagonal b (aeval T p) htri μ).mp hμ
    refine ⟨LinearMap.toMatrix b b T j j,
      (eigenvalue_iff_diagonal b T hb _).mpr ⟨j, rfl⟩, ?_⟩
    rw [hj, hdiag]
  · exact spectral_inclusion T p

theorem complex_spectral_mapping :
    Specs.D05.M09.CommutingSpectrum.PolynomialMapping.complex_spectral_mapping := by
  intro V _ _ _ T p
  exact spectral_mapping T p (IsAlgClosed.splits _)

theorem zero_dimensional :
    Specs.D05.M09.CommutingSpectrum.PolynomialMapping.zero_dimensional := by
  intro K V _ _ _ _ T p hd
  refine ⟨D05.M08.Charpoly.zero_dimensional (aeval T p) hd, ?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro μ hμ
  have h := (Module.End.hasEigenvalue_iff_isRoot_charpoly (aeval T p) μ).mp hμ
  have hc : (aeval T p).charpoly = 1 := D05.M08.Charpoly.zero_dimensional (aeval T p) hd
  rw [hc] at h
  simp [Polynomial.IsRoot] at h

theorem rotation_square :
    Specs.D05.M09.CommutingSpectrum.PolynomialMapping.rotation_square := by
  intro K _
  rw [aeval_X_pow]
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;>
    simp [Specs.D05.M09.FieldDependence.rotation,
      Specs.D05.M09.FieldDependence.rotationMatrix, pow_two,
      Module.End.mul_apply, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

theorem rotation_counterexample :
    Specs.D05.M09.CommutingSpectrum.PolynomialMapping.rotation_counterexample := by
  dsimp [Specs.D05.M09.CommutingSpectrum.PolynomialMapping.rotation_counterexample]
  have hR : {μ | (Specs.D05.M09.FieldDependence.rotation ℝ).HasEigenvalue μ} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr D05.M09.FieldDependence.rotation_real_no_eigenvalues
  have hsq := rotation_square ℝ
  have hspec : {μ | (aeval (Specs.D05.M09.FieldDependence.rotation ℝ)
      (X ^ 2 : ℝ[X])).HasEigenvalue μ} = {-1} := by
    rw [hsq]
    ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff,
      Module.End.hasEigenvalue_neg_iff]
    rw [D05.M09.Eigenspace.identity_hasEigenvalue_iff (-μ)]
    exact neg_eq_iff_eq_neg
  refine ⟨hR, hsq, hspec, ?_⟩
  rw [hspec, hR, Set.image_empty]
  exact Set.singleton_ne_empty _

end D05.M09.CommutingSpectrum.PolynomialMapping
