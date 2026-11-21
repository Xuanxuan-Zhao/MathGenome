import MathGenome.Internal.D05.M02.Basis
import MathGenome.Internal.D05.M04.MatrixOfMap
import MathGenome.Internal.D05.M09.Eigenspace
import MathGenome.Internal.Specs.D05.M09.Diagonalizable

/-! K05.09.diagonalizable: an eigenbasis is precisely a diagonal basis matrix. -/

namespace D05.M09.Diagonalizable

/-- Diagonalization is over the given field, including an empty eigenbasis. -/
def diagonalizable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) : Prop :=
  ∃ (n : ℕ) (b : Module.Basis (Fin n) K V) (μ : Fin n → K),
    ∀ i, T (b i) = μ i • b i

theorem coordinate_column : Specs.D05.M09.Diagonalizable.coordinate_column := by
  intro K V _ _ _ n b T μ h j
  rw [h j, map_smul, b.repr_self]

theorem eigenbasis_iff_hasEigenvector :
    Specs.D05.M09.Diagonalizable.eigenbasis_iff_hasEigenvector := by
  intro K V _ _ _ n b T μ
  simp only [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  constructor
  · intro h i
    exact ⟨h i, b.ne_zero i⟩
  · intro h i
    exact (h i).1

theorem matrix_eq_diagonal_iff :
    Specs.D05.M09.Diagonalizable.matrix_eq_diagonal_iff := by
  intro K V _ _ _ n b T μ
  constructor
  · intro h j
    apply b.repr.injective
    ext i
    have hij := congrFun (congrFun h i) j
    simp only [Specs.D05.M04.MatrixOfMap.matrixOfMap_value,
      LinearMap.toMatrix_apply] at hij
    rw [hij]
    by_cases heq : i = j <;>
      simp [Matrix.diagonal_apply, Finsupp.single_apply, heq, eq_comm]
  · intro h
    ext i j
    change LinearMap.toMatrix b b T i j = Matrix.diagonal μ i j
    rw [LinearMap.toMatrix_apply, coordinate_column b T μ h j]
    by_cases heq : i = j <;>
      simp [Matrix.diagonal_apply, Finsupp.single_apply, heq, eq_comm]

theorem diagonalizable_iff_diagonal_matrix :
    Specs.D05.M09.Diagonalizable.diagonalizable_iff_diagonal_matrix := by
  intro K V _ _ _ _ T
  constructor
  · rintro ⟨n, b, μ, h⟩
    exact ⟨n, b, μ, (matrix_eq_diagonal_iff b T μ).mpr h⟩
  · rintro ⟨n, b, μ, h⟩
    exact ⟨n, b, μ, (matrix_eq_diagonal_iff b T μ).mp h⟩

theorem empty_basis_diagonalizes :
    Specs.D05.M09.Diagonalizable.empty_basis_diagonalizes := by
  intro K V _ _ _ _ T
  let b : Module.Basis (Fin 0) K V := Module.Basis.empty V
  have h : ∀ i, T (b i) = (0 : K) • b i := fun i => Fin.elim0 i
  exact ⟨b, h, (matrix_eq_diagonal_iff b T (fun _ => 0)).mpr h⟩

theorem zero_space_diagonalizable :
    Specs.D05.M09.Diagonalizable.zero_space_diagonalizable := by
  intro K V _ _ _ _ _ T
  obtain ⟨b, h, _⟩ := empty_basis_diagonalizes T
  refine ⟨?_, 0, b, (fun _ => 0), h⟩
  ext x
  exact Subsingleton.elim _ _

end D05.M09.Diagonalizable
