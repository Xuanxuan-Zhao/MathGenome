import MathGenome.Internal.Specs.D05.M04.ChangeBasis
import MathGenome.Internal.D05.M04.InverseMatrix

/-! Independent domain and codomain basis changes, K05.04.change_basis. -/

namespace D05.M04.ChangeBasis

open Matrix
open Specs.D05.M04.MatrixOfMap
open Specs.D05.M04.ChangeBasis

/-- Convert new coordinates to old coordinates via the identity map. -/
noncomputable def changeMatrix {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] {n : ℕ}
    (b b' : Module.Basis (Fin n) R V) : Matrix (Fin n) (Fin n) R :=
  matrixOfMap_value b' b LinearMap.id

theorem conversion_action : Specs.D05.M04.ChangeBasis.conversion_action := by
  intro K V _ _ _ n b b' x
  have h := D05.M04.Composition.identity_coordinates b' b
  exact congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f x) h

theorem conversion_inverse : Specs.D05.M04.ChangeBasis.conversion_inverse := by
  intro R V _ _ _ n b b'
  exact (D05.M04.InverseMatrix.matrix_inverse_iff b' b LinearMap.id LinearMap.id).mpr
    ⟨LinearMap.id_comp _, LinearMap.id_comp _⟩

theorem conversion_isUnit : Specs.D05.M04.ChangeBasis.conversion_isUnit := by
  intro R V _ _ _ n b b'
  obtain ⟨hleft, hright⟩ := conversion_inverse b b'
  exact ⟨⟨changeMatrix_value b b', changeMatrix_value b' b, hright, hleft⟩, rfl⟩

theorem conversion_nonsingular_inverse :
    Specs.D05.M04.ChangeBasis.conversion_nonsingular_inverse := by
  intro R V _ _ _ n b b'
  exact Matrix.inv_eq_left_inv (conversion_inverse b b').1

theorem matrix_commutes : Specs.D05.M04.ChangeBasis.matrix_commutes := by
  intro R V W _ _ _ _ _ n m b b' c c' T
  change matrixOfMap_value c' c LinearMap.id * matrixOfMap_value b' c' T =
    matrixOfMap_value b c T * matrixOfMap_value b' b LinearMap.id
  rw [← D05.M04.Composition.matrix_comp b' c' c,
    ← D05.M04.Composition.matrix_comp b' b c,
    LinearMap.id_comp, LinearMap.comp_id]

theorem column_commutes : Specs.D05.M04.ChangeBasis.column_commutes := by
  intro R V W _ _ _ _ _ n m b b' c c' T x
  simpa only [Matrix.mulVec_mulVec] using
    congrArg (fun A : Matrix (Fin m) (Fin n) R => A *ᵥ x)
      (matrix_commutes b b' c c' T)

theorem change_basis : Specs.D05.M04.ChangeBasis.change_basis := by
  intro R V W _ _ _ _ _ n m b b' c c' T
  rw [conversion_nonsingular_inverse c c']
  calc
    matrixOfMap_value b' c' T =
        (changeMatrix_value c' c * changeMatrix_value c c') * matrixOfMap_value b' c' T := by
      rw [(conversion_inverse c c').1, Matrix.one_mul]
    _ = changeMatrix_value c' c * (matrixOfMap_value b c T * changeMatrix_value b b') := by
      rw [Matrix.mul_assoc, matrix_commutes b b' c c' T]
    _ = _ := (Matrix.mul_assoc _ _ _).symm

theorem change_basis_iff : Specs.D05.M04.ChangeBasis.change_basis_iff := by
  intro R V W _ _ _ _ _ n m b b' c c' T A'
  constructor
  · intro h
    have hmat : changeMatrix_value c c' * A' =
        matrixOfMap_value b c T * changeMatrix_value b b' := by
      apply Matrix.mulVec_injective
      funext x
      simpa only [Matrix.mulVec_mulVec] using h x
    rw [conversion_nonsingular_inverse c c']
    calc
      A' = (changeMatrix_value c' c * changeMatrix_value c c') * A' := by
        rw [(conversion_inverse c c').1, Matrix.one_mul]
      _ = changeMatrix_value c' c * (matrixOfMap_value b c T * changeMatrix_value b b') := by
        rw [Matrix.mul_assoc, hmat]
      _ = _ := (Matrix.mul_assoc _ _ _).symm
  · intro h
    rw [← change_basis b b' c c' T] at h
    subst A'
    exact column_commutes b b' c c' T

theorem represents_iff : Specs.D05.M04.ChangeBasis.represents_iff := by
  intro K V W _ _ _ _ _ n m b b' c c' T A'
  rw [← change_basis b b' c c' T]
  constructor
  · exact D05.M04.MatrixOfMap.unique_matrix_from_coordinates b' c' T A'
  · rintro rfl
    exact D05.M04.MatrixOfMap.coordinates_image b' c' T

end D05.M04.ChangeBasis
