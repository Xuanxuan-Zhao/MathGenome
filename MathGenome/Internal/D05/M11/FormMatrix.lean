import MathGenome.Internal.Specs.D05.M11.FormMatrix
import MathGenome.Internal.D05.M04.ChangeBasis
import MathGenome.Internal.D05.M11.Bilinear
import Mathlib.Tactic.NormNum

/-! Matrices of arbitrary bilinear forms and congruence, K05.11.form_matrix. -/
namespace D05.M11.FormMatrix

open Matrix Module
open Specs.D05.M11.FormMatrix

/-- The entries are the form's values on ordered pairs of basis vectors. -/
noncomputable def formMatrix {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) :
    Matrix (Fin n) (Fin n) K := fun i j => B (b i) (b j)

theorem matrix_entry : Specs.D05.M11.FormMatrix.matrix_entry := by
  intro K V _ _ _ n b B i j
  rfl

theorem matrix_eq_toMatrix : Specs.D05.M11.FormMatrix.matrix_eq_toMatrix := by
  intro K V _ _ _ n b B
  ext i j
  exact (B.toMatrix_apply b i j).symm

theorem coordinate_evaluation : Specs.D05.M11.FormMatrix.coordinate_evaluation := by
  intro K V _ _ _ n b B x y
  rw [matrix_eq_toMatrix]
  exact B.apply_eq_dotProduct_toMatrix_mulVec b x y

theorem change_matrix_entry : Specs.D05.M11.FormMatrix.change_matrix_entry := by
  intro K V _ _ _ n b b' i j
  exact LinearMap.toMatrix_apply b' b LinearMap.id i j

theorem coordinate_conversion : Specs.D05.M11.FormMatrix.coordinate_conversion := by
  intro K V _ _ _ n b b' x
  simpa using (D05.M04.ChangeBasis.conversion_action b b'
    (Specs.D05.M04.Coordinates.coordinates_value b' x)).symm

theorem change_of_basis : Specs.D05.M11.FormMatrix.change_of_basis := by
  intro K V _ _ _ n b b' B
  rw [matrix_eq_toMatrix, matrix_eq_toMatrix]
  change B.toMatrix b' = (LinearMap.toMatrix b' b LinearMap.id)ᵀ *
    B.toMatrix b * LinearMap.toMatrix b' b LinearMap.id
  simpa using (B.toMatrix_comp b b' LinearMap.id LinearMap.id)

theorem substituted_evaluation : Specs.D05.M11.FormMatrix.substituted_evaluation := by
  intro K V _ _ _ n b b' B x' y'
  rw [← change_of_basis b b' B, matrix_eq_toMatrix]
  exact (B.dotProduct_toMatrix_mulVec b' x' y').symm

theorem real_one_dimensional_congruence :
    Specs.D05.M11.FormMatrix.real_one_dimensional_congruence := by
  dsimp [Specs.D05.M11.FormMatrix.real_one_dimensional_congruence]
  constructor
  · refine ⟨⟨Matrix.of (fun _ _ => 2), Matrix.of (fun _ _ => 1 / 2), ?_, ?_⟩, rfl⟩ <;>
      ext i j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply, Subsingleton.elim i j]
  · ext i j
    norm_num [Matrix.mul_apply, Fin.sum_univ_one]

theorem real_one_dimensional_not_similar :
    Specs.D05.M11.FormMatrix.real_one_dimensional_not_similar := by
  dsimp [Specs.D05.M11.FormMatrix.real_one_dimensional_not_similar]
  rintro ⟨Q, hQ, heq⟩
  have hA : Matrix.of (fun (_ _ : Fin 1) => (1 : ℝ)) = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    simp [Matrix.one_apply, Subsingleton.elim i j]
  rw [hA, Matrix.mul_one, Matrix.nonsing_inv_mul Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)] at heq
  have h := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) heq
  norm_num at h

end D05.M11.FormMatrix
