import MathGenome.Internal.Specs.D05.M04.InverseMatrix
import MathGenome.Internal.D05.M04.Composition

/-! Inverse matrices and inverse linear maps, K05.04.inverse_matrix. -/

namespace D05.M04.InverseMatrix

open Specs.D05.M04.MatrixOfMap

theorem coordinate_inverse_iff :
    Specs.D05.M04.InverseMatrix.coordinate_inverse_iff := by
  intro R _ n m A B
  constructor
  · rintro ⟨hBA, hAB⟩
    constructor
    · change B.mulVecLin.comp A.mulVecLin = LinearMap.id
      rw [← Matrix.mulVecLin_mul, hBA, Matrix.mulVecLin_one]
    · change A.mulVecLin.comp B.mulVecLin = LinearMap.id
      rw [← Matrix.mulVecLin_mul, hAB, Matrix.mulVecLin_one]
  · rintro ⟨hBA, hAB⟩
    constructor
    · apply Matrix.toLin'.injective
      change (B * A).mulVecLin = (1 : Matrix (Fin n) (Fin n) R).mulVecLin
      rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_one]
      exact hBA
    · apply Matrix.toLin'.injective
      change (A * B).mulVecLin = (1 : Matrix (Fin m) (Fin m) R).mulVecLin
      rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_one]
      exact hAB

theorem rectangular_inverse_iff_bijective :
    Specs.D05.M04.InverseMatrix.rectangular_inverse_iff_bijective := by
  intro R _ n m A
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨hBA, hAB⟩ := (coordinate_inverse_iff A B).mp hB
    have hleft : Function.LeftInverse (coordinateLinearMap_value B)
        (coordinateLinearMap_value A) := fun x =>
      congrArg (fun f : (Fin n → R) →ₗ[R] (Fin n → R) => f x) hBA
    have hright : Function.RightInverse (coordinateLinearMap_value B)
        (coordinateLinearMap_value A) := fun y =>
      congrArg (fun f : (Fin m → R) →ₗ[R] (Fin m → R) => f y) hAB
    exact ⟨hleft.injective, hright.surjective⟩
  · intro hA
    let e := LinearEquiv.ofBijective (coordinateLinearMap_value A) hA
    let B := LinearMap.toMatrix' e.symm.toLinearMap
    have hB : coordinateLinearMap_value B = e.symm.toLinearMap :=
      Matrix.toLin'_toMatrix' _
    refine ⟨B, (coordinate_inverse_iff A B).mpr ?_⟩
    rw [hB]
    exact ⟨e.symm_comp, e.comp_symm⟩

theorem inverse_iff_bijective :
    Specs.D05.M04.InverseMatrix.inverse_iff_bijective := by
  intro R _ n A
  exact rectangular_inverse_iff_bijective A

theorem inverse_unique : Specs.D05.M04.InverseMatrix.inverse_unique := by
  intro R _ n m A B C hBA hAC
  calc
    B = B * 1 := (Matrix.mul_one B).symm
    _ = B * (A * C) := congrArg (B * ·) hAC.symm
    _ = (B * A) * C := (Matrix.mul_assoc B A C).symm
    _ = C := by rw [hBA, Matrix.one_mul]

theorem inverse_exists_unique :
    Specs.D05.M04.InverseMatrix.inverse_exists_unique := by
  intro R _ n A hA
  obtain ⟨B, hBA, hAB⟩ := (inverse_iff_bijective A).mpr hA
  refine ⟨B, ⟨hBA, hAB⟩, ?_⟩
  intro C hC
  exact inverse_unique A C B hC.1 hAB

/-- Equality to the identity matrix reflects equality to the identity map. -/
theorem matrix_eq_one_iff {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {n : ℕ} (b : Module.Basis (Fin n) R V) (T : V →ₗ[R] V) :
    matrixOfMap_value b b T = 1 ↔ T = LinearMap.id := by
  change LinearMap.toMatrix b b T = 1 ↔ T = LinearMap.id
  rw [← LinearMap.toMatrix_id b]
  exact (LinearMap.toMatrix b b).injective.eq_iff

theorem matrix_inverse_iff : Specs.D05.M04.InverseMatrix.matrix_inverse_iff := by
  intro R V W _ _ _ _ _ n m b c T S
  rw [← D05.M04.Composition.matrix_comp b c b S T,
    ← D05.M04.Composition.matrix_comp c b c T S,
    matrix_eq_one_iff, matrix_eq_one_iff]

theorem matrix_of_inverse : Specs.D05.M04.InverseMatrix.matrix_of_inverse := by
  intro R V W _ _ _ _ _ n m b c e
  exact (matrix_inverse_iff b c e.toLinearMap e.symm.toLinearMap).mpr
    ⟨e.symm_comp, e.comp_symm⟩

theorem inverse_matrix : Specs.D05.M04.InverseMatrix.inverse_matrix := by
  intro R V W _ _ _ _ _ n b c e
  exact Matrix.inv_eq_left_inv (matrix_of_inverse b c e).1

theorem inverse_represents : Specs.D05.M04.InverseMatrix.inverse_represents := by
  intro R _ n A hA
  let e := LinearEquiv.ofBijective (coordinateLinearMap_value A) hA
  let B := LinearMap.toMatrix' e.symm.toLinearMap
  have hB : coordinateLinearMap_value B = e.symm.toLinearMap :=
    Matrix.toLin'_toMatrix' _
  have hBA : B * A = 1 :=
    ((coordinate_inverse_iff A B).mpr (by rw [hB]; exact ⟨e.symm_comp, e.comp_symm⟩)).1
  refine ⟨e, rfl, ?_⟩
  rw [Matrix.inv_eq_left_inv hBA, hB]

theorem left_inverse_is_right : Specs.D05.M04.InverseMatrix.left_inverse_is_right := by
  intro R _ n A B hBA
  exact mul_eq_one_comm.mp hBA

theorem right_inverse_is_left : Specs.D05.M04.InverseMatrix.right_inverse_is_left := by
  intro R _ n A B hAB
  exact mul_eq_one_comm.mp hAB

end D05.M04.InverseMatrix
