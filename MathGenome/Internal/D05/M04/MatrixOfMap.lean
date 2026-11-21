import MathGenome.Internal.Specs.D05.M04.MatrixOfMap
import MathGenome.Internal.D05.M04.Coordinates
import MathGenome.Internal.D05.M04.MatrixProduct
import MathGenome.Internal.D05.M03.BasisExtension

/-! The matrix/map correspondence for K05.04.matrix_of_map. -/

namespace D05.M04.MatrixOfMap

open Matrix

/-- Codomain coordinates of the images of the ordered domain basis vectors. -/
noncomputable def matrixOfMap {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {n m : ℕ} (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin m) R W)
    (T : V →ₗ[R] W) : Matrix (Fin m) (Fin n) R :=
  LinearMap.toMatrix b c T

/-- Row-by-column multiplication, bundled with its linearity. -/
def coordinateLinearMap {R : Type*} [CommRing R] {n m : ℕ}
    (A : Matrix (Fin m) (Fin n) R) : (Fin n → R) →ₗ[R] (Fin m → R) :=
  A.mulVecLin

/-- Matrix action transported through the two basis coordinate isomorphisms. -/
noncomputable def mapOfMatrix {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {n m : ℕ} (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin m) R W)
    (A : Matrix (Fin m) (Fin n) R) : V →ₗ[R] W :=
  Matrix.toLin b c A

theorem matrix_entry : Specs.D05.M04.MatrixOfMap.matrix_entry := by
  intro R V W _ _ _ _ _ n m b c T i j
  exact LinearMap.toMatrix_apply b c T i j

theorem basis_image : Specs.D05.M04.MatrixOfMap.basis_image := by
  intro R V W _ _ _ _ _ n m b c T j
  simp only [Specs.D05.M04.MatrixOfMap.matrixOfMap_value, LinearMap.toMatrix_apply]
  exact (c.sum_repr (T (b j))).symm

theorem image_linear_combination :
    Specs.D05.M04.MatrixOfMap.image_linear_combination := by
  intro R V W _ _ _ _ _ n m b c T x
  change T (∑ j, x j • b j) =
    ∑ i, (∑ j, LinearMap.toMatrix b c T i j * x j) • c i
  have h := Matrix.toLin_apply b c (LinearMap.toMatrix b c T) (∑ j, x j • b j)
  rw [Matrix.toLin_toMatrix] at h
  simpa only [b.repr_sum_self, Matrix.mulVec, dotProduct] using h

theorem coordinates_image : Specs.D05.M04.MatrixOfMap.coordinates_image := by
  intro K V W _ _ _ _ _ n m b c T v
  exact (LinearMap.toMatrix_mulVec_repr b c T v).symm

theorem unique_matrix_from_basis :
    Specs.D05.M04.MatrixOfMap.unique_matrix_from_basis := by
  intro R V W _ _ _ _ _ n m b c T A h
  apply Matrix.ext
  intro i j
  have hj := congrArg (fun w => c.repr w i) (h j)
  rw [c.repr_sum_self] at hj
  exact hj.symm.trans (LinearMap.toMatrix_apply b c T i j).symm

theorem unique_matrix_from_coordinates :
    Specs.D05.M04.MatrixOfMap.unique_matrix_from_coordinates := by
  intro K V W _ _ _ _ _ n m b c T A h
  apply Matrix.mulVec_injective
  funext x
  let v := (Specs.D05.M04.Coordinates.coordinates_value b).symm x
  have hx : Specs.D05.M04.Coordinates.coordinates_value b v = x :=
    b.equivFun.apply_symm_apply x
  have hv := (h v).symm.trans (coordinates_image b c T v)
  simpa only [hx] using hv

theorem coordinateLinearMap_apply :
    Specs.D05.M04.MatrixOfMap.coordinateLinearMap_apply := by
  intro R _ n m A x i
  rfl

theorem coordinateLinearMap_unique :
    Specs.D05.M04.MatrixOfMap.coordinateLinearMap_unique := by
  intro R _ n m A
  refine ⟨coordinateLinearMap A, coordinateLinearMap_apply A, ?_⟩
  intro F hF
  apply LinearMap.ext
  intro x
  funext i
  exact hF x i

theorem mapOfMatrix_apply : Specs.D05.M04.MatrixOfMap.mapOfMatrix_apply := by
  intro R V W _ _ _ _ _ n m b c A v
  exact Matrix.toLin_apply b c A v

theorem mapOfMatrix_coordinates :
    Specs.D05.M04.MatrixOfMap.mapOfMatrix_coordinates := by
  intro K V W _ _ _ _ _ n m b c A v
  exact Matrix.repr_toLin b c A v

theorem matrixOfMap_mapOfMatrix :
    Specs.D05.M04.MatrixOfMap.matrixOfMap_mapOfMatrix := by
  intro R V W _ _ _ _ _ n m b c A
  exact LinearMap.toMatrix_toLin b c A

theorem mapOfMatrix_matrixOfMap :
    Specs.D05.M04.MatrixOfMap.mapOfMatrix_matrixOfMap := by
  intro R V W _ _ _ _ _ n m b c T
  exact Matrix.toLin_toMatrix b c T

theorem exists_unique_map : Specs.D05.M04.MatrixOfMap.exists_unique_map := by
  intro K V W _ _ _ _ _ n m b c A
  refine ⟨mapOfMatrix b c A, mapOfMatrix_coordinates b c A, ?_⟩
  intro T hT
  have hA := unique_matrix_from_coordinates b c T A hT
  calc
    T = Matrix.toLin b c (LinearMap.toMatrix b c T) :=
      (Matrix.toLin_toMatrix b c T).symm
    _ = mapOfMatrix b c A := congrArg (Matrix.toLin b c) hA.symm

end D05.M04.MatrixOfMap
