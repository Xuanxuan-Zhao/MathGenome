import Mathlib.LinearAlgebra.Matrix.ToLin
import MathGenome.Internal.Specs.D05.M04.Coordinates
import MathGenome.Internal.Specs.D05.M04.MatrixProduct
import MathGenome.Internal.Specs.D05.M03.BasisExtension

/-!
Independent specifications for K05.04.matrix_of_map, paper.tex:625–628.
`Fin n` indexes the ordered domain basis and `Fin m` the ordered codomain
basis. Columns are functions, and matrix action is `Matrix.mulVec`.
No size is assumed positive. The constructions and finite-sum assertions
are also valid for based modules over a commutative ring; the coordinate
identity over a field uses the accepted coordinate isomorphism verbatim.
-/

namespace Specs.D05.M04.MatrixOfMap

open Matrix

universe u v w

/-- Type of the matrix construction, with codomain rows and domain columns. -/
def matrixOfMap_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  {R : Type u} → {V : Type v} → {W : Type w} →
  [CommRing R] → [AddCommGroup V] → [Module R V] →
  [AddCommGroup W] → [Module R W] → {n m : ℕ} →
  Module.Basis (Fin n) R V → Module.Basis (Fin m) R W →
  (V →ₗ[R] W) → Matrix (Fin m) (Fin n) R

noncomputable def matrixOfMap_value : matrixOfMap_type.{u, v, w} :=
  fun b c T => LinearMap.toMatrix b c T

/-- Every rectangular matrix acts linearly on coordinate columns. -/
def coordinateLinearMap_type : Type (u + 1) :=
  {R : Type u} → [CommRing R] → {n m : ℕ} →
  Matrix (Fin m) (Fin n) R → ((Fin n → R) →ₗ[R] (Fin m → R))

def coordinateLinearMap_value : coordinateLinearMap_type.{u} :=
  fun A => A.mulVecLin

/-- Type of the inverse construction, with the same two ordered bases. -/
def mapOfMatrix_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  {R : Type u} → {V : Type v} → {W : Type w} →
  [CommRing R] → [AddCommGroup V] → [Module R V] →
  [AddCommGroup W] → [Module R W] → {n m : ℕ} →
  Module.Basis (Fin n) R V → Module.Basis (Fin m) R W →
  Matrix (Fin m) (Fin n) R → (V →ₗ[R] W)

noncomputable def mapOfMatrix_value : mapOfMatrix_type.{u, v, w} :=
  fun b c A => Matrix.toLin b c A

/-- Entry `(i,j)` is coefficient `i` of the image of domain vector `j`. -/
def matrix_entry : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m : ℕ}
    (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin m) R W)
    (T : V →ₗ[R] W) (i : Fin m) (j : Fin n),
    matrixOfMap_value b c T i j = c.repr (T (b j)) i

/-- The defining column expansion of the paper. -/
def basis_image : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m : ℕ}
    (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin m) R W)
    (T : V →ₗ[R] W) (j : Fin n),
    T (b j) = ∑ i, matrixOfMap_value b c T i j • c i

/-- Applying the map to an arbitrary expansion gives the row-by-column sums. -/
def image_linear_combination : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m : ℕ}
    (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin m) R W)
    (T : V →ₗ[R] W) (x : Fin n → R),
    T (∑ j, x j • b j) =
      ∑ i, (∑ j, matrixOfMap_value b c T i j * x j) • c i

/-- The accepted coordinate maps intertwine `T` with its matrix action. -/
def coordinates_image : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (T : V →ₗ[K] W) (v : V),
    Coordinates.coordinates_value c (T v) =
      matrixOfMap_value b c T *ᵥ Coordinates.coordinates_value b v

/-- The column expansion uniquely determines the matrix. -/
def unique_matrix_from_basis : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m : ℕ}
    (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin m) R W)
    (T : V →ₗ[R] W) (A : Matrix (Fin m) (Fin n) R),
    (∀ j, T (b j) = ∑ i, A i j • c i) → A = matrixOfMap_value b c T

/-- The coordinate identity for all vectors uniquely determines the matrix. -/
def unique_matrix_from_coordinates : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (T : V →ₗ[K] W) (A : Matrix (Fin m) (Fin n) K),
    (∀ v, Coordinates.coordinates_value c (T v) =
      A *ᵥ Coordinates.coordinates_value b v) → A = matrixOfMap_value b c T

/-- The coordinate-space map has exactly the paper's entry formula. -/
def coordinateLinearMap_apply : Prop :=
  ∀ {R : Type*} [CommRing R] {n m : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (x : Fin n → R) (i : Fin m),
    coordinateLinearMap_value A x i = ∑ j, A i j * x j

def coordinateLinearMap_unique : Prop :=
  ∀ {R : Type*} [CommRing R] {n m : ℕ}
    (A : Matrix (Fin m) (Fin n) R),
    ∃! F : (Fin n → R) →ₗ[R] (Fin m → R),
      ∀ x i, F x i = ∑ j, A i j * x j

/-- Transporting matrix action back to the given spaces gives this sum. -/
def mapOfMatrix_apply : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m : ℕ}
    (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin m) R W)
    (A : Matrix (Fin m) (Fin n) R) (v : V),
    mapOfMatrix_value b c A v = ∑ i, (∑ j, A i j * b.repr v j) • c i

def mapOfMatrix_coordinates : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (A : Matrix (Fin m) (Fin n) K) (v : V),
    Coordinates.coordinates_value c (mapOfMatrix_value b c A v) =
      coordinateLinearMap_value A (Coordinates.coordinates_value b v)

/-- Starting with any matrix recovers that very matrix. -/
def matrixOfMap_mapOfMatrix : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m : ℕ}
    (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin m) R W)
    (A : Matrix (Fin m) (Fin n) R),
    matrixOfMap_value b c (mapOfMatrix_value b c A) = A

/-- Starting with any linear map recovers that very map. -/
def mapOfMatrix_matrixOfMap : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m : ℕ}
    (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin m) R W)
    (T : V →ₗ[R] W),
    mapOfMatrix_value b c (matrixOfMap_value b c T) = T

/-- Every matrix represents exactly one map between the given based spaces. -/
def exists_unique_map : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (A : Matrix (Fin m) (Fin n) K),
    ∃! T : V →ₗ[K] W, ∀ v, Coordinates.coordinates_value c (T v) =
      A *ᵥ Coordinates.coordinates_value b v

end Specs.D05.M04.MatrixOfMap
