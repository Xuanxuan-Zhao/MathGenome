import MathGenome.Internal.Specs.D05.M04.InverseMatrix

/-!
Independent specification for K05.04.change_basis, paper.tex:652–655.
The old and new bases of each space have the same finite ordered index type.
The domain size `n` and codomain size `m` are independent and may be zero.
`changeMatrix_value b b'` converts NEW (`b'`) coordinates to OLD (`b`)
coordinates, so it represents `c_b ∘ c_b'⁻¹`, not the reverse conversion.
The based-module matrix identities hold over any commutative ring. The
coordinate statements reuse the accepted field-valued coordinate maps.
-/

namespace Specs.D05.M04.ChangeBasis

open Matrix
open MatrixOfMap

universe u v

/-- The square conversion matrix for two ordered bases of the same space. -/
def changeMatrix_type : Type (max (u + 1) (v + 1)) :=
  {R : Type u} → {V : Type v} → [CommRing R] →
  [AddCommGroup V] → [Module R V] → {n : ℕ} →
  Module.Basis (Fin n) R V → Module.Basis (Fin n) R V → Matrix (Fin n) (Fin n) R

/-- The identity map with new input basis and old output basis. -/
noncomputable def changeMatrix_value : changeMatrix_type.{u, v} :=
  fun b b' => matrixOfMap_value b' b LinearMap.id

/-- This is exactly the coordinate conversion specified by the paper. -/
def conversion_action : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b b' : Module.Basis (Fin n) K V) (x : Fin n → K),
    changeMatrix_value b b' *ᵥ x =
      Coordinates.coordinates_value b ((Coordinates.coordinates_value b').symm x)

/-- Reversing the two bases gives a two-sided matrix inverse. -/
def conversion_inverse : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
    (b b' : Module.Basis (Fin n) R V),
    changeMatrix_value b' b * changeMatrix_value b b' = 1 ∧
      changeMatrix_value b b' * changeMatrix_value b' b = 1

/-- Invertibility is a conclusion, without extra hypotheses on the bases. -/
def conversion_isUnit : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
    (b b' : Module.Basis (Fin n) R V), IsUnit (changeMatrix_value b b')

/-- The conventional nonsingular inverse is the reverse conversion. -/
def conversion_nonsingular_inverse : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
    (b b' : Module.Basis (Fin n) R V),
    (changeMatrix_value b b')⁻¹ = changeMatrix_value b' b

/-- `Q A' = A P` for independent domain and codomain basis changes. -/
def matrix_commutes : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m : ℕ}
    (b b' : Module.Basis (Fin n) R V) (c c' : Module.Basis (Fin m) R W)
    (T : V →ₗ[R] W),
    changeMatrix_value c c' * matrixOfMap_value b' c' T =
      matrixOfMap_value b c T * changeMatrix_value b b'

/-- The displayed equality `Q A' x = A P x` holds for every column. -/
def column_commutes : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m : ℕ}
    (b b' : Module.Basis (Fin n) R V) (c c' : Module.Basis (Fin m) R W)
    (T : V →ₗ[R] W) (x : Fin n → R),
    changeMatrix_value c c' *ᵥ (matrixOfMap_value b' c' T *ᵥ x) =
      matrixOfMap_value b c T *ᵥ (changeMatrix_value b b' *ᵥ x)

/-- The full rectangular change-of-basis formula, `A' = Q⁻¹ A P`. -/
def change_basis : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m : ℕ}
    (b b' : Module.Basis (Fin n) R V) (c c' : Module.Basis (Fin m) R W)
    (T : V →ₗ[R] W),
    matrixOfMap_value b' c' T =
      (changeMatrix_value c c')⁻¹ * matrixOfMap_value b c T * changeMatrix_value b b'

/-- For an arbitrary candidate matrix, commuting with the two conversions
is equivalent to the formula; this includes the converse and uniqueness. -/
def change_basis_iff : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m : ℕ}
    (b b' : Module.Basis (Fin n) R V) (c c' : Module.Basis (Fin m) R W)
    (T : V →ₗ[R] W) (A' : Matrix (Fin m) (Fin n) R),
    (∀ x : Fin n → R, changeMatrix_value c c' *ᵥ (A' *ᵥ x) =
      matrixOfMap_value b c T *ᵥ (changeMatrix_value b b' *ᵥ x)) ↔
    A' = (changeMatrix_value c c')⁻¹ * matrixOfMap_value b c T * changeMatrix_value b b'

/-- The formula characterizes precisely the matrices representing `T`
in the new bases, using the original coordinate-map definition. -/
def represents_iff : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b b' : Module.Basis (Fin n) K V) (c c' : Module.Basis (Fin m) K W)
    (T : V →ₗ[K] W) (A' : Matrix (Fin m) (Fin n) K),
    (∀ v : V, Coordinates.coordinates_value c' (T v) =
      A' *ᵥ Coordinates.coordinates_value b' v) ↔
    A' = (changeMatrix_value c c')⁻¹ * matrixOfMap_value b c T * changeMatrix_value b b'

end Specs.D05.M04.ChangeBasis
