import MathGenome.Internal.Specs.D05.M04.MatrixOfMap
import MathGenome.Internal.Specs.D05.M03.MapAlgebra

/-!
Independent statements for K05.04.composition, paper.tex:635–642.
Matrices use the accepted `matrixOfMap_value`, with codomain rows and domain
columns. The three ordered bases have arbitrary finite sizes, including zero.
The based-module formulas hold over a commutative ring, hence in particular
over the paper's field. The coordinate-isomorphism statement uses the accepted
field-valued coordinate maps. No candidate implementation is imported here.
-/

namespace Specs.D05.M04.Composition

open Matrix

/-- Matrix multiplication represents composition, in the order `S` after `T`. -/
def matrix_comp : Prop :=
  ∀ {R U V W : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m l : ℕ}
    (b : Module.Basis (Fin n) R U) (c : Module.Basis (Fin m) R V)
    (d : Module.Basis (Fin l) R W) (S : V →ₗ[R] W) (T : U →ₗ[R] V),
    MatrixOfMap.matrixOfMap_value b d (S.comp T) =
      MatrixOfMap.matrixOfMap_value c d S * MatrixOfMap.matrixOfMap_value b c T

/-- The coefficient of a composite is the finite row-by-column sum. -/
def composition_entry : Prop :=
  ∀ {R U V W : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m l : ℕ}
    (b : Module.Basis (Fin n) R U) (c : Module.Basis (Fin m) R V)
    (d : Module.Basis (Fin l) R W) (S : V →ₗ[R] W) (T : U →ₗ[R] V)
    (i : Fin l) (j : Fin n),
    MatrixOfMap.matrixOfMap_value b d (S.comp T) i j =
      ∑ k, MatrixOfMap.matrixOfMap_value c d S i k *
        MatrixOfMap.matrixOfMap_value b c T k j

/-- Substitution of the two basis expansions gives the composite expansion. -/
def composition_basis_image : Prop :=
  ∀ {R U V W : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m l : ℕ}
    (b : Module.Basis (Fin n) R U) (c : Module.Basis (Fin m) R V)
    (d : Module.Basis (Fin l) R W) (S : V →ₗ[R] W) (T : U →ₗ[R] V)
    (j : Fin n),
    S (T (b j)) = ∑ i, (∑ k, MatrixOfMap.matrixOfMap_value c d S i k *
      MatrixOfMap.matrixOfMap_value b c T k j) • d i

/-- With the same basis on both sides, the identity map has identity matrix. -/
def matrix_id : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {n : ℕ} (b : Module.Basis (Fin n) R V),
    MatrixOfMap.matrixOfMap_value b b (LinearMap.id : V →ₗ[R] V) = 1

/-- With two bases, the columns of the identity matrix are the old basis
vectors expressed in the output basis. -/
def identity_entry : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {n m : ℕ} (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin m) R V)
    (i : Fin m) (j : Fin n),
    MatrixOfMap.matrixOfMap_value b c (LinearMap.id : V →ₗ[R] V) i j =
      c.repr (b j) i

/-- The identity map's matrix converts input-basis coordinates into
output-basis coordinates: it represents `c_C ∘ c_B⁻¹`. -/
def identity_coordinates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n m : ℕ} (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K V),
    MatrixOfMap.coordinateLinearMap_value
        (MatrixOfMap.matrixOfMap_value b c (LinearMap.id : V →ₗ[K] V)) =
      (Coordinates.coordinates_value c).toLinearMap.comp
        (Coordinates.coordinates_value b).symm.toLinearMap

/-- For equally indexed bases, this conversion is the identity matrix
exactly when the ordered bases agree. -/
def identity_eq_one_iff : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {n : ℕ} (b c : Module.Basis (Fin n) R V),
    MatrixOfMap.matrixOfMap_value b c (LinearMap.id : V →ₗ[R] V) = 1 ↔ b = c

end Specs.D05.M04.Composition
