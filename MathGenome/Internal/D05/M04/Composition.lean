import MathGenome.Internal.Specs.D05.M04.Composition
import MathGenome.Internal.D05.M04.MatrixOfMap
import MathGenome.Internal.D05.M03.MapAlgebra

/-! Composition and the identity map in ordered bases, K05.04.composition. -/

namespace D05.M04.Composition

open Matrix

theorem matrix_comp : Specs.D05.M04.Composition.matrix_comp := by
  intro R U V W _ _ _ _ _ _ _ n m l b c d S T
  exact LinearMap.toMatrix_comp b c d S T

theorem composition_entry : Specs.D05.M04.Composition.composition_entry := by
  intro R U V W _ _ _ _ _ _ _ n m l b c d S T i j
  rw [matrix_comp b c d S T]
  exact Matrix.mul_apply

theorem composition_basis_image :
    Specs.D05.M04.Composition.composition_basis_image := by
  intro R U V W _ _ _ _ _ _ _ n m l b c d S T j
  have h := MatrixOfMap.basis_image b d (S.comp T) j
  simpa only [LinearMap.comp_apply, composition_entry b c d S T] using h

theorem matrix_id : Specs.D05.M04.Composition.matrix_id := by
  intro R V _ _ _ n b
  exact LinearMap.toMatrix_id b

theorem identity_entry : Specs.D05.M04.Composition.identity_entry := by
  intro R V _ _ _ n m b c i j
  exact LinearMap.toMatrix_apply b c LinearMap.id i j

theorem identity_coordinates : Specs.D05.M04.Composition.identity_coordinates := by
  intro K V _ _ _ n m b c
  apply LinearMap.ext
  intro x
  change (Specs.D05.M04.MatrixOfMap.matrixOfMap_value b c LinearMap.id) *ᵥ x =
    (Specs.D05.M04.Coordinates.coordinates_value c)
      ((Specs.D05.M04.Coordinates.coordinates_value b).symm x)
  have h := MatrixOfMap.coordinates_image b c (LinearMap.id : V →ₗ[K] V)
    ((Specs.D05.M04.Coordinates.coordinates_value b).symm x)
  simpa only [LinearMap.id_apply, LinearEquiv.apply_symm_apply] using h.symm

theorem identity_eq_one_iff : Specs.D05.M04.Composition.identity_eq_one_iff := by
  intro R V _ _ _ n b c
  constructor
  · intro h
    apply DFunLike.ext
    intro j
    apply c.repr.injective
    ext i
    have hij := congrArg (fun A : Matrix (Fin n) (Fin n) R => A i j) h
    simpa only [identity_entry b c, Matrix.one_apply, c.repr_self,
      Finsupp.single_apply, eq_comm] using hij
  · rintro rfl
    exact matrix_id b

end D05.M04.Composition
