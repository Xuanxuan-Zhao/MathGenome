import MathGenome.Internal.Specs.D05.M04.Coordinates
import MathGenome.Internal.D05.M02.Basis
import MathGenome.Internal.D05.M03.Isomorphism

/-! Coordinate columns and their inverse for K05.04.coordinates. -/

namespace D05.M04.Coordinates

/-- The coordinates in a finite ordered basis, bundled as a linear isomorphism. -/
noncomputable def coordinates {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) : V ≃ₗ[K] (Fin n → K) :=
  b.equivFun

theorem coordinates_apply : Specs.D05.M04.Coordinates.coordinates_apply := by
  intro K V _ _ _ n b x j
  rfl

theorem coordinates_add : Specs.D05.M04.Coordinates.coordinates_add := by
  intro K V _ _ _ n b x y
  exact b.equivFun.map_add x y

theorem coordinates_smul : Specs.D05.M04.Coordinates.coordinates_smul := by
  intro K V _ _ _ n b a x
  exact b.equivFun.map_smul a x

theorem inverse_apply : Specs.D05.M04.Coordinates.inverse_apply := by
  intro K V _ _ _ n b x
  exact b.equivFun_symm_apply x

theorem coordinates_sum : Specs.D05.M04.Coordinates.coordinates_sum := by
  intro K V _ _ _ n b x
  change b.equivFun (∑ j, x j • b j) = x
  rw [← b.equivFun_symm_apply, b.equivFun.apply_symm_apply]

theorem reconstruction : Specs.D05.M04.Coordinates.reconstruction := by
  intro K V _ _ _ n b x
  exact b.sum_equivFun x

theorem inverse_linear_combination :
    Specs.D05.M04.Coordinates.inverse_linear_combination := by
  intro K V _ _ _ n b a c x y
  exact D05.M03.Isomorphism.inverse_linear_combination b.equivFun a c x y

theorem inverse_laws : Specs.D05.M04.Coordinates.inverse_laws := by
  intro K V _ _ _ n b
  exact D05.M03.Isomorphism.inverse_laws b.equivFun

theorem unique_coordinates : Specs.D05.M04.Coordinates.unique_coordinates := by
  intro K V _ _ _ n b v
  refine ⟨b.equivFun v, b.sum_equivFun v, ?_⟩
  intro x hx
  have h := congrArg b.equivFun hx
  rw [← b.equivFun_symm_apply, b.equivFun.apply_symm_apply] at h
  exact h

theorem reindex_coordinates : Specs.D05.M04.Coordinates.reindex_coordinates := by
  intro K V _ _ _ n b σ x j
  exact b.repr_reindex_apply x σ j

theorem empty_basis_zero : Specs.D05.M04.Coordinates.empty_basis_zero := by
  intro K V _ _ _ b x
  have h := b.sum_equivFun x
  simpa only [Finset.univ_eq_empty, Finset.sum_empty] using h.symm

end D05.M04.Coordinates
