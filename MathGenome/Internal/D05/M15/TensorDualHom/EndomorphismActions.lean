import MathGenome.Internal.Specs.D05.M15.TensorDualHom.EndomorphismActions
import MathGenome.Internal.D05.M03.HomDimension
import MathGenome.Internal.D05.M15.TensorBasis
import MathGenome.Internal.D05.M15.TensorMaps
import MathGenome.Internal.D05.M15.TensorPairing
import MathGenome.Internal.D05.M07.DualMap

/-! K05.15.tensor_dual_hom: linear maps on a tensor product.
The library equivalence is obtained by tensor–Hom equivalences and currying,
with its forward linear map definitionally the canonical linearization.
The elementary matrix calculation and the duality square are verified below.
-/
namespace D05.M15.TensorDualHom.EndomorphismActions

open scoped TensorProduct

theorem map_apply : Specs.D05.M15.TensorDualHom.EndomorphismActions.map_apply := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ S T
  rfl

theorem map_unique : Specs.D05.M15.TensorDualHom.EndomorphismActions.map_unique := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ F hF
  exact TensorProduct.ext' hF

theorem canonical_isomorphism :
    Specs.D05.M15.TensorDualHom.EndomorphismActions.canonical_isomorphism := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ⟨homTensorHomEquiv K V W V' W', rfl⟩

theorem canonical_bijective :
    Specs.D05.M15.TensorDualHom.EndomorphismActions.canonical_bijective := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨E, hE⟩ := canonical_isomorphism (K := K) (V := V) (W := W) (V' := V') (W' := W')
  rw [← hE]
  exact E.bijective

theorem matrix_unit_action :
    Specs.D05.M15.TensorDualHom.EndomorphismActions.matrix_unit_action := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ n m n' m' b c b' c' i j k l a d
  rw [map_apply, TensorProduct.map_tmul,
    D05.M03.HomDimension.elementaryMap_apply_basis,
    D05.M03.HomDimension.elementaryMap_apply_basis]
  split_ifs <;> simp_all

theorem dual_naturality :
    Specs.D05.M15.TensorDualHom.EndomorphismActions.dual_naturality := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ S T
  apply TensorProduct.ext'
  intro φ ψ
  apply TensorProduct.ext'
  intro v w
  rfl

theorem dual_tensor_map :
    Specs.D05.M15.TensorDualHom.EndomorphismActions.dual_tensor_map := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _ S T
  obtain ⟨E, hE⟩ := D05.M15.TensorPairing.perfect_pairing (K := K) (V := V) (W := W)
  obtain ⟨F, hF⟩ := D05.M15.TensorPairing.perfect_pairing (K := K) (V := V') (W := W')
  refine ⟨E, F, hE, hF, ?_⟩
  have h := dual_naturality S T
  rw [← hE, ← hF] at h
  apply LinearMap.ext
  intro z
  have hz := congrArg (fun L => L (F.symm z)) h
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using hz

end D05.M15.TensorDualHom.EndomorphismActions
