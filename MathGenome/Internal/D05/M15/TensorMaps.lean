import MathGenome.Internal.D05.M03.MapAlgebra
import MathGenome.Internal.D05.M15.TensorUniversal
import MathGenome.Internal.Specs.D05.M15.TensorMaps

/-! K05.15.tensor_maps: induced tensor maps, functoriality and linearity. -/

namespace D05.M15.TensorMaps

open scoped TensorProduct

/-- The unique linear map sending `v ⊗ w` to `S v ⊗ T w`.
Mathlib constructs it by the tensor universal property. -/
abbrev tensorMap {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (S : V →ₗ[K] V') (T : W →ₗ[K] W') :
    (V ⊗[K] W) →ₗ[K] (V' ⊗[K] W') := TensorProduct.map S T

theorem elementary_bilinear : Specs.D05.M15.TensorMaps.elementary_bilinear := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ S T
  exact ⟨((TensorProduct.mk K V' W').compl₂ T).comp S, fun _ _ => rfl⟩

theorem map_apply : Specs.D05.M15.TensorMaps.map_apply := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ S T v w
  rfl

theorem map_unique : Specs.D05.M15.TensorMaps.map_unique := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ S T F hF
  apply TensorProduct.ext'
  exact hF

theorem comp_apply : Specs.D05.M15.TensorMaps.comp_apply := by
  intro K V W V' W' V'' W'' _ _ _ _ _ _ _ _ _ _ _ _ _ S T S' T' v w
  rfl

theorem map_comp : Specs.D05.M15.TensorMaps.map_comp := by
  intro K V W V' W' V'' W'' _ _ _ _ _ _ _ _ _ _ _ _ _ S T S' T'
  apply TensorProduct.ext'
  intro v w
  rfl

theorem map_id : Specs.D05.M15.TensorMaps.map_id := by
  intro K V W _ _ _ _ _
  exact TensorProduct.map_id

theorem map_add_left : Specs.D05.M15.TensorMaps.map_add_left := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ S₁ S₂ T
  exact TensorProduct.map_add_left S₁ S₂ T

theorem map_add_right : Specs.D05.M15.TensorMaps.map_add_right := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ S T₁ T₂
  exact TensorProduct.map_add_right S T₁ T₂

theorem map_smul_left : Specs.D05.M15.TensorMaps.map_smul_left := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ a S T
  exact TensorProduct.map_smul_left a S T

theorem map_smul_right : Specs.D05.M15.TensorMaps.map_smul_right := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ a S T
  exact TensorProduct.map_smul_right a S T

/-- Tensoring isomorphisms, with inverse the tensor of the inverse maps. -/
abbrev tensorEquiv {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (S : V ≃ₗ[K] V') (T : W ≃ₗ[K] W') :
    (V ⊗[K] W) ≃ₗ[K] (V' ⊗[K] W') := TensorProduct.congr S T

theorem tensorEquiv_forward : Specs.D05.M15.TensorMaps.tensorEquiv_forward := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ S T
  rfl

theorem tensorEquiv_inverse : Specs.D05.M15.TensorMaps.tensorEquiv_inverse := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ S T
  rfl

end D05.M15.TensorMaps
