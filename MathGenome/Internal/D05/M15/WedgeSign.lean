import MathGenome.Internal.Specs.D05.M15.WedgeSign
import MathGenome.Internal.D05.M15.Exterior
import MathGenome.Internal.D05.M15.TensorMaps

/-! K05.15.wedge_sign: graded commutativity and the functorial exterior map.
All degrees and arbitrary vector spaces over an arbitrary field are included. -/

noncomputable section
namespace D05.M15.WedgeSign

open scoped TensorProduct
open Specs.D05.M15.WedgeSign

abbrev tensorMap : tensorMap_type := @tensorMap_value
abbrev exteriorMap : exteriorMap_type := @exteriorMap_value
abbrev powerMap : powerMap_type := @powerMap_value

theorem elementary_sign : Specs.D05.M15.WedgeSign.elementary_sign := by
  intro K V _ _ _ p q a b
  simpa only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one, ← Int.cast_smul_eq_zsmul K, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Nat.mul_comm] using
    (_root_.ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm K a b)

theorem graded_comm : Specs.D05.M15.WedgeSign.graded_comm := by
  intro K V _ _ _ p q a b ha hb
  change a ∈ ⋀[K]^p V at ha
  change b ∈ ⋀[K]^q V at hb
  rw [← _root_.ExteriorAlgebra.ιMulti_span_fixedDegree K p] at ha
  rw [← _root_.ExteriorAlgebra.ιMulti_span_fixedDegree K q] at hb
  refine Submodule.span_induction₂ (p := fun x y _ _ =>
    x * y = (-1 : K) ^ (p * q) • (y * x)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
  · rintro x y ⟨u, rfl⟩ ⟨v, rfl⟩
    exact elementary_sign p q u v
  all_goals simp +contextual [add_mul, mul_add, smul_smul, mul_comm]

theorem tensor_map_generator : Specs.D05.M15.WedgeSign.tensor_map_generator := by
  intro K V W _ _ _ _ _ T v
  exact _root_.TensorAlgebra.lift_ι_apply ((_root_.TensorAlgebra.ι K).comp T) v

theorem tensor_map_word : Specs.D05.M15.WedgeSign.tensor_map_word := by
  intro K V W _ _ _ _ _ T p a
  rw [D05.M15.TensorAlgebra.elementary_word, D05.M15.TensorAlgebra.elementary_word,
    map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, tensorMap_value, _root_.TensorAlgebra.lift_ι_apply,
    LinearMap.comp_apply]

theorem tensor_map_homogeneous : Specs.D05.M15.WedgeSign.tensor_map_homogeneous := by
  intro K V W _ _ _ _ _ T p a
  have h : (tensorMap T).toLinearMap.comp TensorPower.toTensorAlgebra =
      (TensorPower.toTensorAlgebra : TensorPower K p W →ₗ[K] _).comp
        (PiTensorProduct.map (fun _ : Fin p => T)) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      PiTensorProduct.map_tprod, Function.comp_def, tensorMap,
      AlgHom.toLinearMap_apply] using tensor_map_word T p x
  exact LinearMap.congr_fun h a

theorem tensor_map_square : Specs.D05.M15.WedgeSign.tensor_map_square := by
  intro K V W _ _ _ _ _ T v
  rw [map_mul, tensor_map_generator]

theorem exterior_map_generator : Specs.D05.M15.WedgeSign.exterior_map_generator := by
  intro K V W _ _ _ _ _ T v
  exact _root_.ExteriorAlgebra.map_apply_ι T v

theorem exterior_map_word : Specs.D05.M15.WedgeSign.exterior_map_word := by
  intro K V W _ _ _ _ _ T p a
  exact _root_.ExteriorAlgebra.map_apply_ιMulti T a

theorem quotient_naturality : Specs.D05.M15.WedgeSign.quotient_naturality := by
  intro K V W _ _ _ _ _ T
  apply _root_.TensorAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  change exteriorMap T (D05.M15.Exterior.quotientMap K V (_root_.TensorAlgebra.ι K v)) =
    D05.M15.Exterior.quotientMap K W (tensorMap T (_root_.TensorAlgebra.ι K v))
  rw [D05.M15.Exterior.quotient_generator, tensor_map_generator,
    D05.M15.Exterior.quotient_generator, exterior_map_generator]

theorem ideal_preserved : Specs.D05.M15.WedgeSign.ideal_preserved := by
  intro K V W _ _ _ _ _ T a ha
  apply (D05.M15.Exterior.quotient_kernel _).mp
  have h := AlgHom.congr_fun (quotient_naturality T) a
  change exteriorMap T (D05.M15.Exterior.quotientMap K V a) =
    D05.M15.Exterior.quotientMap K W (tensorMap T a) at h
  rw [(D05.M15.Exterior.quotient_kernel a).mpr ha, map_zero] at h
  exact h.symm

theorem exterior_map_unique : Specs.D05.M15.WedgeSign.exterior_map_unique := by
  intro K V W _ _ _ _ _ T F hF
  apply _root_.ExteriorAlgebra.hom_ext
  exact LinearMap.ext (fun v => (hF v).trans (exterior_map_generator T v).symm)

theorem power_restriction : Specs.D05.M15.WedgeSign.power_restriction := by
  intro K V W _ _ _ _ _ T p a
  exact exteriorPower.coe_map T a

theorem degree_preserved : Specs.D05.M15.WedgeSign.degree_preserved := by
  intro K V W _ _ _ _ _ T p a ha
  rw [← power_restriction T p ⟨a, ha⟩]
  exact (powerMap p T ⟨a, ha⟩).property

theorem power_map_elementary : Specs.D05.M15.WedgeSign.power_map_elementary := by
  intro K V W _ _ _ _ _ T p a
  exact exteriorPower.map_apply_ιMulti T a

theorem power_map_comp : Specs.D05.M15.WedgeSign.power_map_comp := by
  intro K V W X _ _ _ _ _ _ _ T S p
  exact exteriorPower.map_comp T S

theorem power_map_id : Specs.D05.M15.WedgeSign.power_map_id := by
  intro K V _ _ _ p
  exact exteriorPower.map_id

theorem exterior_map_comp : Specs.D05.M15.WedgeSign.exterior_map_comp := by
  intro K V W X _ _ _ _ _ _ _ T S
  exact (_root_.ExteriorAlgebra.map_comp_map T S).symm

theorem exterior_map_id : Specs.D05.M15.WedgeSign.exterior_map_id := by
  intro K V _ _ _
  exact _root_.ExteriorAlgebra.map_id

theorem power_map_zero : Specs.D05.M15.WedgeSign.power_map_zero := by
  intro K V W _ _ _ _ _ T a
  exact LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality T) a

theorem exterior_map_scalar : Specs.D05.M15.WedgeSign.exterior_map_scalar := by
  intro K V W _ _ _ _ _ T c
  exact (exteriorMap T).commutes c

end D05.M15.WedgeSign
