import MathGenome.Internal.Specs.D05.M15.TensorKernel
import MathGenome.Internal.D05.M15.TensorDirectSum
import MathGenome.Internal.D05.M15.TensorMaps
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! K05.15.tensor_kernel: images and kernels in the ambient tensor spaces. -/

namespace D05.M15.TensorKernel

open scoped TensorProduct

theorem subspace_tensor_inclusion :
    Specs.D05.M15.TensorKernel.subspace_tensor_inclusion := by
  intro K V W _ _ _ _ _ _ _ U P
  have hU := (D05.M15.TensorDirectSum.finite_subspace_tensor_inclusions
    (W := W) U).2.2.1
  have hP := (D05.M15.TensorDirectSum.finite_subspace_tensor_inclusions
    (W := U) P).2.2.2
  have hcomp : (TensorProduct.map U.subtype (LinearMap.id : W →ₗ[K] W)).comp
      (TensorProduct.map (LinearMap.id : U →ₗ[K] U) P.subtype) =
      TensorProduct.map U.subtype P.subtype := by
    rw [← TensorProduct.map_comp]
    simp
  rw [← hcomp]
  exact hU.comp hP

theorem range_tensorMap : Specs.D05.M15.TensorKernel.range_tensorMap := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _ S T
  simp only [TensorProduct.range_map, Submodule.range_subtype]

/-- Restrict each map to its image so that right exactness applies. The
injective tensor inclusion of those images does not change the kernel. -/
theorem ker_tensorMap : Specs.D05.M15.TensorKernel.ker_tensorMap := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _ S T
  have hincl := subspace_tensor_inclusion S.range T.range
  have hfactor : (TensorProduct.map S.range.subtype T.range.subtype).comp
      (TensorProduct.map S.rangeRestrict T.rangeRestrict) = TensorProduct.map S T := by
    rw [← TensorProduct.map_comp]
    rw [S.subtype_comp_rangeRestrict, T.subtype_comp_rangeRestrict]
  rw [← hfactor, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hincl)]
  have hS : Function.Exact S.ker.subtype S.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have hT : Function.Exact T.ker.subtype T.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have h := TensorProduct.map_ker hS S.surjective_rangeRestrict
    hT T.surjective_rangeRestrict
  simpa only [LinearMap.lTensor, LinearMap.rTensor, sup_comm] using h

end D05.M15.TensorKernel
