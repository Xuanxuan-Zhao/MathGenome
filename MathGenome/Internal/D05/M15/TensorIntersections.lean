import MathGenome.Internal.Specs.D05.M15.TensorIntersections
import MathGenome.Internal.D05.M15.TensorDirectSum
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! K05.15.tensor_intersections. We use kernels and exactness, rather than a
simultaneously adapted basis. Over a field every vector space is free and flat.
All equalities concern the images of the actual natural tensor inclusions. -/
namespace D05.M15.TensorIntersections

open scoped TensorProduct
open LinearMap

section Kernels
variable {K V Z P Q : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup Z] [Module K Z]
  [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]

/-- A tensor killed by the two one-sided maps comes from the tensor of their
kernels. Lift through the first kernel, use injectivity of its inclusion to
retain the second vanishing condition, then lift through the second kernel. -/
theorem range_tensor_kernels (f : V →ₗ[K] P) (g : Z →ₗ[K] Q) :
    range (TensorProduct.map (ker f).subtype (ker g).subtype) =
      ker (f.rTensor Z) ⊓ ker (g.lTensor V) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    constructor
    · change (f.rTensor Z) (TensorProduct.map (ker f).subtype (ker g).subtype a) = 0
      have h : (f.rTensor Z).comp
          (TensorProduct.map (ker f).subtype (ker g).subtype) = 0 := by
        ext v z
        simp
      exact DFunLike.congr_fun h a
    · change (g.lTensor V) (TensorProduct.map (ker f).subtype (ker g).subtype a) = 0
      have h : (g.lTensor V).comp
          (TensorProduct.map (ker f).subtype (ker g).subtype) = 0 := by
        ext v z
        simp
      exact DFunLike.congr_fun h a
  · intro t ht
    obtain ⟨a, ha⟩ := (Module.Flat.rTensor_exact Z (exact_subtype_ker_map f) t).mp ht.1
    have hga : (g.lTensor (ker f)) a = 0 := by
      apply Module.Flat.rTensor_preserves_injective_linearMap (ker f).subtype
        (ker f).injective_subtype
      have hcomm : ((ker f).subtype.rTensor Q).comp (g.lTensor (ker f)) =
          (g.lTensor V).comp ((ker f).subtype.rTensor Z) := by
        ext v z
        rfl
      rw [map_zero]
      change (((ker f).subtype.rTensor Q).comp (g.lTensor (ker f))) a = 0
      rw [hcomm, LinearMap.comp_apply, ha]
      exact ht.2
    obtain ⟨b, hb⟩ := (Module.Flat.lTensor_exact (ker f) (exact_subtype_ker_map g) a).mp hga
    refine ⟨b, ?_⟩
    rw [← ha, ← hb]
    exact (DFunLike.congr_fun (LinearMap.rTensor_comp_lTensor _
      (ker f).subtype (ker g).subtype) b).symm

end Kernels

section Intersections
variable {K V Z P P' : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup Z] [Module K Z]
  [AddCommGroup P] [Module K P] [AddCommGroup P'] [Module K P']

/-- Tensoring on the right carries the kernel of a pair of maps to the
intersection of the two tensor kernels. -/
theorem ker_rTensor_prod (f : V →ₗ[K] P) (f' : V →ₗ[K] P') :
    ker ((f.prod f').rTensor Z) = ker (f.rTensor Z) ⊓ ker (f'.rTensor Z) := by
  let e := TensorProduct.prodLeft K K P P' Z
  have h : e.toLinearMap.comp ((f.prod f').rTensor Z) =
      (f.rTensor Z).prod (f'.rTensor Z) := by
    apply TensorProduct.ext'
    intro v z
    rfl
  ext t
  change (f.prod f').rTensor Z t = 0 ↔ _
  rw [← e.map_eq_zero_iff]
  change (e.toLinearMap.comp ((f.prod f').rTensor Z)) t = 0 ↔ _
  rw [h]
  simp only [LinearMap.prod_apply, Function.prod_apply, Prod.mk_eq_zero, Submodule.mem_inf, mem_ker]

/-- The corresponding kernel calculation in the other tensor variable. -/
theorem ker_lTensor_prod (f : V →ₗ[K] P) (f' : V →ₗ[K] P') :
    ker ((f.prod f').lTensor Z) = ker (f.lTensor Z) ⊓ ker (f'.lTensor Z) := by
  let e := TensorProduct.prodRight K K Z P P'
  have h : e.toLinearMap.comp ((f.prod f').lTensor Z) =
      (f.lTensor Z).prod (f'.lTensor Z) := by
    apply TensorProduct.ext'
    intro z v
    rfl
  ext t
  change (f.prod f').lTensor Z t = 0 ↔ _
  rw [← e.map_eq_zero_iff]
  change (e.toLinearMap.comp ((f.prod f').lTensor Z)) t = 0 ↔ _
  rw [h]
  simp only [LinearMap.prod_apply, Function.prod_apply, Prod.mk_eq_zero, Submodule.mem_inf, mem_ker]

/-- Quotients detect membership in the tensor of subspaces in both factors. -/
theorem range_tensor_subspaces (U : Submodule K V) (W : Submodule K Z) :
    range (TensorProduct.map U.subtype W.subtype) =
      ker (U.mkQ.rTensor Z) ⊓ ker (W.mkQ.lTensor V) := by
  have h := range_tensor_kernels U.mkQ W.mkQ
  rw [Submodule.ker_mkQ, Submodule.ker_mkQ] at h
  exact h

/-- The exact-sequence description of an intersection in the first factor. -/
theorem ker_rTensor_inf_quotient (U U' : Submodule K V) :
    ker ((U ⊓ U').mkQ.rTensor Z) =
      ker (U.mkQ.rTensor Z) ⊓ ker (U'.mkQ.rTensor Z) := by
  have h := (exact_iff.mp (Module.Flat.rTensor_exact Z
    (exact_subtype_ker_map (U.mkQ.prod U'.mkQ)))).symm
  rw [ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ] at h
  rw [rTensor_mkQ]
  exact h.trans (ker_rTensor_prod U.mkQ U'.mkQ)

/-- The exact-sequence description of an intersection in the second factor. -/
theorem ker_lTensor_inf_quotient (U U' : Submodule K V) :
    ker ((U ⊓ U').mkQ.lTensor Z) =
      ker (U.mkQ.lTensor Z) ⊓ ker (U'.mkQ.lTensor Z) := by
  have h := (exact_iff.mp (Module.Flat.lTensor_exact Z
    (exact_subtype_ker_map (U.mkQ.prod U'.mkQ)))).symm
  rw [ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ] at h
  rw [lTensor_mkQ]
  exact h.trans (ker_lTensor_prod U.mkQ U'.mkQ)

end Intersections

theorem tensor_subspace_injective :
    Specs.D05.M15.TensorIntersections.tensor_subspace_injective := by
  intro K V Z _ _ _ _ _ _ _ U W
  have hU := (D05.M15.TensorDirectSum.finite_subspace_tensor_inclusions
    (W := ↥W) U).2.2.1
  have hW := (D05.M15.TensorDirectSum.finite_subspace_tensor_inclusions
    (W := V) W).2.2.2
  rw [← LinearMap.lTensor_comp_rTensor]
  exact hW.comp hU

theorem tensor_intersection : Specs.D05.M15.TensorIntersections.tensor_intersection := by
  intro K V Z _ _ _ _ _ _ _ U U' W W'
  rw [range_tensor_subspaces, range_tensor_subspaces, range_tensor_subspaces,
    ker_rTensor_inf_quotient, ker_lTensor_inf_quotient]
  ext t
  simp only [Submodule.mem_inf]
  exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩,
    fun h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩⟩

end D05.M15.TensorIntersections
