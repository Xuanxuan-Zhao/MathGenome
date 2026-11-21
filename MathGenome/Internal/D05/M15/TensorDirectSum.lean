import MathGenome.Internal.Specs.D05.M15.TensorDirectSum
import MathGenome.Internal.D05.M06.ExternalSum
import MathGenome.Internal.D05.M06.Complement
import MathGenome.Internal.D05.M15.TensorMaps
import MathGenome.Internal.D05.M02.BasisExtension.Choice
import Mathlib.LinearAlgebra.TensorProduct.Pi

namespace D05.M15.TensorDirectSum

open scoped TensorProduct
open Specs.D05.M06.ExternalSum (finiteProductMap)

section Distribution

variable {K V W ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype ι]
  (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]

/-- Transport finite product distribution to the canonical external sum. -/
noncomputable def distributeLeft (d : V ≃ₗ[K] (∀ i, M i)) :
    (V ⊗[K] W) ≃ₗ[K] _root_.DirectSum ι (fun i => M i ⊗[K] W) := by
  classical
  exact TensorProduct.congr d (.refl K W) ≪≫ₗ
    TensorProduct.piLeft K W M ≪≫ₗ (finiteProductMap K ι _).symm

noncomputable def distributeRight (d : V ≃ₗ[K] (∀ i, M i)) :
    (W ⊗[K] V) ≃ₗ[K] _root_.DirectSum ι (fun i => W ⊗[K] M i) := by
  classical
  exact TensorProduct.congr (.refl K W) d ≪≫ₗ
    TensorProduct.piRight K K W M ≪≫ₗ (finiteProductMap K ι _).symm

@[simp] theorem distributeLeft_tmul (d : V ≃ₗ[K] (∀ i, M i)) (v : V) (w : W) (i : ι) :
    distributeLeft M d (v ⊗ₜ[K] w) i = d v i ⊗ₜ[K] w := by
  classical
  unfold distributeLeft
  simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  rw [D05.M06.ExternalSum.finiteProductEquiv_symm_apply]
  simp [TensorProduct.piLeft, LinearEquiv.piCongrRight_apply]

@[simp] theorem distributeRight_tmul (d : V ≃ₗ[K] (∀ i, M i)) (w : W) (v : V) (i : ι) :
    distributeRight M d (w ⊗ₜ[K] v) i = w ⊗ₜ[K] d v i := by
  classical
  unfold distributeRight
  simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  rw [D05.M06.ExternalSum.finiteProductEquiv_symm_apply]
  rfl

variable [DecidableEq ι]

/-- The inverse on one summand is precisely its tensor inclusion. -/
theorem distributeLeft_symm_lof (d : V ≃ₗ[K] (∀ i, M i)) (i : ι) (z : M i ⊗[K] W) :
    (distributeLeft M d).symm (_root_.DirectSum.lof K ι _ i z) =
      TensorProduct.map (d.symm.toLinearMap.comp (LinearMap.single K M i))
        (LinearMap.id : W →ₗ[K] W) z := by
  have h : (distributeLeft M d).symm.toLinearMap.comp (_root_.DirectSum.lof K ι _ i) =
      TensorProduct.map (d.symm.toLinearMap.comp (LinearMap.single K M i))
        (LinearMap.id : W →ₗ[K] W) := by
    apply TensorProduct.ext'
    intro m w
    apply (distributeLeft M d).injective
    apply _root_.DirectSum.ext
    intro j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      distributeLeft_tmul]
    by_cases hij : i = j
    · subst j
      simp
    · simp [Ne.symm hij, _root_.DirectSum.lof_eq_of,
        _root_.DirectSum.of_eq_of_ne]
  exact DFunLike.congr_fun h z

theorem distributeRight_symm_lof (d : V ≃ₗ[K] (∀ i, M i)) (i : ι) (z : W ⊗[K] M i) :
    (distributeRight M d).symm (_root_.DirectSum.lof K ι _ i z) =
      TensorProduct.map (LinearMap.id : W →ₗ[K] W)
        (d.symm.toLinearMap.comp (LinearMap.single K M i)) z := by
  have h : (distributeRight M d).symm.toLinearMap.comp (_root_.DirectSum.lof K ι _ i) =
      TensorProduct.map (LinearMap.id : W →ₗ[K] W)
        (d.symm.toLinearMap.comp (LinearMap.single K M i)) := by
    apply TensorProduct.ext'
    intro w m
    apply (distributeRight M d).injective
    apply _root_.DirectSum.ext
    intro j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      distributeRight_tmul]
    by_cases hij : i = j
    · subst j
      simp
    · simp [Ne.symm hij, _root_.DirectSum.lof_eq_of,
        _root_.DirectSum.of_eq_of_ne]
  exact DFunLike.congr_fun h z

/-- Finite summation of the component inverse maps. -/
theorem distributeLeft_symm (d : V ≃ₗ[K] (∀ i, M i))
    (t : _root_.DirectSum ι (fun i => M i ⊗[K] W)) :
    (distributeLeft M d).symm t = ∑ i,
      TensorProduct.map (d.symm.toLinearMap.comp (LinearMap.single K M i))
        (LinearMap.id : W →ₗ[K] W) (t i) := by
  classical
  have ht : (∑ i, _root_.DirectSum.lof K ι _ i (t i)) = t := by
    simpa only [_root_.DirectSum.lof_eq_of] using
      _root_.DirectSum.sum_univ_of t
  rw [← ht, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [distributeLeft_symm_lof]
  rw [ht]

theorem distributeRight_symm (d : V ≃ₗ[K] (∀ i, M i))
    (t : _root_.DirectSum ι (fun i => W ⊗[K] M i)) :
    (distributeRight M d).symm t = ∑ i,
      TensorProduct.map (LinearMap.id : W →ₗ[K] W)
        (d.symm.toLinearMap.comp (LinearMap.single K M i)) (t i) := by
  classical
  have ht : (∑ i, _root_.DirectSum.lof K ι _ i (t i)) = t := by
    simpa only [_root_.DirectSum.lof_eq_of] using
      _root_.DirectSum.sum_univ_of t
  rw [← ht, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [distributeRight_symm_lof]
  rw [ht]

end Distribution

theorem external_left : Specs.D05.M15.TensorDirectSum.external_left := by
  intro K W ι _ _ _ _ M _ _
  classical
  let d := finiteProductMap K ι M
  refine ⟨distributeLeft M d, ?_, ?_⟩
  · intro v w i
    exact distributeLeft_tmul M d v w i
  · intro t
    have hsingle (i : ι) : d.symm.toLinearMap.comp (LinearMap.single K M i) =
        _root_.DirectSum.lof K ι M i := by
      apply LinearMap.ext
      intro m
      apply _root_.DirectSum.ext
      intro j
      change ((finiteProductMap K ι M).symm (Pi.single i m)) j =
        (_root_.DirectSum.lof K ι M i m) j
      rw [D05.M06.ExternalSum.finiteProductEquiv_symm_apply]
      rfl
    simpa only [hsingle] using distributeLeft_symm M d t

theorem external_right : Specs.D05.M15.TensorDirectSum.external_right := by
  intro K W ι _ _ _ _ M _ _
  classical
  let d := finiteProductMap K ι M
  refine ⟨distributeRight M d, ?_, ?_⟩
  · intro w v i
    exact distributeRight_tmul M d w v i
  · intro t
    have hsingle (i : ι) : d.symm.toLinearMap.comp (LinearMap.single K M i) =
        _root_.DirectSum.lof K ι M i := by
      apply LinearMap.ext
      intro m
      apply _root_.DirectSum.ext
      intro j
      change ((finiteProductMap K ι M).symm (Pi.single i m)) j =
        (_root_.DirectSum.lof K ι M i m) j
      rw [D05.M06.ExternalSum.finiteProductEquiv_symm_apply]
      rfl
    simpa only [hsingle] using distributeRight_symm M d t

theorem internal_left : Specs.D05.M15.TensorDirectSum.internal_left := by
  intro K V W ι _ _ _ _ _ _ U hU
  classical
  obtain ⟨s, hs⟩ := D05.M06.DirectSum.summation_equiv U hU
  refine ⟨s.symm, hs, distributeLeft (fun i => U i) s.symm, ?_, ?_⟩
  · intro v w i
    exact distributeLeft_tmul (fun i => U i) s.symm v w i
  · intro t
    have hsingle (i : ι) : s.toLinearMap.comp (LinearMap.single K (fun i => U i) i) =
        (U i).subtype := by
      ext u
      change s (Pi.single i u) = (u : V)
      rw [hs]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    simpa only [LinearEquiv.symm_symm, hsingle] using
      distributeLeft_symm (fun i => U i) s.symm t

theorem internal_right : Specs.D05.M15.TensorDirectSum.internal_right := by
  intro K V W ι _ _ _ _ _ _ U hU
  classical
  obtain ⟨s, hs⟩ := D05.M06.DirectSum.summation_equiv U hU
  refine ⟨s.symm, hs, distributeRight (fun i => U i) s.symm, ?_, ?_⟩
  · intro w v i
    exact distributeRight_tmul (fun i => U i) s.symm w v i
  · intro t
    have hsingle (i : ι) : s.toLinearMap.comp (LinearMap.single K (fun i => U i) i) =
        (U i).subtype := by
      ext u
      change s (Pi.single i u) = (u : V)
      rw [hs]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    simpa only [LinearEquiv.symm_symm, hsingle] using
      distributeRight_symm (fun i => U i) s.symm t

/-- This calculation uses only functoriality, hence no basis choice. -/
theorem tensor_left_inverse : Specs.D05.M15.TensorDirectSum.tensor_left_inverse := by
  intro K U V W _ _ _ _ _ _ _ f r h
  constructor
  · rw [← TensorProduct.map_comp, h, LinearMap.id_comp, TensorProduct.map_id]
  · rw [← TensorProduct.map_comp, h, LinearMap.id_comp, TensorProduct.map_id]

/-- Mathlib's extension proof chooses a basis of the image and extends it to a
basis of the codomain, using the declared unrestricted basis-choice principle. -/
theorem subspace_retraction : Specs.D05.M15.TensorDirectSum.subspace_retraction := by
  intro K V _ _ _ U
  exact U.subtype.exists_leftInverse_of_injective U.ker_subtype

/-- A shared elementary consequence of a retraction, for either tensor variable. -/
theorem tensor_inclusions_of_retraction {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (U : Submodule K V) (r : V →ₗ[K] U) (hr : r.comp U.subtype = LinearMap.id) :
    (∃ R : (V ⊗[K] W) →ₗ[K] (U ⊗[K] W), R.comp
      (TensorProduct.map U.subtype (LinearMap.id : W →ₗ[K] W)) = LinearMap.id) ∧
    (∃ R : (W ⊗[K] V) →ₗ[K] (W ⊗[K] U), R.comp
      (TensorProduct.map (LinearMap.id : W →ₗ[K] W) U.subtype) = LinearMap.id) ∧
    Function.Injective (TensorProduct.map U.subtype (LinearMap.id : W →ₗ[K] W)) ∧
    Function.Injective (TensorProduct.map (LinearMap.id : W →ₗ[K] W) U.subtype) := by
  obtain ⟨hL, hR⟩ := tensor_left_inverse (W := W) U.subtype r hr
  refine ⟨⟨TensorProduct.map r LinearMap.id, hL⟩,
    ⟨TensorProduct.map LinearMap.id r, hR⟩, ?_, ?_⟩
  · exact (show Function.LeftInverse (TensorProduct.map r (LinearMap.id : W →ₗ[K] W))
      (TensorProduct.map U.subtype (LinearMap.id : W →ₗ[K] W)) from
        fun x => DFunLike.congr_fun hL x).injective
  · exact (show Function.LeftInverse (TensorProduct.map (LinearMap.id : W →ₗ[K] W) r)
      (TensorProduct.map (LinearMap.id : W →ₗ[K] W) U.subtype) from
        fun x => DFunLike.congr_fun hR x).injective

theorem subspace_tensor_inclusions :
    Specs.D05.M15.TensorDirectSum.subspace_tensor_inclusions := by
  intro K V W _ _ _ _ _ U
  obtain ⟨r, hr⟩ := subspace_retraction U
  exact tensor_inclusions_of_retraction U r hr

/-- The finite case takes its retraction from the accepted finite complement
interface. -/
theorem finite_subspace_tensor_inclusions :
    Specs.D05.M15.TensorDirectSum.finite_subspace_tensor_inclusions := by
  intro K V W _ _ _ _ _ _ U
  obtain ⟨C, hsup, hinf⟩ := D05.M06.Complement.exists_complement_sup_inf U
  have hc : IsCompl U C := isCompl_iff.mpr ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  exact tensor_inclusions_of_retraction U (U.projectionOnto C hc)
    (U.projectionOnto_comp_subtype hc)

end D05.M15.TensorDirectSum
