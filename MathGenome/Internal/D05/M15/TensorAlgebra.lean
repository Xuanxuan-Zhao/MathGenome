import MathGenome.Internal.Specs.D05.M15.TensorAlgebra
import MathGenome.Internal.D05.M06.ExternalSum
import MathGenome.Internal.D05.M15.AssociativitySymmetry

/-! K05.15.tensor_algebra: finite homogeneous decomposition, concatenation,
and the universal map to an arbitrary associative unital algebra.

The canonical quotient model is retained so subsequent exterior and symmetric
quotients can reuse it. `directSumEquiv` proves its equivalence with the paper's
external direct sum, including multiplication and scalar units.
-/

namespace D05.M15.TensorAlgebra

open scoped TensorProduct DirectSum

abbrev tensorAlgebra (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  _root_.TensorAlgebra K V

abbrev generator (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    V →ₗ[K] tensorAlgebra K V := _root_.TensorAlgebra.ι K

abbrev homogeneousInclusion (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) : TensorPower K p V →ₗ[K] tensorAlgebra K V := TensorPower.toTensorAlgebra

abbrev directSumEquiv (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    tensorAlgebra K V ≃ₐ[K] ⨁ p : ℕ, TensorPower K p V :=
  _root_.TensorAlgebra.equivDirectSum

abbrev extend (K V A : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Ring A] [Algebra K A] (f : V →ₗ[K] A) : tensorAlgebra K V →ₐ[K] A :=
  _root_.TensorAlgebra.lift K f

theorem degree_zero : Specs.D05.M15.TensorAlgebra.degree_zero := by
  intro K V _ _ _
  refine ⟨PiTensorProduct.isEmptyEquiv (Fin 0),
    fun x => PiTensorProduct.isEmptyEquiv_apply_tprod (Fin 0) x, fun _ => rfl, ?_⟩
  intro a
  exact TensorPower.toTensorAlgebra_galgebra_toFun a

theorem direct_sum_inclusion : Specs.D05.M15.TensorAlgebra.direct_sum_inclusion := by
  intro K V _ _ _ p t
  have h : (_root_.TensorAlgebra.equivDirectSum (R := K) (M := V)).toLinearMap.comp
      TensorPower.toTensorAlgebra = DirectSum.lof K ℕ (fun n => TensorPower K n V) p := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      TensorPower.toTensorAlgebra_tprod, DirectSum.lof_eq_of,
      AlgEquiv.toLinearMap_apply, _root_.TensorAlgebra.equivDirectSum_apply] using
      _root_.TensorAlgebra.toDirectSum_tensorPower_tprod (R := K) (M := V) x
  exact LinearMap.congr_fun h t

theorem direct_sum_inverse : Specs.D05.M15.TensorAlgebra.direct_sum_inverse := by
  intro K V _ _ _ p t
  apply (directSumEquiv K V).injective
  rw [AlgEquiv.apply_symm_apply, direct_sum_inclusion]

theorem homogeneous_injective : Specs.D05.M15.TensorAlgebra.homogeneous_injective := by
  intro K V _ _ _ p x y h
  have hh := congrArg (directSumEquiv K V) h
  rw [direct_sum_inclusion, direct_sum_inclusion] at hh
  have := congrArg (fun c => c p) hh
  simpa only [DirectSum.lof_eq_of, DirectSum.of_eq_same] using this

theorem finite_support : Specs.D05.M15.TensorAlgebra.finite_support := by
  intro K V _ _ _ x
  exact D05.M06.ExternalSum.finite_support (_root_.TensorAlgebra.equivDirectSum x)

theorem component_characterization :
    Specs.D05.M15.TensorAlgebra.component_characterization := by
  intro K V _ _ _ c
  constructor
  · rintro ⟨x, hx, _⟩
    have heq : (fun p => _root_.TensorAlgebra.equivDirectSum x p) = c := funext hx
    rw [← heq]
    exact finite_support x
  · intro hc
    obtain ⟨t, ht⟩ := D05.M06.ExternalSum.tuple_iff_finite_support c |>.mpr hc
    refine ⟨(directSumEquiv K V).symm t, ?_, ?_⟩
    · intro p
      rw [AlgEquiv.apply_symm_apply]
      exact ht p
    · intro y hy
      apply (directSumEquiv K V).injective
      rw [AlgEquiv.apply_symm_apply]
      exact DirectSum.ext (fun p => (hy p).trans (ht p).symm)

theorem reconstruction : Specs.D05.M15.TensorAlgebra.reconstruction := by
  intro K V _ _ _ x
  classical
  let t := directSumEquiv K V x
  refine ⟨t.support, ?_, ?_⟩
  · intro p hp
    exact DFinsupp.notMem_support_iff.mp hp
  · apply (directSumEquiv K V).injective
    rw [map_sum]
    calc
      directSumEquiv K V x = ∑ p ∈ t.support,
          DirectSum.lof K ℕ (fun n => TensorPower K n V) p (t p) := by
        simpa only [DirectSum.lof_eq_of] using (DirectSum.sum_support_of t).symm
      _ = _ := Finset.sum_congr rfl (fun p _ => (direct_sum_inclusion p (t p)).symm)

theorem elementary_word : Specs.D05.M15.TensorAlgebra.elementary_word := by
  intro K V _ _ _ p x
  exact (TensorPower.toTensorAlgebra_tprod x).trans (_root_.TensorAlgebra.tprod_apply K V x)

theorem homogeneous_multiplication :
    Specs.D05.M15.TensorAlgebra.homogeneous_multiplication := by
  intro K V _ _ _ p q x y
  exact (TensorPower.toTensorAlgebra_gMul x y).symm

theorem elementary_concatenation :
    Specs.D05.M15.TensorAlgebra.elementary_concatenation := by
  intro K V _ _ _ p q x y
  rw [homogeneous_multiplication, ← TensorPower.gMul_def, TensorPower.tprod_mul_tprod]

theorem algebra_laws : Specs.D05.M15.TensorAlgebra.algebra_laws := by
  intro K V _ _ _
  refine ⟨fun x y z => mul_assoc x y z, fun x => ⟨one_mul x, mul_one x⟩,
    fun a x y z => ⟨add_mul x y z, mul_add x y z, smul_mul_assoc a x y,
      mul_smul_comm a x y⟩, ?_⟩
  intro x
  rw [elementary_word]
  simp

theorem generated_by_vectors : Specs.D05.M15.TensorAlgebra.generated_by_vectors := by
  intro K V _ _ _
  exact _root_.TensorAlgebra.adjoin_range_ι

theorem extend_generator : Specs.D05.M15.TensorAlgebra.extend_generator := by
  intro K V A _ _ _ _ _ f v
  exact _root_.TensorAlgebra.lift_ι_apply f v

theorem extend_scalar : Specs.D05.M15.TensorAlgebra.extend_scalar := by
  intro K V A _ _ _ _ _ f a
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

theorem hom_ext : Specs.D05.M15.TensorAlgebra.hom_ext := by
  intro K V A _ _ _ _ _ F G h
  exact _root_.TensorAlgebra.hom_ext (LinearMap.ext h)

theorem universal_property : Specs.D05.M15.TensorAlgebra.universal_property := by
  intro K V A _ _ _ _ _ f
  refine ⟨extend K V A f, extend_generator f, ?_⟩
  intro F hF
  exact hom_ext F (extend K V A f) (fun v => (hF v).trans (extend_generator f v).symm)

theorem extending_hom_word : Specs.D05.M15.TensorAlgebra.extending_hom_word := by
  intro K V A _ _ _ _ _ f F hF p x
  rw [elementary_word, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, hF]

theorem extend_homogeneous : Specs.D05.M15.TensorAlgebra.extend_homogeneous := by
  intro K V A _ _ _ _ _ f p
  refine ⟨(extend K V A f).toLinearMap.comp (homogeneousInclusion K V p), ?_, fun _ => rfl⟩
  intro x
  exact extending_hom_word f (extend K V A f) (extend_generator f) p x

theorem extend_finite_sum : Specs.D05.M15.TensorAlgebra.extend_finite_sum := by
  intro K V A _ _ _ _ _ f s c
  exact map_sum (_root_.TensorAlgebra.lift K f) _ _

end D05.M15.TensorAlgebra
