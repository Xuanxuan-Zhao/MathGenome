import MathGenome.Internal.Specs.D05.M15.Exterior
import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.LinearAlgebra.Isomorphisms
import MathGenome.Internal.D05.M15.TensorAlgebra
import MathGenome.Internal.D05.M15.Multilinear
import MathGenome.Internal.D05.M05.Alternating
import MathGenome.Internal.D05.M06.QuotientLift

/-! K05.15.exterior: the square-relation quotient, its grading, and both
universal properties, over an arbitrary field and in all degrees. -/

noncomputable section
namespace D05.M15.Exterior

open scoped TensorProduct DirectSum
open Specs.D05.M15.Exterior

abbrev exteriorAlgebra := exteriorAlgebra_value
abbrev definingIdeal := definingIdeal_value
abbrev homogeneousPart := homogeneousPart_value
abbrev generator := generator_value
abbrev quotientMap := quotientMap_value
abbrev tensorProjection := tensorProjection_value
abbrev degreeRelations := degreeRelations_value
abbrev alternatingLift := alternatingLift_value
abbrev algebraLift := algebraLift_value

theorem quotient_generator : Specs.D05.M15.Exterior.quotient_generator := by
  intro K V _ _ _ v
  exact _root_.TensorAlgebra.toExterior_ι v

/-- The canonical lift is literally the projection to the square-relation quotient. -/
theorem quotientMap_eq_mk {K V : Type*} [Field K] [AddCommGroup V] [Module K V] :
    quotientMap K V = RingCon.mkₐ K (definingIdeal K V).ringCon := by
  apply _root_.TensorAlgebra.hom_ext
  exact LinearMap.ext (fun v => quotient_generator v)

theorem quotient_realization : Specs.D05.M15.Exterior.quotient_realization := by
  intro K V _ _ _
  exact ⟨AlgEquiv.refl, fun t => (AlgHom.congr_fun quotientMap_eq_mk t).symm⟩

theorem quotient_kernel : Specs.D05.M15.Exterior.quotient_kernel := by
  intro K V _ _ _ t
  change quotientMap K V t = 0 ↔ (definingIdeal K V).ringCon t 0
  rw [quotientMap_eq_mk]
  exact (definingIdeal K V).ringCon.eq

theorem quotient_surjective : Specs.D05.M15.Exterior.quotient_surjective := by
  intro K V _ _ _
  change Function.Surjective (quotientMap K V)
  rw [quotientMap_eq_mk]
  exact RingCon.mkₐ_surjective _

theorem ideal_eq_span : Specs.D05.M15.Exterior.ideal_eq_span := by
  intro K V _ _ _
  apply le_antisymm
  · rw [TwoSidedIdeal.ringCon_le_iff]
    apply RingCon.ringConGen_le.mpr
    intro x y h
    cases h with
    | of v =>
      have h := (TwoSidedIdeal.subset_span (Set.mem_range_self v) :
          _root_.TensorAlgebra.ι K v * _root_.TensorAlgebra.ι K v ∈
            TwoSidedIdeal.span (Set.range (fun v : V =>
              _root_.TensorAlgebra.ι K v * _root_.TensorAlgebra.ι K v)))
      change (TwoSidedIdeal.span _).ringCon _ 0 at h
      simpa only [zero_apply, map_zero] using h
  · apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨v, rfl⟩
    apply (quotient_kernel _).mp
    simp only [quotientMap_value, map_mul, _root_.TensorAlgebra.toExterior_ι,
      _root_.ExteriorAlgebra.ι_sq_zero]

theorem square_zero : Specs.D05.M15.Exterior.square_zero := by
  intro K V _ _ _ v
  exact _root_.ExteriorAlgebra.ι_sq_zero v

theorem generator_anticommutation : Specs.D05.M15.Exterior.generator_anticommutation := by
  intro K V _ _ _ u v
  exact eq_neg_of_add_eq_zero_left (_root_.ExteriorAlgebra.ι_add_mul_swap u v)

theorem algebra_laws : Specs.D05.M15.Exterior.algebra_laws := by
  intro K V _ _ _
  exact ⟨mul_assoc, fun x => ⟨one_mul x, mul_one x⟩,
    fun x y z => ⟨add_mul x y z, mul_add x y z⟩⟩

theorem graded_decomposition : Specs.D05.M15.Exterior.graded_decomposition := by
  intro K V _ _ _
  exact ⟨DirectSum.decomposeAlgEquiv (fun p : ℕ => ⋀[K]^p V),
    fun p x => DirectSum.decompose_coe (fun p : ℕ => ⋀[K]^p V) x⟩

theorem homogeneous_multiplication : Specs.D05.M15.Exterior.homogeneous_multiplication := by
  intro K V _ _ _ p q a b ha hb
  exact SetLike.GradedMul.mul_mem (A := fun p : ℕ => ⋀[K]^p V) ha hb

theorem degree_zero : Specs.D05.M15.Exterior.degree_zero := by
  intro K V _ _ _
  refine ⟨exteriorPower.zeroEquiv K V, exteriorPower.zeroEquiv_ιMulti, ?_⟩
  intro a
  simp only [exteriorPower.zeroEquiv_symm_apply, Submodule.coe_smul_of_tower,
    exteriorPower.ιMulti_apply_coe, _root_.ExteriorAlgebra.ιMulti_zero_apply,
    Algebra.algebraMap_eq_smul_one]

theorem projection_elementary : Specs.D05.M15.Exterior.projection_elementary := by
  intro K V _ _ _ p x
  exact PiTensorProduct.lift.tprod _

theorem projection_compatibility : Specs.D05.M15.Exterior.projection_compatibility := by
  intro K V _ _ _ p t
  have h : (Submodule.subtype (⋀[K]^p V)).comp (tensorProjection K V p) =
      (quotientMap K V).toLinearMap.comp TensorPower.toTensorAlgebra := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change ((tensorProjection K V p) (PiTensorProduct.tprod K x) :
      _root_.ExteriorAlgebra K V) = quotientMap K V (TensorPower.toTensorAlgebra _)
    rw [projection_elementary p x, D05.M15.TensorAlgebra.elementary_word p x]
    change _root_.ExteriorAlgebra.ιMulti K p x =
      _root_.TensorAlgebra.toExterior ((List.ofFn (fun i => _root_.TensorAlgebra.ι K (x i))).prod)
    rw [_root_.ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    exact (_root_.TensorAlgebra.toExterior_ι (x i)).symm
  exact LinearMap.congr_fun h t

theorem projection_surjective : Specs.D05.M15.Exterior.projection_surjective := by
  intro K V _ _ _ p
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← exteriorPower.ιMulti_span K p V, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact ⟨PiTensorProduct.tprod K x, projection_elementary p x⟩

theorem degree_relations_iff : Specs.D05.M15.Exterior.degree_relations_iff := by
  intro K V _ _ _ p t
  exact quotient_kernel _

/-- The degree map has precisely the pulled-back defining relations as kernel. -/
theorem projection_kernel {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (p : ℕ) :
    LinearMap.ker (tensorProjection K V p) = degreeRelations K V p := by
  ext t
  change tensorProjection K V p t = 0 ↔ quotientMap K V (TensorPower.toTensorAlgebra t) = 0
  rw [← projection_compatibility p t]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem degree_quotient : Specs.D05.M15.Exterior.degree_quotient := by
  intro K V _ _ _ p
  have hk : degreeRelations_value K V p = LinearMap.ker (tensorProjection K V p) :=
    (projection_kernel p).symm
  rw [hk]
  exact ⟨LinearMap.quotKerEquivOfSurjective (tensorProjection K V p) (projection_surjective p),
    fun t => LinearMap.quotKerEquivOfSurjective_apply_mk _ _ t⟩

theorem alternating_swap : Specs.D05.M15.Exterior.alternating_swap := by
  intro K V H _ _ _ _ _ p b hb x i j hij
  exact (show AlternatingMap K V H (Fin p) from ⟨b, hb⟩).map_swap x hij

theorem alternatingLift_apply : Specs.D05.M15.Exterior.alternatingLift_apply := by
  intro K V H _ _ _ _ _ p b x
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b x

theorem alternating_universal : Specs.D05.M15.Exterior.alternating_universal := by
  intro K V H _ _ _ _ _ p b
  constructor
  · rintro ⟨L, hL, _⟩ x i j hx hij
    rw [← hL, (exteriorPower.ιMulti K p).map_eq_zero_of_eq x hx hij, map_zero]
  · intro hb
    let a : AlternatingMap K V H (Fin p) := ⟨b, hb⟩
    refine ⟨alternatingLift K V H p a, alternatingLift_apply p a, ?_⟩
    intro L hL
    apply exteriorPower.linearMap_ext
    exact AlternatingMap.ext (fun x => (hL x).trans (alternatingLift_apply p a x).symm)

theorem algebraLift_apply : Specs.D05.M15.Exterior.algebraLift_apply := by
  intro K V A _ _ _ _ _ f hf v
  exact _root_.ExteriorAlgebra.lift_ι_apply K f hf v

theorem algebra_hom_ext : Specs.D05.M15.Exterior.algebra_hom_ext := by
  intro K V A _ _ _ _ _ F G h
  exact _root_.ExteriorAlgebra.hom_ext (LinearMap.ext h)

theorem algebra_universal : Specs.D05.M15.Exterior.algebra_universal := by
  intro K V A _ _ _ _ _ f
  constructor
  · rintro ⟨F, hF, _⟩ v
    rw [← hF, ← map_mul, square_zero, map_zero]
  · intro hf
    refine ⟨algebraLift K V A f hf, algebraLift_apply f hf, ?_⟩
    intro F hF
    exact algebra_hom_ext F _ (fun v => (hF v).trans (algebraLift_apply f hf v).symm)

theorem algebra_tensor_factorization : Specs.D05.M15.Exterior.algebra_tensor_factorization := by
  intro K V A _ _ _ _ _ f hf
  apply _root_.TensorAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  simp only [AlgHom.comp_toLinearMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    quotientMap_value, _root_.TensorAlgebra.toExterior_ι, algebraLift_value,
    _root_.ExteriorAlgebra.lift_ι_apply, _root_.TensorAlgebra.lift_ι_apply]

/-- The quotient preserves each tensor degree; hence its kernel is homogeneous. -/
theorem ideal_homogeneous : Specs.D05.M15.Exterior.ideal_homogeneous := by
  intro K V _ _ _ t ht p
  let qg : (fun n : ℕ => LinearMap.range (_root_.TensorAlgebra.ι K (M := V)) ^ n) →+*ᵍ
      (fun n : ℕ => ⋀[K]^n V) :=
    { (quotientMap K V).toRingHom with
      map_mem := by
        intro n x hx
        have hr : Submodule.map (quotientMap K V).toLinearMap
            (LinearMap.range (_root_.TensorAlgebra.ι K (M := V))) =
            LinearMap.range (_root_.ExteriorAlgebra.ι K (M := V)) := by
          rw [← LinearMap.range_comp]
          congr 1
          exact LinearMap.ext (fun v => quotient_generator v)
        have hmap := Submodule.mem_map_of_mem (f := (quotientMap K V).toLinearMap) hx
        rw [Submodule.map_pow, hr] at hmap
        exact hmap }
  apply (quotient_kernel _).mp
  change qg _ = 0
  rw [qg.map_directSumDecompose]
  have hz : qg t = 0 := (quotient_kernel t).mpr ht
  simp only [hz, DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]

theorem alternating_annihilates_relations :
    Specs.D05.M15.Exterior.alternating_annihilates_relations := by
  intro K V H _ _ _ _ _ p b
  constructor
  · intro hb
    obtain ⟨L, hL, _⟩ := (alternating_universal p b).mpr hb
    have hfac : L.comp (tensorProjection K V p) = PiTensorProduct.lift b := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        tensorProjection, tensorProjection_value, PiTensorProduct.lift.tprod]
      exact hL x
    intro t ht
    have hz : tensorProjection K V p t = 0 := by
      change t ∈ LinearMap.ker (tensorProjection K V p)
      rw [projection_kernel p]
      exact ht
    change PiTensorProduct.lift b t = 0
    rw [← hfac, LinearMap.comp_apply, hz, map_zero]
  · intro hb x i j hx hij
    have hz : tensorProjection K V p (PiTensorProduct.tprod K x) = 0 := by
      rw [projection_elementary]
      exact (exteriorPower.ιMulti K p).map_eq_zero_of_eq x hx hij
    have ht : PiTensorProduct.tprod K x ∈ degreeRelations K V p := by
      rw [← projection_kernel p]
      exact hz
    have h := hb ht
    exact (PiTensorProduct.lift.tprod x).symm.trans h

theorem linear_factorization : Specs.D05.M15.Exterior.linear_factorization := by
  intro K V H _ _ _ _ _ p T
  constructor
  · rintro ⟨L, hL, _⟩ t ht
    have hz : tensorProjection K V p t = 0 := by
      change t ∈ LinearMap.ker (tensorProjection K V p)
      rw [projection_kernel p]
      exact ht
    change T t = 0
    rw [← hL, LinearMap.comp_apply, hz, map_zero]
  · intro hT
    obtain ⟨e, he⟩ := degree_quotient (K := K) (V := V) p
    let L := ((degreeRelations K V p).liftQ T hT).comp e.symm.toLinearMap
    have hL : L.comp (tensorProjection K V p) = T := by
      apply LinearMap.ext
      intro t
      change (degreeRelations K V p).liftQ T hT (e.symm (tensorProjection K V p t)) = T t
      rw [← he t, e.symm_apply_apply]
      rfl
    refine ⟨L, hL, ?_⟩
    intro L' hL'
    apply LinearMap.ext
    intro x
    obtain ⟨t, rfl⟩ := projection_surjective p x
    exact (LinearMap.congr_fun hL' t).trans (LinearMap.congr_fun hL t).symm

end D05.M15.Exterior
