import MathGenome.Internal.Specs.D05.M06.ExternalSum
import MathGenome.Internal.D05.M06.DirectSum
import MathGenome.Internal.D05.M03.Isomorphism

/-! K05.06.external_sum: external finitely supported sums, finite products,
and the actual summation map to an internal sum. -/

namespace D05.M06.ExternalSum

open Specs.D05.M06.ExternalSum (finiteProductMap summationMap)

/-- Tuples with finite support; the scalar field supplies the canonical module
structure on this existing additive group. -/
abbrev externalSum (ι : Type*) (M : ι → Type*) [∀ i, AddCommGroup (M i)] :=
  _root_.DirectSum ι M

/-- The finite sum/product identification keeps exactly the same components. -/
noncomputable abbrev finiteProductEquiv (K : Type*) (ι : Type*) (M : ι → Type*)
    [Field K] [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] [Finite ι] :
    externalSum ι M ≃ₗ[K] (∀ i, M i) := finiteProductMap K ι M

/-- Add the actual included subspace components. -/
noncomputable abbrev summation (K V ι : Type*) [Field K] [AddCommGroup V]
    [Module K V] (U : ι → Submodule K V) :
    externalSum ι (fun i => U i) →ₗ[K] V := summationMap U

theorem vector_space : Specs.D05.M06.ExternalSum.vector_space := by
  intro K ι M _ _ _
  exact ⟨inferInstance⟩

theorem componentwise_operations : Specs.D05.M06.ExternalSum.componentwise_operations := by
  intro K ι M _ _ _ a x y i
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem finite_support : Specs.D05.M06.ExternalSum.finite_support := by
  intro ι M _ x
  exact DFinsupp.finite_support x

theorem tuple_iff_finite_support : Specs.D05.M06.ExternalSum.tuple_iff_finite_support := by
  intro ι M _ f
  classical
  constructor
  · rintro ⟨x, hx⟩
    have heq : (fun i => x i) = f := funext hx
    rw [← heq]
    exact finite_support x
  · intro hf
    refine ⟨DFinsupp.mk hf.toFinset (fun i => f i), ?_⟩
    intro i
    by_cases hi : i ∈ hf.toFinset
    · exact DFinsupp.mk_of_mem hi
    · rw [DFinsupp.mk_of_notMem hi]
      exact (not_ne_iff.mp (by simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        using hi)).symm

theorem extensionality : Specs.D05.M06.ExternalSum.extensionality := by
  intro ι M _ x y
  exact ⟨_root_.DirectSum.ext, fun h i => congrArg (fun z => z i) h⟩

theorem support_add_subset : Specs.D05.M06.ExternalSum.support_add_subset := by
  intro ι M _ x y i hi
  change x i + y i ≠ 0 at hi
  by_cases hx : x i = 0
  · exact Or.inr (fun hy => hi (by rw [hx, hy, add_zero]))
  · exact Or.inl hx

theorem support_smul_subset : Specs.D05.M06.ExternalSum.support_smul_subset := by
  intro K ι M _ _ _ a x i hi hx
  apply hi
  change a • x i = 0
  rw [hx, smul_zero]

theorem finiteProductEquiv_apply : Specs.D05.M06.ExternalSum.finiteProductEquiv_apply := by
  intro K ι M _ _ _ _ x i
  rfl

theorem finiteProductEquiv_symm_apply :
    Specs.D05.M06.ExternalSum.finiteProductEquiv_symm_apply := by
  intro K ι M _ _ _ _ f i
  exact congrFun ((finiteProductMap K ι M).apply_symm_apply f) i

theorem summation_apply : Specs.D05.M06.ExternalSum.summation_apply := by
  intro K V ι _ _ _ _ U x
  classical
  exact D05.M06.DirectSum.finite_sum_comparison U x

theorem range_summation : Specs.D05.M06.ExternalSum.range_summation := by
  intro K V ι _ _ _ U
  classical
  exact _root_.DirectSum.range_coeLinearMap

theorem surjective_iff_spanning : Specs.D05.M06.ExternalSum.surjective_iff_spanning := by
  intro K V ι _ _ _ U
  rw [← range_summation U, LinearMap.range_eq_top]

theorem mem_kernel_iff_zero_sum : Specs.D05.M06.ExternalSum.mem_kernel_iff_zero_sum := by
  intro K V ι _ _ _ _ U x
  change summationMap U x = 0 ↔ _
  rw [summation_apply U x]

theorem bijective_iff_internal : Specs.D05.M06.ExternalSum.bijective_iff_internal := by
  intro K V ι _ _ _ _ U
  classical
  exact (D05.M06.DirectSum.internal_iff_mathlib U).symm

theorem isomorphism_iff_internal : Specs.D05.M06.ExternalSum.isomorphism_iff_internal := by
  intro K V ι _ _ _ _ U
  rw [D05.M03.Isomorphism.isomorphism_iff_bijective, bijective_iff_internal U]

end D05.M06.ExternalSum
