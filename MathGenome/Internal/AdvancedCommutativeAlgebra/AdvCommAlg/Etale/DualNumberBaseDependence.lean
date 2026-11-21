import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.DualNumberBaseDependence
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Hypersurfaces
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.SurjectiveBase
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.UnramifiedCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.QuotientsAndIdempotents

namespace AdvCommAlg.Etale.DualNumbers

universe u
open Specs.AdvCommAlg.Differentials
open Specs.AdvCommAlg.Etale.DualNumbers

/-- The polynomial structure really sends X to ε, and has kernel (X²). -/
theorem base_map_description : baseMapDescription.{u} := by
  intro K _
  constructor
  · rfl
  · exact Ideal.mk_ker

/-- Nonzero differentials in every characteristic, detected by ε ↦ 0. -/
theorem field_differentials_nonzero : fieldDifferentialsNonzero.{u} := by
  intro K _ h
  obtain ⟨e, he, _⟩ := Differentials.dual_number_presentation K
  have hz : Ideal.Quotient.mk (Ideal.span {(2 : DualQuotient K) * epsilon K}) 1 = 0 := by
    apply e.injective
    exact @Subsingleton.elim _ h _ _
  have hm : (1 : DualQuotient K) ∈ Ideal.span {(2 : DualQuotient K) * epsilon K} :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hle : Ideal.span {(2 : DualQuotient K) * epsilon K} ≤
      RingHom.ker (Differentials.dualAugmentation K).toRingHom := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change Differentials.dualAugmentation K ((2 : DualQuotient K) * epsilon K) = 0
    simp
  have hone : (1 : K) = 0 := by
    simpa using hle hm
  exact one_ne_zero hone

/-- All elements come from the polynomial base, so its relative differentials vanish. -/
theorem polynomial_differentials_zero : polynomialDifferentialsZero.{u} := by
  intro K _
  exact Differentials.subsingleton_of_surjective (Polynomial K) (DualQuotient K)
    Ideal.Quotient.mk_surjective

/-- Squaring (X²) gives (X⁴), which does not contain X². -/
theorem kernel_not_idempotent : kernelNotIdempotent.{u} := by
  intro K _ h
  have hm : (Polynomial.X ^ 2 : Polynomial K) ∈ (relationIdeal K) ^ 2 := by
    rw [h]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hd : ((Polynomial.X ^ 2) ^ 2 : Polynomial K) ∣ Polynomial.X ^ 2 := by
    simpa only [relationIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hm
  have hn := Polynomial.natDegree_le_of_dvd hd (pow_ne_zero 2 Polynomial.X_ne_zero)
  norm_num at hn

/-- Over k[X] the principal quotient is finitely presented and unramified. -/
theorem polynomial_finitely_presented_unramified : polynomialFinitelyPresentedUnramified.{u} := by
  intro K _
  have hfp : Algebra.FinitePresentation (Polynomial K) (DualQuotient K) :=
    (finitePresentation_quotient_iff (Polynomial K) (relationIdeal K)).mpr
      (Submodule.fg_span_singleton _)
  apply (finitelyPresentedUnramified_iff (Polynomial K) (DualQuotient K)).mpr
  exact ⟨hfp, (FormalLifting.formallyUnramified_iff_subsingleton_omega
      (Polynomial K) (DualQuotient K)).mpr
    (polynomial_differentials_zero K)⟩

/-- The idempotent-ideal criterion rules out étaleness over k[X]. -/
theorem polynomial_not_etale : polynomialNotEtale.{u} := by
  intro K _ h
  have hf : FormalLifting.FormallyEtale (Polynomial K) (DualQuotient K) :=
    ((AdvCommAlg.Etale.etale_iff (Polynomial K) (DualQuotient K)).mp h).2
  exact kernel_not_idempotent K
    ((formallyEtale_quotient_iff (Polynomial K) (relationIdeal K)).mp hf)

/-- Over k the same ring fails even the unramified condition. -/
theorem field_not_unramified : fieldNotUnramified.{u} := by
  intro K _ h
  have hf : FormalLifting.FormallyUnramified K (DualQuotient K) :=
    ((AdvCommAlg.Etale.unramified_iff K (DualQuotient K)).mp h).2
  exact field_differentials_nonzero K
    ((FormalLifting.formallyUnramified_iff_subsingleton_omega K (DualQuotient K)).mp hf)

end AdvCommAlg.Etale.DualNumbers
