import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.SurjectiveBase
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Polynomial
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Localization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.ChangeOfRingExamples

/-! Three changes of ring, paper.tex KD-25. -/
namespace AdvCommAlg.Differentials

universe u v
noncomputable section
open scoped TensorProduct

theorem away_differentials :
    Specs.AdvCommAlg.Differentials.ChangeOfRingExamples.awayDifferentials.{u,v} := by
  intro A T _ _ _ f _
  have := subsingleton_self A
  obtain ⟨e, _⟩ := localization_differential_equiv A A T (Submonoid.powers f)
  exact e.symm.injective.subsingleton

theorem rational_function_basis :
    Specs.AdvCommAlg.Differentials.ChangeOfRingExamples.rationalFunctionBasis.{u} := by
  intro K _
  let b := (Module.Basis.singleton Unit (Polynomial K)).map
    (KaehlerDifferential.polynomialEquiv K).symm
  let b' := b.ofIsLocalizedModule (RatFunc K) (nonZeroDivisors (Polynomial K))
    (KaehlerDifferential.map K K (Polynomial K) (RatFunc K))
  refine ⟨b', ?_⟩
  simp [b', b, KaehlerDifferential.map_D, RatFunc.algebraMap_X]

theorem prime_field_differentials :
    Specs.AdvCommAlg.Differentials.ChangeOfRingExamples.primeFieldDifferentials := by
  intro p _
  exact subsingleton_of_surjective ℤ (ZMod p) (ZMod.intCast_surjective)

theorem prime_field_tensor_obstruction :
    Specs.AdvCommAlg.Differentials.ChangeOfRingExamples.primeFieldTensorObstruction := by
  intro p hp
  let μ : ℤ →ₗ[ℤ] ℤ := (p : ℤ) • LinearMap.id
  have hinj : Function.Injective μ := by
    intro x y h
    exact mul_left_cancel₀ (by exact_mod_cast hp.out.ne_zero) h
  have hz : μ.rTensor (ZMod p) = 0 := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro z
    change μ.rTensor (ZMod p) (x ⊗ₜ[ℤ] z) = 0
    simp only [LinearMap.rTensor_tmul, μ, LinearMap.smul_apply,
      LinearMap.id_apply]
    rw [TensorProduct.smul_tmul]
    simp [zsmul_eq_mul]
  have : Nontrivial (ℤ ⊗[ℤ] ZMod p) :=
    (TensorProduct.lid ℤ (ZMod p)).symm.injective.nontrivial
  refine ⟨hinj, hz, inferInstance, ?_⟩
  rw [hz]
  intro h
  exact one_ne_zero ((TensorProduct.lid ℤ (ZMod p)).symm.injective
    (h (show (0 : ℤ ⊗[ℤ] ZMod p) = 0 from rfl)))

theorem prime_field_not_flat :
    Specs.AdvCommAlg.Differentials.ChangeOfRingExamples.primeFieldNotFlat := by
  intro p hp hflat
  let := hflat
  obtain ⟨hinj, _, _, hnot⟩ := prime_field_tensor_obstruction p
  exact hnot (Module.Flat.rTensor_preserves_injective_linearMap _ hinj)

end
end AdvCommAlg.Differentials
