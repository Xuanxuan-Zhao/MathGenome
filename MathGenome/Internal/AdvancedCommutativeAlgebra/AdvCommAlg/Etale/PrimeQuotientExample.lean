import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.PrimeQuotientExample
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.FlatUnramifiedCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.SurjectiveBase
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.UnramifiedCriterion
import Mathlib.RingTheory.FinitePresentation

/-! The prime quotient example of ET-16. Surjectivity kills relative
differentials, while tensoring the injective integer multiplication map
exhibits the failure of flatness. -/
namespace AdvCommAlg.Etale

open scoped TensorProduct
open Specs.AdvCommAlg.Etale.PrimeQuotient (multiplication)

theorem prime_multiplication_injective :
    Specs.AdvCommAlg.Etale.PrimeQuotient.multiplicationInjective := by
  intro p hp
  change Function.Injective (fun z : ℤ => (p : ℤ) * z)
  exact mul_right_injective₀ (by exact_mod_cast hp.out.ne_zero)

theorem prime_tensor_zero : Specs.AdvCommAlg.Etale.PrimeQuotient.tensorZero := by
  intro p hp
  apply TensorProduct.ext'
  intro x z
  change x ⊗ₜ[ℤ] ((p : ℤ) * z) = 0
  rw [← smul_eq_mul, ← TensorProduct.smul_tmul]
  simp [zsmul_eq_mul]

theorem prime_tensor_nonzero : Specs.AdvCommAlg.Etale.PrimeQuotient.tensorNonzero := by
  intro p hp
  let e := TensorProduct.AlgebraTensorModule.rid ℤ (ZMod p) (ZMod p)
  exact ⟨e.toEquiv.nontrivial, ⟨e⟩⟩

theorem prime_quotient_properties : Specs.AdvCommAlg.Etale.PrimeQuotient.properties := by
  intro p hp
  have hsurj : Function.Surjective (algebraMap ℤ (ZMod p)) := ZMod.intCast_surjective
  have hfin : Algebra.FiniteType ℤ (ZMod p) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId ℤ (ZMod p)) hsurj
  have hfp : Algebra.FinitePresentation ℤ (ZMod p) :=
    Algebra.FinitePresentation.of_finiteType.mp hfin
  have hΩ := Differentials.subsingleton_of_surjective ℤ (ZMod p) hsurj
  have hunr : Unramified ℤ (ZMod p) :=
    (unramified_iff ℤ (ZMod p)).mpr ⟨hfin,
      (FormalLifting.formallyUnramified_iff_subsingleton_omega ℤ (ZMod p)).mpr hΩ⟩
  have hnflat : ¬ Module.Flat ℤ (ZMod p) := by
    intro hflat
    let := hflat
    have hinj := Module.Flat.lTensor_preserves_injective_linearMap
      (M := ZMod p) (multiplication p) (prime_multiplication_injective p)
    rw [prime_tensor_zero p] at hinj
    have hz : (1 : ZMod p) ⊗ₜ[ℤ] (1 : ℤ) = 0 := hinj (by simp)
    have h10 : (1 : ZMod p) = 0 := by
      simpa using congrArg (TensorProduct.rid ℤ (ZMod p)) hz
    exact one_ne_zero h10
  exact ⟨hfp, hunr, hnflat, fun h => hnflat
    ((etale_iff_finitePresentation_flat_subsingleton_omega ℤ (ZMod p)).mp h).2.1⟩

end AdvCommAlg.Etale
