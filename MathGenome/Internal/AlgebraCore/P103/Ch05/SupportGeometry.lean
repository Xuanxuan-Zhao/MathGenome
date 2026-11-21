import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.SupportGeometry
import MathGenome.Internal.AlgebraCore.P103.Ch05.AssociatedPrimesInterface
import MathGenome.Internal.AlgebraCore.P103.Ch05.AssociatedLocalization
import MathGenome.Internal.AlgebraCore.P103.Ch05.AssociatedFiniteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
Support geometry in Theorem 5.4 (paper.tex:984–990).
The library's support is definitionally the source's nonzero-localization
support. Its associated primes use radical annihilators; the upstream
Noetherian comparison identifies them with the source's exact annihilators.
The library's minimal-prime theorem uses nonemptiness after localization
and contraction of associated primes, as in the source proof.
-/
namespace P103.Ch05.SupportGeometry

open P103.Specs.Ch05.AssociatedPrimesInterface
open P103.Specs.Ch05.SupportGeometry
universe u v

theorem support_eq_zeroLocus : support_eq_zeroLocusType.{u,v} := by
  intro R _ _ M _ _ _
  exact Module.support_eq_zeroLocus

theorem associatedPrimes_subset_support : associatedPrimes_subset_supportType.{u,v} := by
  intro R _ _ M _ _ _ p hp
  apply Module.mem_support_iff_of_finite.mpr
  rw [AssociatedLocalization.associatedPrimes_eq_library] at hp
  exact Submodule.annihilator_top.symm.le.trans (IsAssociatedPrime.annihilator_le hp)

theorem minimalPrimes_annihilator_subset_associatedPrimes :
    minimalPrimes_annihilator_subset_associatedPrimesType.{u,v} := by
  intro R _ _ M _ _ _
  rw [AssociatedLocalization.associatedPrimes_eq_library]
  exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M

theorem minimal_support_associated : minimal_support_associatedType.{u,v} := by
  intro R _ _ M _ _ _ p hp
  apply minimalPrimes_annihilator_subset_associatedPrimes R M
  refine ⟨⟨p.isPrime, Module.mem_support_iff_of_finite.mp hp.1⟩, ?_⟩
  intro q hq hqp
  have hs : (⟨q, hq.1⟩ : PrimeSpectrum R) ∈ supportValue R M :=
    Module.mem_support_iff_of_finite.mpr hq.2
  exact hp.2 hs hqp

theorem zero_module : zero_moduleType.{u,v} := by
  intro R _ M _ _ _
  exact ⟨Module.annihilator_eq_top_iff.mpr inferInstance,
    AssociatedPrimesInterface.support_eq_empty R M,
    AssociatedPrimesInterface.associatedPrimes_eq_empty R M⟩

theorem minimalPrimes_finite : minimalPrimes_finiteType.{u} := by
  intro R _ _
  apply (AssociatedFiniteness.associatedPrimes_finite R R).subset
  have h := minimalPrimes_annihilator_subset_associatedPrimes R R
  simpa only [Module.annihilator_eq_bot.mpr (inferInstance : FaithfulSMul R R)] using h

end P103.Ch05.SupportGeometry
