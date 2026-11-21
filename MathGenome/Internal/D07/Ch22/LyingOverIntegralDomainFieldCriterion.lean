import MathGenome.Internal.Specs.D07.Ch22.LyingOverIntegralDomainFieldCriterion
import MathGenome.Internal.D07.Ch09.Contraction
import MathGenome.Internal.D07.Ch09.MaximalQuotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
The general field criterion used in K07.22.lying_over, and its
maximal-ideal consequence (paper.tex:7293–7310).

For the criterion, Mathlib proves that an integral algebra which is a
domain is a field over a field, and that an injective integral algebra
map reflects fields. We apply these statements to the algebra structure
of the specified homomorphism, preserving its ring operations.

For contraction, the induced map R/(M.comap f) → B/M is injective.
Reducing monic equations proves that it is integral. The source is a
domain by prime contraction, and the target is a field by maximality.
The field criterion and the maximal-quotient criterion finish the proof.
No localization, ambient domain, or module-finiteness assumption is used.
-/

universe u v

namespace D07.Ch22.LyingOverIntegralDomainFieldCriterion

open Specs.D07.Ch22.LyingOverIntegralDomainFieldCriterion

theorem integralDomainFieldCriterion : IntegralDomainFieldCriterion.{u, v} := by
  intro A D _ _ _ _ f hf hint
  letI : Algebra A D := f.toAlgebra
  letI : Algebra.IsIntegral A D := ⟨hint⟩
  exact Algebra.IsIntegral.isField_iff_isField hf

/-- Integrality descends to the actual quotient inclusion. Injectivity
of this induced map holds even when the original map is not injective. -/
theorem quotientIntegralInclusion
    {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    (f : R →+* B) (hint : f.IsIntegral) (I : Ideal B) :
    Function.Injective (Ideal.quotientMap I f le_rfl) ∧
      (Ideal.quotientMap I f le_rfl).IsIntegral :=
  ⟨Ideal.quotientMap_injective, hint.quotient⟩

theorem maximalContraction : MaximalContraction.{u, v} := by
  intro R B _ _ f _hf hint M hM
  letI : M.IsMaximal := hM
  letI : (M.comap f).IsPrime :=
    D07.Ch09.Contraction.prime_contraction R B f M hM.isPrime
  obtain ⟨hqinj, hqint⟩ := quotientIntegralInclusion f hint M
  have hfield : IsField (B ⧸ M) :=
    (D07.Ch09.MaximalQuotient.maximal_iff_isField_quotient B M).mp hM
  have hbase : IsField (R ⧸ M.comap f) :=
    (integralDomainFieldCriterion (R ⧸ M.comap f) (B ⧸ M)
      (Ideal.quotientMap M f le_rfl) hqinj hqint).mpr hfield
  exact (D07.Ch09.MaximalQuotient.maximal_iff_isField_quotient R (M.comap f)).mpr hbase

end D07.Ch22.LyingOverIntegralDomainFieldCriterion
