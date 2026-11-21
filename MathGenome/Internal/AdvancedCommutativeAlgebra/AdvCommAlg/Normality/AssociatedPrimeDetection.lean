import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.SerreDepthConditions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.AssociatedPrimeDetection

/-! Detection by associated primes, SN-02. -/
universe u v
namespace AdvCommAlg.Normality

/-- Every given nonzero element survives at an associated prime.
An associated prime containing its annihilator suffices: an element of
its prime complement cannot kill the original element. -/
theorem exists_associatedPrime_localized_ne_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (x : M) (hx : x ≠ 0) :
    ∃ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M ∧
      (LocalizedModule.mk x (1 : p.asIdeal.primeCompl) :
        LocalizedModule.AtPrime p.asIdeal M) ≠ 0 := by
  obtain ⟨p, hp, hAnn⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A x hx
  have : p.IsPrime := hp.isPrime
  let pp : PrimeSpectrum A := ⟨p, hp.isPrime⟩
  refine ⟨pp, hp, ?_⟩
  intro hzero
  change LocalizedModule.mkLinearMap p.primeCompl M x = 0 at hzero
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)).mp hzero
  apply s.property
  apply hAnn
  simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot,
    Submonoid.smul_def] using hs

/-- The `(S₁)` condition is exactly minimality in the support of every
associated prime, with the same predicates as CM-11a. -/
theorem serreCondition_one_iff_associatedPrimes_minimal
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    CohenMacaulay.SerreCondition A M 1 ↔
      ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
        Minimal (fun q => q ∈ Module.support A M) p :=
  CohenMacaulay.serreCondition_one_iff_noEmbeddedAssociatedPrimes A M

end AdvCommAlg.Normality
