import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.SerreDepthConditions

/-! Independent statements of SN-02 (paper.tex:4061–4079).
The Serre predicate and the associated-prime convention are those of CM-11a.
`LocalizedModule.mk x 1` is the image `x/1` in the prime localization.
-/
universe u v
namespace AdvCommAlg.Normality.Specs

def exists_associatedPrime_localized_ne_zeroType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (x : M), x ≠ 0 →
    ∃ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M ∧
      (LocalizedModule.mk x (1 : p.asIdeal.primeCompl) :
        LocalizedModule.AtPrime p.asIdeal M) ≠ 0

def serreCondition_one_iff_associatedPrimes_minimalType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M],
    CohenMacaulay.Specs.SerreConditionValue A M 1 ↔
      ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
        Minimal (fun q => q ∈ Module.support A M) p

end AdvCommAlg.Normality.Specs
