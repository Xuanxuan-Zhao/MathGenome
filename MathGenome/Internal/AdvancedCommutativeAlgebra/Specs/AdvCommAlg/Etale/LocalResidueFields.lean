import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.StandardAndPointwiseDefinitions
import Mathlib.RingTheory.Unramified.LocalRing

/-! ET-13, local assertions (paper.tex 1883–1887, 1892–1899).
Only an étale principal neighborhood is assumed, with no global finiteness
hypothesis on the algebra. The residue field action is induced by the
canonical map of localizations at the contracted primes. -/
namespace Specs.AdvCommAlg.Etale.LocalResidueFields

universe u v

/-- Extension of the prime and of its contraction agree in the local ring. -/
def primeExtensionEquality : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B),
    StandardAndPointwise.isEtaleAtValue A B q →
    q.asIdeal.map (algebraMap B (Localization.AtPrime q.asIdeal)) =
      (q.asIdeal.under A).map (algebraMap A (Localization.AtPrime q.asIdeal))

/-- The canonical extension of residue fields is finite and separable. -/
def finiteSeparableResidueFields : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B),
    StandardAndPointwise.isEtaleAtValue A B q →
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under A) q.asIdeal
    Module.Finite (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField ∧
      Algebra.IsSeparable (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField

/-- Identify the local fiber with the residue field, by the residue map. -/
def localFiberIdentification : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B),
    StandardAndPointwise.isEtaleAtValue A B q →
    ∃ e : ((Localization.AtPrime q.asIdeal) ⧸
      (q.asIdeal.under A).map (algebraMap A (Localization.AtPrime q.asIdeal)))
        ≃ₐ[Localization.AtPrime q.asIdeal] q.asIdeal.ResidueField,
    ∀ x, e (Ideal.Quotient.mk _ x) =
      algebraMap (Localization.AtPrime q.asIdeal) q.asIdeal.ResidueField x

end Specs.AdvCommAlg.Etale.LocalResidueFields
