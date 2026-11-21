import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.PrimeFin

/-! ET-16 (localization examples), paper.tex:1963–1970.
All rings, including the zero ring, and all elements a, including zero, are allowed.
The one-variable quotient is `AdjoinRoot (C a * X - 1)`.
-/
namespace Specs.AdvCommAlg.Etale.LocalizationExamples

universe u v

open Specs.AdvCommAlg.FormalLifting

def principalPresentation : Prop := ∀ (A : Type u) (L : Type v)
    [CommRing A] [CommRing L] [Algebra A L] (a : A) [IsLocalization.Away a L],
  Nonempty (L ≃ₐ[A] AdjoinRoot (Polynomial.C a * Polynomial.X - 1)) ∧
    Polynomial.derivative (Polynomial.C a * Polynomial.X - 1) = Polynomial.C a ∧
    IsUnit (algebraMap A L a)

def principalEtale : Prop := ∀ (A : Type u) (L : Type v)
    [CommRing A] [CommRing L] [Algebra A L] (a : A) [IsLocalization.Away a L],
  etaleValue A L

def localizationFormallyEtale : Prop := ∀ (A : Type u) (L : Type v)
    [CommRing A] [CommRing L] [Algebra A L] (S : Submonoid A) [IsLocalization S L],
  formallyEtaleValue A L

/-- No new denominator primes appear under algebra generation by a finite list. -/
def adjoinDenominatorPrimes : Prop := ∀ (s : Finset ℚ) (q : ℚ),
    q ∈ Algebra.adjoin ℤ (s : Set ℚ) → ∀ p : ℕ, p.Prime → p ∣ q.den →
      p ∈ s.biUnion (fun r => r.den.primeFactors)

def rationalsNotFiniteType : Prop := ¬ Algebra.FiniteType ℤ ℚ

def rationalsFormallyEtaleNotEtale : Prop :=
  formallyEtaleValue ℤ ℚ ∧ ¬ etaleValue ℤ ℚ

end Specs.AdvCommAlg.Etale.LocalizationExamples
