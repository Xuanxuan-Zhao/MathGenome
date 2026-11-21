import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.StandardAndPointwiseDefinitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.LocusDefinitions
import Mathlib.RingTheory.Etale.Locus

/-! Independent specifications for the locus assertion of ET-04
(paper.tex:1599–1607, 1627–1632). The comparison with prime-local
formal étaleness assumes finite presentation over the original base.
Support refers to the entire localized module, with no residue-field tensor.
All commutative unital rings, including the zero ring, are allowed. -/
namespace Specs.AdvCommAlg.Etale.OpenLocus

universe u v

open StandardAndPointwise

def neighborhoodIffIsEtaleAt : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
  (q : PrimeSpectrum B),
  isEtaleAtValue A B q ↔ Algebra.IsEtaleAt A q.asIdeal

def neighborhoodIffFormal : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
  (q : PrimeSpectrum B),
  isEtaleAtValue A B q ↔
    FormalLifting.formallyEtaleValue A (Localization.AtPrime q.asIdeal)

def locusEqMathlib : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B],
  etaleLocusValue A B = Algebra.etaleLocus A B

def isOpenEtaleLocus : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B],
  IsOpen (etaleLocusValue A B)

def locusEqSmoothDiffSupport : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B],
  etaleLocusValue A B =
    Smooth.smoothLocusValue A B \ Module.support B (KaehlerDifferential A B)

/-- Explicitly record the source's meaning of differential support. -/
def differentialSupportIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B),
  q ∈ Module.support B (KaehlerDifferential A B) ↔
    Nontrivial (LocalizedModule q.asIdeal.primeCompl (KaehlerDifferential A B))

end Specs.AdvCommAlg.Etale.OpenLocus
