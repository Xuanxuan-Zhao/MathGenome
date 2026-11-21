import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.StandardAndPointwiseDefinitions
import Mathlib.RingTheory.Ideal.Span

/-! Independent specifications for ET-09, paper.tex:1719–1745.
Standard form means a localization of a monic one-variable quotient, with
invertible derivative, as in ET-06. No ring is assumed nonzero. -/
namespace Specs.AdvCommAlg.Etale.LocalStandardCover

universe u v

open StandardAndPointwise

def localStandardNeighborhood : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
  (q : PrimeSpectrum B), isEtaleAtValue A B q →
    ∃ b : B, b ∉ q.asIdeal ∧ standardEtaleValue A (Localization.Away b)

/-- A finite principal cover, expressed by generation of the unit ideal.
The finite set is allowed to be empty. -/
def finiteStandardCover : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B], etaleValue A B →
    ∃ s : Finset B, Ideal.span (s : Set B) = ⊤ ∧
      ∀ b ∈ s, standardEtaleValue A (Localization.Away b)

/-- In a zero target ring the empty family itself is a standard cover. -/
def emptyStandardCover : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] [Subsingleton B],
    Ideal.span ((∅ : Finset B) : Set B) = ⊤ ∧
      ∀ b ∈ (∅ : Finset B), standardEtaleValue A (Localization.Away b)

end Specs.AdvCommAlg.Etale.LocalStandardCover
