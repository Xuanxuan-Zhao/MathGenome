import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.RingTheory.Localization.Away.Basic

/-! The finite principal-cover assertion of ET-04 (paper.tex:1597–1599).
There is no prior finite type or finite presentation assumption on B.
The family may be empty; then the span hypothesis forces B to be the zero ring.
-/
namespace Specs.AdvCommAlg.Etale

universe u v

/-- Étaleness, including finite presentation, descends from a finite
family of principal localizations generating the unit ideal. -/
def etaleTargetLocality : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) (b : Fin n → B), Ideal.span (Set.range b) = ⊤ →
      (∀ i, etaleValue A (Localization.Away (b i))) → etaleValue A B

end Specs.AdvCommAlg.Etale
