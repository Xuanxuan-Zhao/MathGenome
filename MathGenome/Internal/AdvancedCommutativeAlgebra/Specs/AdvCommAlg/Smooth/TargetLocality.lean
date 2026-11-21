import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Definitions
import Mathlib.RingTheory.Localization.Away.Basic

/-! Independent statement of the first assertion of SM-07
(paper.tex:1099–1104, with proof at 1120–1160).
There is no finite type or finite presentation assumption on B.
The index set Fin n includes n = 0, and zero rings are allowed. -/
namespace Specs.AdvCommAlg.Smooth

universe u v

/-- Smoothness descends from a finite principal cover, including its
finite presentation condition. -/
def smoothTargetLocality : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) (g : Fin n → B), Ideal.span (Set.range g) = ⊤ →
      (∀ i, smoothValue A (Localization.Away (g i))) → smoothValue A B

end Specs.AdvCommAlg.Smooth
