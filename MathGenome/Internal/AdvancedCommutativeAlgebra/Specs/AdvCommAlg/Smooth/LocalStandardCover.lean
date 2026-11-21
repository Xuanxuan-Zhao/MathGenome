import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.StandardPresentation
import Mathlib.RingTheory.Localization.Away.Basic

/-! Independent statements for SM-05 (paper.tex:1023–1071).
The structural map A → B is arbitrary. The localization B_g uses the
induced A-algebra structure, and standard smoothness is exactly the common
SM-03 predicate, characterized there by a finite presentation with an
invertible minor using every relation column. No nonzero-ring assumption
is imposed, and the finite covering family need not be nonempty. -/

namespace Specs.AdvCommAlg.Smooth.LocalStandardCover

universe u v

/-- Every prime of a smooth algebra has a principal standard smooth
neighbourhood over the original base. -/
def localStandard : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  smoothValue A B → ∀ (q : Ideal B) [q.IsPrime],
    ∃ g : B, g ∉ q ∧ standardSmoothValue A (Localization.Away g)

/-- A finite principal standard smooth cover, expressed by generators of
the unit ideal. In the zero ring the empty finset is allowed. -/
def finiteStandardCover : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  smoothValue A B → ∃ s : Finset B,
    Ideal.span (s : Set B) = ⊤ ∧
      ∀ g ∈ s, standardSmoothValue A (Localization.Away g)

end Specs.AdvCommAlg.Smooth.LocalStandardCover
