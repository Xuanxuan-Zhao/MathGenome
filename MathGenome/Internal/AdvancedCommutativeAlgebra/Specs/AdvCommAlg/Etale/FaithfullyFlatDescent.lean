import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Independent specification of the descent assertion of ET-14,
paper.tex:1912–1915 and 1919–1925. The tensor product carries its
canonical left A'-algebra structure. Finite presentation over A is a
conclusion, included in étaleness, rather than a hypothesis. -/
namespace Specs.AdvCommAlg.Etale

open TensorProduct

universe u v w

/-- Étaleness descends along an arbitrary faithfully flat base change.
All commutative unital rings, including the zero ring, are allowed. -/
def faithfullyFlatDescent : Prop :=
  ∀ (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] [Module.FaithfullyFlat A A'],
    etaleValue A' (A' ⊗[A] B) → etaleValue A B

end Specs.AdvCommAlg.Etale
