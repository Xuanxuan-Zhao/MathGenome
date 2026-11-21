import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Definitions
import Mathlib.RingTheory.Flat.Basic

/-! Independent statement of SM-08, paper.tex:1183–1225. -/
namespace Specs.AdvCommAlg.Smooth

universe u v

/-- Every smooth algebra is flat over its specified base. Both rings may be
zero; no Noetherian or other additional hypothesis is imposed. -/
def flatness : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  smoothValue A B → Module.Flat A B

end Specs.AdvCommAlg.Smooth
