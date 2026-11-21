import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Flatness
import Mathlib.RingTheory.Smooth.Flat

/-! Flatness of smooth algebras (SM-08). -/
namespace AdvCommAlg.Smooth

universe u v

/-- A smooth algebra over any commutative base is flat as a module. -/
theorem flat (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (h : Smooth A B) : Module.Flat A B := by
  let : Algebra.Smooth A B := h
  exact Algebra.Smooth.flat A B

end AdvCommAlg.Smooth
