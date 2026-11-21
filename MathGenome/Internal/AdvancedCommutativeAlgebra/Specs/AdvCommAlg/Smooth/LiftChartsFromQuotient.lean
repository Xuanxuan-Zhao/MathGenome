import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.LocalStandardCover
import Mathlib.RingTheory.TensorProduct.Basic

/-! The second assertion of SM-15 (paper.tex:1430–1433, 1452–1460).
Reduction is expressed by the equivalent base change (A/J) ⊗[A] D.
The ideal is arbitrary and the finite covering family may be empty. -/
namespace Specs.AdvCommAlg.Smooth.LiftChartsFromQuotient

universe u v
open scoped TensorProduct

/-- A finite principal standard smooth cover with standard smooth lifts of
all its charts to the original base. -/
def finiteLiftedStandardCover : Prop :=
  ∀ (A : Type u) [CommRing A] (J : Ideal A)
    (C : Type v) [CommRing C] [Algebra (A ⧸ J) C],
    smoothValue (A ⧸ J) C →
    ∃ s : Finset C, Ideal.span (s : Set C) = ⊤ ∧
      ∀ g ∈ s, standardSmoothValue (A ⧸ J) (Localization.Away g) ∧
        ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
          standardSmoothValue A D ∧
            Nonempty ((A ⧸ J) ⊗[A] D ≃ₐ[A ⧸ J] Localization.Away g)

end Specs.AdvCommAlg.Smooth.LiftChartsFromQuotient
