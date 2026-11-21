import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Definitions
import Mathlib.RingTheory.Finiteness.Subalgebra

/-! Independent statement of the first assertion of SM-15
(paper.tex:1425–1429). The integer algebra structure is the canonical one;
no injectivity of the map from the integers is required. -/

namespace Specs.AdvCommAlg.Smooth

universe u v

open scoped TensorProduct

/-- Every smooth algebra has a smooth model over a finitely generated
integer subalgebra of its base. The inclusion and all scalar structures on
the tensor product are those of this actual subalgebra. -/
def finiteCoefficientModel : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    smoothValue A B →
      ∃ (A₀ : Subalgebra ℤ A) (B₀ : Type u)
        (_ : CommRing B₀) (_ : Algebra A₀ B₀),
        A₀.FG ∧ Function.Injective (algebraMap A₀ A) ∧
          Algebra.FiniteType ℤ A₀ ∧ smoothValue A₀ B₀ ∧
          Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀)

end Specs.AdvCommAlg.Smooth
