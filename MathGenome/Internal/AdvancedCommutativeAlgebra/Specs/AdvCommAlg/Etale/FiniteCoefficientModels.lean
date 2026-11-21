import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.RingTheory.TensorProduct.Basic

/-! ET-15, first assertion (paper.tex:1938–1940, 1946–1954).
The coefficient ring is a finitely generated ℤ-subalgebra of the original
base. The base-change identification retains its full A-algebra structure.
No Noetherian or nontriviality assumption is made.
-/
namespace Specs.AdvCommAlg.Etale

universe u v

open scoped TensorProduct

/-- Every étale algebra has an étale model over a finitely generated
ℤ-subalgebra of its base ring. The model can lie in the universe of the base. -/
def finiteCoefficientModels : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    etaleValue A B →
      ∃ (A₀ : Subalgebra ℤ A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
        A₀.FG ∧ etaleValue A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀)

end Specs.AdvCommAlg.Etale
