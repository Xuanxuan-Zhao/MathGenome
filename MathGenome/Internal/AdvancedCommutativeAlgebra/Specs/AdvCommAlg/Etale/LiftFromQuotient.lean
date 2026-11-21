import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.RingTheory.TensorProduct.Basic

/-! ET-19 (first assertion). The base change is along the canonical quotient
map, and the equivalence respects the full quotient-base algebra structure.
The ideal is arbitrary; zero rings are included. -/
namespace Specs.AdvCommAlg.Etale

universe u v

open scoped TensorProduct

/-- Every étale algebra over a quotient lifts to an étale algebra over the
original ring. The lifted algebra can be chosen in the universe of the base. -/
def liftFromQuotient : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A)
    (Bbar : Type v) [CommRing Bbar] [Algebra (A ⧸ I) Bbar],
    etaleValue (A ⧸ I) Bbar →
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Algebra.Etale A B ∧ Nonempty ((A ⧸ I) ⊗[A] B ≃ₐ[A ⧸ I] Bbar)

end Specs.AdvCommAlg.Etale
