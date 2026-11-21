import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Localization.Away.Basic

/-! The diagonal assertion of ET-13, paper.tex 1888–1890 and 1901–1908.
The tensor product has its B-algebra structure through the first factor.
The action of D = B ⊗[A] B on B is specifically multiplication.
All commutative rings, including the zero ring, are allowed. -/
namespace Specs.AdvCommAlg.Etale.Diagonal

universe u v

open scoped TensorProduct

/-- Multiplication, b ⊗ b' ↦ bb', as a B-algebra map. -/
abbrev multiplication (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] : (B ⊗[A] B) →ₐ[B] B :=
  Algebra.TensorProduct.lmul'' A

/-- The D-action on B is induced by the displayed multiplication map. -/
abbrev multiplicationAlgebra (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] : Algebra (B ⊗[A] B) B :=
  (multiplication A B).toRingHom.toAlgebra

/-- The diagonal is the quotient by a principal idempotent ideal and the
localization at its complementary idempotent. The displayed formula fixes
this identification over D on every element of the multiplication map. -/
def diagonalIdempotent : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B],
  etaleValue A B →
  letI : Algebra (B ⊗[A] B) B := multiplicationAlgebra A B
  ∃ e : B ⊗[A] B, e * e = e ∧
    RingHom.ker (multiplication A B).toRingHom = Ideal.span {e} ∧
    ∃ φ : B ≃ₐ[B ⊗[A] B] Localization.Away (1 - e),
      ∀ x : B ⊗[A] B,
        φ (multiplication A B x) =
          algebraMap (B ⊗[A] B) (Localization.Away (1 - e)) x

end Specs.AdvCommAlg.Etale.Diagonal
