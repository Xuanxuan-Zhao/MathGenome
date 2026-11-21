import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Polynomial
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Independent statements for KD-18, paper.tex lines 372–389.
The product of two modules represents their (finite) direct sum. Polynomial
free modules are represented by finitely supported functions, with no finiteness
assumption on the index type. All rings, including the zero ring, are allowed. -/
namespace Specs.AdvCommAlg.Differentials
open scoped TensorProduct
open KaehlerDifferential TensorProduct
universe u v w t
noncomputable section

/-- The prescribed pure-tensor formula determines the canonical splitting. -/
def tensorAlgebraDifferentials : Prop :=
  ∀ (A : Type u) (B₁ : Type v) (B₂ : Type w)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂],
    letI : Algebra B₂ (B₁ ⊗[A] B₂) := Algebra.TensorProduct.rightAlgebra
    ∃ e : Ω[(B₁ ⊗[A] B₂)⁄A] ≃ₗ[B₁ ⊗[A] B₂]
        ((B₁ ⊗[A] B₂) ⊗[B₁] Ω[B₁⁄A]) × ((B₁ ⊗[A] B₂) ⊗[B₂] Ω[B₂⁄A]),
      ∀ (b₁ : B₁) (b₂ : B₂), e (D A (B₁ ⊗[A] B₂) (b₁ ⊗ₜ b₂)) =
        (algebraMap B₂ (B₁ ⊗[A] B₂) b₂ • (1 ⊗ₜ D A B₁ b₁),
         algebraMap B₁ (B₁ ⊗[A] B₂) b₁ • (1 ⊗ₜ D A B₂ b₂))

/-- The specialization to B[Xᵢ], identifying the second summand by its dXᵢ basis. -/
def polynomialAlgebraDifferentials : Prop :=
  ∀ (A : Type u) (B : Type v) (ι : Type t)
    [CommRing A] [CommRing B] [Algebra A B],
    ∃ e : Ω[(MvPolynomial ι B)⁄A] ≃ₗ[MvPolynomial ι B]
        ((MvPolynomial ι B) ⊗[B] Ω[B⁄A]) × (ι →₀ MvPolynomial ι B),
      (∀ b : B, e (D A (MvPolynomial ι B) (MvPolynomial.C b)) =
        (1 ⊗ₜ D A B b, 0)) ∧
      (∀ i : ι, e (D A (MvPolynomial ι B) (MvPolynomial.X i)) =
        (0, Finsupp.single i 1))

end
end Specs.AdvCommAlg.Differentials
