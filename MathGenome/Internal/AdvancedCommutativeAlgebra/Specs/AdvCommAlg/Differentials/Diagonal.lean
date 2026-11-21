import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal

/-! Independent statements for KD-03 (paper.tex, lines 171–190).
The tensor product has its usual left-factor B-action. No nonzero or finiteness
hypothesis is imposed. The ideal cotangent is the quotient J/J². -/
namespace Specs.AdvCommAlg.Differentials

universe u v
noncomputable section
open scoped TensorProduct

/-- The kernel of multiplication on B ⊗[A] B. -/
abbrev diagonalIdeal (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] : Ideal (B ⊗[A] B) :=
  RingHom.ker (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B)

/-- J/J², with the B-module structure induced from the left tensor factor. -/
abbrev diagonalCotangent (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] :=
  (diagonalIdeal A B).Cotangent

/-- The actual two factor actions agree on every class of J/J². -/
def diagonalActionsAgree : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (b : B) (q : diagonalCotangent A B),
    (b ⊗ₜ[A] (1 : B)) • q = ((1 : B) ⊗ₜ[A] b) • q

/-- The specified B-action on the quotient is the left factor action. -/
def diagonalLeftAction : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (b : B) (q : diagonalCotangent A B),
    b • q = (b ⊗ₜ[A] (1 : B)) • q

def diagonalEquivType :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    KaehlerDifferential A B ≃ₗ[B] diagonalCotangent A B

/-- The canonical differential module is implemented by this very quotient. -/
def diagonalEquivValue : diagonalEquivType.{u,v} :=
  fun A B _ _ _ => LinearEquiv.refl B _

def diagonalEquivApply : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] (b : B),
    diagonalEquivValue A B (universalDerivationValue A B b) =
      (diagonalIdeal A B).toCotangent
        ⟨(1 : B) ⊗ₜ[A] b - b ⊗ₜ[A] (1 : B),
          KaehlerDifferential.one_smul_sub_smul_one_mem_ideal A b⟩

end
end Specs.AdvCommAlg.Differentials
