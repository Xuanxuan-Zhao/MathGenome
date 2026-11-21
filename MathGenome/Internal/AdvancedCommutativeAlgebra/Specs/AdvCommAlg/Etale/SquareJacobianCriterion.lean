import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.JacobianPresentation

/-! ET-03, paper.tex:1556–1593. Variables index rows and relations index
columns. The quotient uses exactly n equations in n variables, for any natural
number n, including zero. There is no nontriviality hypothesis. -/
namespace Specs.AdvCommAlg.Etale

universe u v
noncomputable section

open Specs.AdvCommAlg.Differentials

/-- Equivalent formulation retaining the specified generators and relations. -/
def squarePresentationCriterion : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B],
  etaleValue A B ↔ ∃ (n : ℕ) (P : Algebra.Presentation A B (Fin n) (Fin n)),
    IsUnit (presentationJacobian P).det

/-- The literal square polynomial quotient formulation of ET-03. The
isomorphism transports the determinant of the reduced partial derivatives to B. -/
def squareJacobianCriterion : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B],
  etaleValue A B ↔ ∃ (n : ℕ) (f : Fin n → MvPolynomial (Fin n) A)
    (e : B ≃ₐ[A] JacobianQuotient A n n f),
    IsUnit (e.symm (quotientJacobianMatrix A n n f).det)

/-- The determinant convention explicitly includes the empty matrix. -/
def emptySquareJacobian : Prop := ∀ (A : Type u) [CommRing A]
    (f : Fin 0 → MvPolynomial (Fin 0) A),
  (quotientJacobianMatrix A 0 0 f).det = 1

end
end Specs.AdvCommAlg.Etale
