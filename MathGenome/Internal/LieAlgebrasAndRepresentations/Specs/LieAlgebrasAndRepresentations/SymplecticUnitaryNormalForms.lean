import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! The compact matrix normal forms in the symplectic case of LA-J07. -/

namespace Specs.LieAlgebrasAndRepresentations.SymplecticUnitaryNormalForms

open Matrix
open ClassicalRootsC

abbrev Sp (n : ℕ) := symplecticGroup (Fin n) ℂ

/-- The diagonal with the first `p` quaternionic coordinates positive. -/
def signatureDiagonal (n p : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun i => if i.val < p then 1 else -1

def signatureMatrix (n p : ℕ) : Mat n :=
  fromBlocks (signatureDiagonal n p) 0 0 (signatureDiagonal n p)

def squareOneType : Prop :=
  ∀ n : ℕ, 0 < n → ∀ A : Sp n,
    (A : Mat n)ᴴ * (A : Mat n) = 1 →
    (A : Mat n) * (A : Mat n) = 1 →
    ∃ p : ℕ, p ≤ n ∧ ∃ B : Sp n, (B : Mat n)ᴴ * (B : Mat n) = 1 ∧
      ((B * A * B⁻¹ : Sp n) : Mat n) = signatureMatrix n p

def squareNegOneType : Prop :=
  ∀ n : ℕ, 0 < n → ∀ A : Sp n,
    (A : Mat n)ᴴ * (A : Mat n) = 1 →
    (A : Mat n) * (A : Mat n) = -1 →
    ∃ B : Sp n, (B : Mat n)ᴴ * (B : Mat n) = 1 ∧
      B * A * B⁻¹ = SymplecticGroup.symJ (Fin n) ℂ

end Specs.LieAlgebrasAndRepresentations.SymplecticUnitaryNormalForms
