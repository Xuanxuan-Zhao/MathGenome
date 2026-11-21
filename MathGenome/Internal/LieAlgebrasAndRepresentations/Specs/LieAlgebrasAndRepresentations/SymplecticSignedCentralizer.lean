import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
import Mathlib.Algebra.Lie.Prod

/-!
LA-J07, notes/005/lie-algebras-and-representations.tex:4973–4978, 5060–5064.
The signed compact involution acts by conjugation with `diag(D,D)` in the
D08-C coordinates. Its fixed complex algebra is the centralizer below.
-/

namespace Specs.LieAlgebrasAndRepresentations.SymplecticSignedCentralizer

open ClassicalRootsC Matrix

noncomputable section

attribute [local instance] LieRing.ofAssociativeRing

/-- The first `p` quaternionic coordinates have sign `+1`. -/
def signatureDiagonal (n p : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => if i.val < p then 1 else -1

/-- The signature matrix acts with the same signs on both complex halves. -/
def signatureMatrix (n p : ℕ) : Mat n :=
  fromBlocks (signatureDiagonal n p) 0 0 (signatureDiagonal n p)

/-- The complex Lie subalgebra of the original symplectic algebra commuting
with the signature matrix. -/
def signedCentralizer (n p : ℕ) : LieSubalgebra ℂ (sp n) where
  carrier := {X | Commute (signatureMatrix n p) (X : Mat n)}
  zero_mem' := Commute.zero_right _
  add_mem' := Commute.add_right
  smul_mem' := fun c _ h => Commute.smul_right h c
  lie_mem' := by
    intro X Y hX hY
    change Commute (signatureMatrix n p)
      ((X : Mat n) * (Y : Mat n) - (Y : Mat n) * (X : Mat n))
    exact (hX.mul_right hY).sub_right (hY.mul_right hX)

@[simp]
theorem mem_signedCentralizer {n p : ℕ} (X : sp n) :
    X ∈ signedCentralizer n p ↔
      signatureMatrix n p * (X : Mat n) = (X : Mat n) * signatureMatrix n p :=
  Iff.rfl

/-- The full centralizer, including the cases `p = 0` and `p = n`,
is a product of the two symplectic Lie algebras. -/
def signedCentralizerEquivType : Prop :=
  ∀ (n p : ℕ), p ≤ n →
    Nonempty (signedCentralizer n p ≃ₗ⁅ℂ⁆ (sp p × sp (n - p)))

end
end Specs.LieAlgebrasAndRepresentations.SymplecticSignedCentralizer
