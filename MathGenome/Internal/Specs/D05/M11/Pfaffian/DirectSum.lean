import MathGenome.Internal.Specs.D05.M11.Pfaffian
import Mathlib.Data.Matrix.Block

/-! The ordered direct sum in paper.tex:1831–1840. Both matrices are real,
and may be singular or empty. The sum equivalence puts the whole A block first. -/
noncomputable section
namespace Specs.D05.M11.Pfaffian.DirectSum

/-- The ordered concatenation of the two even coordinate blocks. -/
def blockIndex (r s : ℕ) : Fin (2*r) ⊕ Fin (2*s) ≃ Fin (2*(r+s)) :=
  finSumFinEquiv.trans (finCongr (Nat.mul_add 2 r s).symm)

/-- The usual diagonal block matrix, with zero off-diagonal blocks. -/
def blockMatrix {r s : ℕ}
    (A : Matrix (Fin (2*r)) (Fin (2*r)) ℝ)
    (B : Matrix (Fin (2*s)) (Fin (2*s)) ℝ) :
    Matrix (Fin (2*(r+s))) (Fin (2*(r+s))) ℝ :=
  fun i j => Matrix.fromBlocks A 0 0 B ((blockIndex r s).symm i) ((blockIndex r s).symm j)

def direct_sum : Prop :=
  ∀ (r s : ℕ) (A : Matrix (Fin (2*r)) (Fin (2*r)) ℝ)
    (B : Matrix (Fin (2*s)) (Fin (2*s)) ℝ),
    (∀ i j, A i j = -A j i) → (∀ i j, B i j = -B j i) →
    pfaffian_value (blockMatrix A B) = pfaffian_value A * pfaffian_value B

end Specs.D05.M11.Pfaffian.DirectSum
