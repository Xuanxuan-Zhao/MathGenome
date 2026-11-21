import MathGenome.Internal.Specs.D05.M10.JordanExistence
import MathGenome.Internal.Specs.D05.M04.Similarity
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Matrix.PEquiv

/-! Independent statements for paper.tex:1622–1626. The block reversal preserves
block indices and reverses coordinates inside each block. The final theorem is
about complex matrices, with the size-zero case included. -/
noncomputable section
open scoped Classical
namespace Specs.D05.M10.TransposeSimilarity

/-- The permutation reversing every individual Jordan chain. -/
def blockReversal {r : ℕ} (a : Fin r → ℕ) : Equiv.Perm (Σ i, Fin (a i)) :=
  Equiv.sigmaCongrRight (fun _ => Fin.revPerm)

/-- Its permutation matrix, with a 1 at (i,j) exactly when j is the
reversal of i inside the same block. -/
def reversalMatrix {K : Type*} [Field K] {r : ℕ} (a : Fin r → ℕ) :
    Matrix (Σ i, Fin (a i)) (Σ i, Fin (a i)) K :=
  (blockReversal a).toPEquiv.toMatrix

def reversal_squared : Prop :=
  ∀ {K : Type*} [Field K] {r : ℕ} (a : Fin r → ℕ),
    reversalMatrix (K := K) a * reversalMatrix a = 1

def reversal_inverse : Prop :=
  ∀ {K : Type*} [Field K] {r : ℕ} (a : Fin r → ℕ),
    IsUnit (reversalMatrix (K := K) a) ∧
      (reversalMatrix (K := K) a)⁻¹ = reversalMatrix a

/-- This includes a single block as well as any finite block diagonal family.
No positive-characteristic restriction is needed for the reversal calculation. -/
def jordan_transpose : Prop :=
  ∀ {K : Type*} [Field K] {r : ℕ} (a : Fin r → ℕ) (μ : Fin r → K),
    (reversalMatrix a)⁻¹ * JordanExistence.jordanMatrix a μ * reversalMatrix a =
      (JordanExistence.jordanMatrix a μ).transpose

def complex_transpose_similarity : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
    Specs.D05.M04.Similarity.similar_value A A.transpose

end Specs.D05.M10.TransposeSimilarity
