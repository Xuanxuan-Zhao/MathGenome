import MathGenome.Internal.Specs.D05.M05.DetDefinition
import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Finset.Sort

/-! General Laplace expansion (paper.tex:2985–2995). All minors use the
increasing enumerations from the minor-coefficient specification. The exponent
uses one-based indices, including when the ambient Lean indices are `Fin n`.
There are no invertibility, positive-dimension, or characteristic assumptions. -/

noncomputable section
namespace Specs.D05.M15.DeterminantLine.Laplace

universe u
open scoped BigOperators

/-- The increasingly ordered complementary set has size n-k. -/
def complement {n k : ℕ} (I : Set.powersetCard (Fin n) k) :
    Set.powersetCard (Fin n) (n - k) :=
  ⟨I.valᶜ, by simp [Finset.card_compl]⟩

/-- The ordered minor is the same submatrix determinant as in MinorCoefficients. -/
def orderedMinor {K : Type u} [Field K] {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (I J : Set.powersetCard (Fin n) k) : K :=
  D05.M05.determinant (A.submatrix
    (I.val.orderEmbOfFin I.prop) (J.val.orderEmbOfFin J.prop))

/-- Sum of the paper's one-based positions. -/
def indexSum {n : ℕ} (I : Finset (Fin n)) : ℕ :=
  ∑ i ∈ I, (i.val + 1)

/-- The complete fixed-row-set formula, including k=0, k=n and n=0. -/
def general_laplace : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (k : ℕ) (I : Set.powersetCard (Fin n) k),
    D05.M05.determinant A =
      ∑ J : Set.powersetCard (Fin n) k,
        (-1 : K) ^ (indexSum I.val + indexSum J.val) *
          orderedMinor A I J * orderedMinor A (complement I) (complement J)

/-- In particular the singleton case is the usual row cofactor formula,
with the complements in their increasing `succAbove` order. -/
def cofactor_expansion : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (i : Fin (n+1)),
    D05.M05.determinant A = ∑ j : Fin (n+1),
      (-1 : K) ^ ((i.val + 1) + (j.val + 1)) * A i j *
        D05.M05.determinant (A.submatrix i.succAbove j.succAbove)

end Specs.D05.M15.DeterminantLine.Laplace
