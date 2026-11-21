import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.RectangularPartitions
import Mathlib.FieldTheory.RatFunc.AsPolynomial

noncomputable section
namespace FiniteCombinatorics.Partition.GaussianProductSpecs

/-- The canonical inclusion ℤ[q] → ℚ[q] → ℚ(q). -/
def polynomialImage : Polynomial ℤ →+* RatFunc ℚ :=
  (algebraMap (Polynomial ℚ) (RatFunc ℚ)).comp
    (Polynomial.mapRingHom (Int.castRingHom ℚ))

/-- W28's product formula. The index `i` represents `j = i + 1`, so the
product is over exactly `1 ≤ j ≤ k`, with an empty product when `k = 0`. -/
def ProductFormula : Prop := ∀ n k : ℕ, k ≤ n →
  polynomialImage (RectangleSpecs.GValue n k) =
    ∏ i ∈ Finset.range k,
      (1 - (RatFunc.X : RatFunc ℚ) ^ (n - k + (i + 1))) /
        (1 - (RatFunc.X : RatFunc ℚ) ^ (i + 1))

end FiniteCombinatorics.Partition.GaussianProductSpecs
