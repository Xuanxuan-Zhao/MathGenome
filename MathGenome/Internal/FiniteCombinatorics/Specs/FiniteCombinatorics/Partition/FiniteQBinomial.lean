import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.RectangularPartitions

noncomputable section
namespace FiniteCombinatorics.Partition.FiniteQBinomialSpecs

/-- W28, the finite q-binomial identity in ℤ[q][t].
The inner `X : Polynomial ℤ` is q; the outer `X` is t, and `C`
embeds the integer q-polynomial coefficients into the polynomial ring in t.
The range `n + 1` includes precisely k = 0, …, n. -/
def Identity : Prop :=
  ∀ n : ℕ,
    (∏ i ∈ Finset.range n,
      (1 + Polynomial.X * Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ i) :
        Polynomial (Polynomial ℤ))) =
    ∑ k ∈ Finset.range (n + 1),
      Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (k * (k - 1) / 2) *
        RectangleSpecs.GValue n k) * Polynomial.X ^ k

end FiniteCombinatorics.Partition.FiniteQBinomialSpecs
