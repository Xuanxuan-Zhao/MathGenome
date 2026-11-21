import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

/-! W43, the Frobenius singular-value bound. Singular values have the source's
one-based descending enumeration, including multiplicities and zero padding.
No positive dimension or rank hypothesis is imposed. -/
noncomputable section
open scoped BigOperators
namespace Specs.NumAnalysis206.MirskyFrobenius
open _root_.NumAnalysis206.MatrixDefinitions
universe u

/-- The sum over the smaller rectangular dimension. -/
def mirsky_frobenius_min : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A B : Mat K m n),
    (∑ i ∈ Finset.range (min m n),
      (singularValue A (i + 1) - singularValue B (i + 1)) ^ 2) ≤
        frobeniusNorm (A - B) ^ 2

/-- Every finite padded sum extending past the smaller dimension has the
same value, so the choice of zero tail does not affect the assertion. -/
def singular_difference_sum_eq_min : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A B : Mat K m n)
    (N : ℕ), min m n ≤ N →
    (∑ i ∈ Finset.range N,
      (singularValue A (i + 1) - singularValue B (i + 1)) ^ 2) =
    ∑ i ∈ Finset.range (min m n),
      (singularValue A (i + 1) - singularValue B (i + 1)) ^ 2

/-- In particular the sum over the full domain dimension satisfies W43. -/
def mirsky_frobenius : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A B : Mat K m n),
    (∑ i ∈ Finset.range n,
      (singularValue A (i + 1) - singularValue B (i + 1)) ^ 2) ≤
        frobeniusNorm (A - B) ^ 2
end Specs.NumAnalysis206.MirskyFrobenius
