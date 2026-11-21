import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.StirlingSecond
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.StirlingFallingExpansion
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Data.Matrix.Mul

/-! Independent statements for the power expansion and the inverse changes of
basis in paper.tex, W05 (including the degree-zero truncation). -/
namespace FiniteCombinatorics.StirlingPowerExpansionSpec

open Polynomial
open scoped BigOperators

/-- The second Stirling array is the count of unordered nonempty blocks. -/
def IntegerExpansion : Prop := ∀ n : ℕ,
  (X : ℤ[X]) ^ n = ∑ k ∈ Finset.range (n + 1),
    C (StirlingSecond.count n k : ℤ) * ∏ i ∈ Finset.range k, (X - C (i : ℤ))

/-- Linear independence and spanning are the basis assertion for each bounded
polynomial space, over the integers rather than only over a field. -/
def FiniteDegreeBasis : Prop := ∀ d : ℕ,
  LinearIndependent ℤ (fun k : Fin (d + 1) =>
    ∏ i ∈ Finset.range k.val, (X - C (i : ℤ))) ∧
  Submodule.span ℤ (Set.range (fun k : Fin (d + 1) =>
    ∏ i ∈ Finset.range k.val, (X - C (i : ℤ)))) = Polynomial.degreeLE ℤ d

noncomputable def signedFirstMatrix (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ :=
  fun n k => (-1 : ℤ) ^ (n.val - k.val) * (StirlingFirstSpec.stirlingFirst n.val k.val : ℤ)

noncomputable def secondMatrix (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ :=
  fun n k => (StirlingSecond.count n.val k.val : ℤ)

/-- Both finite matrix products, for every truncation, are the identity. -/
def MutualInverses : Prop := ∀ d : ℕ,
  signedFirstMatrix d * secondMatrix d = 1 ∧
  secondMatrix d * signedFirstMatrix d = 1

/-- The matrices really are lower triangular, retaining every out-of-range zero. -/
def OutOfRange : Prop := ∀ d (n k : Fin (d + 1)), n < k →
  signedFirstMatrix d n k = 0 ∧ secondMatrix d n k = 0

end FiniteCombinatorics.StirlingPowerExpansionSpec
