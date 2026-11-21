import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.StirlingFirst
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Independent specifications for the first polynomial identity of paper.tex W05.
The coefficients are signed integers formed from the permutation-counting array.
All finite products and sums include their usual empty-family conventions. -/
namespace FiniteCombinatorics.StirlingFallingExpansionSpec

open Polynomial
open scoped BigOperators

/-- The identity in the original integer coefficient ring. -/
def IntegerExpansion : Prop := ∀ n : ℕ,
  (∏ i ∈ Finset.range n, (X - C (i : ℤ))) =
    ∑ k ∈ Finset.range (n + 1),
      C ((-1 : ℤ) ^ (n - k) * (StirlingFirstSpec.stirlingFirst n k : ℤ)) * X ^ k

/-- Change coefficients along any unital ring homomorphism from the integers. -/
def CoefficientMapExpansion : Prop := ∀ {R : Type*} [CommRing R]
    (f : ℤ →+* R) (n : ℕ),
  Polynomial.map f (∏ i ∈ Finset.range n, (X - C (i : ℤ))) =
    ∑ k ∈ Finset.range (n + 1),
      C (f ((-1 : ℤ) ^ (n - k) * (StirlingFirstSpec.stirlingFirst n k : ℤ))) * X ^ k

/-- The corresponding polynomial identity over every commutative ring. -/
def RingExpansion : Prop := ∀ {R : Type*} [CommRing R] (n : ℕ),
  (∏ i ∈ Finset.range n, (X - C (i : R))) =
    ∑ k ∈ Finset.range (n + 1),
      C (((-1 : ℤ) ^ (n - k) * (StirlingFirstSpec.stirlingFirst n k : ℤ) : ℤ) : R) * X ^ k

/-- Evaluation retains exactly the same signed integer coefficients. -/
def EvaluationExpansion : Prop := ∀ {R : Type*} [CommRing R] (n : ℕ) (x : R),
  (∏ i ∈ Finset.range n, (x - (i : R))) =
    ∑ k ∈ Finset.range (n + 1),
      (((-1 : ℤ) ^ (n - k) * (StirlingFirstSpec.stirlingFirst n k : ℤ) : ℤ) : R) * x ^ k

end FiniteCombinatorics.StirlingFallingExpansionSpec
