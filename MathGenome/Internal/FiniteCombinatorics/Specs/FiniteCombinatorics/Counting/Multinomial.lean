import Mathlib.Data.Nat.Choose.Multinomial

/-!
Independent specifications for the multinomial and binomial assertions of
paper.tex, W04. The summation index `piAntidiag univ n` consists exactly of
all natural exponent vectors of total degree `n` (see `ExponentMembership`).
Division takes place in ℕ before casting into the arbitrary coefficient ring.
Empty sums/products and zero powers use the conventions stated in the paper.
-/

namespace Specs.FiniteCombinatorics.Counting.Multinomial

universe u

def ExponentMembership : Prop :=
  ∀ (r n : ℕ) (k : Fin r → ℕ),
    k ∈ Finset.piAntidiag Finset.univ n ↔ (∑ i, k i) = n

def MultinomialExpansion : Prop :=
  ∀ {R : Type u} [CommRing R] (r n : ℕ) (x : Fin r → R),
    (∑ i, x i) ^ n =
      ∑ k ∈ Finset.piAntidiag Finset.univ n,
        (↑(n.factorial / ∏ i, (k i).factorial) : R) * ∏ i, x i ^ k i

/-- The direct two-variable specialization of the same exponent-vector sum. -/
def TwoVariableExpansion : Prop :=
  ∀ {R : Type u} [CommRing R] (x y : R) (n : ℕ),
    (x + y) ^ n =
      ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) n,
        (↑(n.factorial / ((k 0).factorial * (k 1).factorial)) : R) *
          (x ^ k 0 * y ^ k 1)

/-- The usual binomial theorem with natural binomial coefficients cast to R. -/
def BinomialExpansion : Prop :=
  ∀ {R : Type u} [CommRing R] (x y : R) (n : ℕ),
    (x + y) ^ n =
      ∑ j ∈ Finset.range (n + 1), x ^ j * y ^ (n - j) * (↑(n.choose j) : R)

def ZeroDegree : Prop :=
  ∀ {R : Type u} [CommRing R] (r : ℕ) (x : Fin r → R),
    (∑ k ∈ Finset.piAntidiag Finset.univ 0,
      (↑((0 : ℕ).factorial / ∏ i, (k i).factorial) : R) * ∏ i, x i ^ k i) = 1

/-- For no variables the expansion is 1 at degree zero and 0 otherwise. -/
def EmptyFamily : Prop :=
  ∀ {R : Type u} [CommRing R] (n : ℕ) (x : Fin 0 → R),
    (∑ k ∈ Finset.piAntidiag Finset.univ n,
      (↑(n.factorial / ∏ i, (k i).factorial) : R) * ∏ i, x i ^ k i) =
      if n = 0 then 1 else 0

end Specs.FiniteCombinatorics.Counting.Multinomial
