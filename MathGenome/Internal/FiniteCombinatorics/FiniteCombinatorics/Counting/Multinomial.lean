import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.Multinomial

/-!
The multinomial and binomial expansions of paper.tex W04.
Mathlib's multinomial theorem applies to an arbitrary commutative ring,
including positive characteristic. On the exponent antidiagonal its natural
multinomial coefficient is exactly the prescribed factorial quotient.
-/

namespace FiniteCombinatorics.Counting.Multinomial

universe u

/-- Every natural exponent vector of total degree n occurs in the sum. -/
theorem exponent_membership (r n : ℕ) (k : Fin r → ℕ) :
    k ∈ Finset.piAntidiag Finset.univ n ↔ (∑ i, k i) = n := by
  simp

/-- Multinomial expansion, with the quotient computed in ℕ before casting. -/
theorem multinomial_expansion {R : Type u} [CommRing R] (r n : ℕ) (x : Fin r → R) :
    (∑ i, x i) ^ n =
      ∑ k ∈ Finset.piAntidiag Finset.univ n,
        (↑(n.factorial / ∏ i, (k i).factorial) : R) * ∏ i, x i ^ k i := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.multinomial, (Finset.mem_piAntidiag.mp hk).1]

/-- Setting r = 2 gives the two-variable factorial-quotient expansion. -/
theorem two_variable_expansion {R : Type u} [CommRing R] (x y : R) (n : ℕ) :
    (x + y) ^ n =
      ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) n,
        (↑(n.factorial / ((k 0).factorial * (k 1).factorial)) : R) *
          (x ^ k 0 * y ^ k 1) := by
  simpa only [Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] using
    multinomial_expansion 2 n ![x, y]

/-- The usual binomial theorem, in the same arbitrary coefficient ring. -/
theorem binomial_expansion {R : Type u} [CommRing R] (x y : R) (n : ℕ) :
    (x + y) ^ n =
      ∑ j ∈ Finset.range (n + 1), x ^ j * y ^ (n - j) * (↑(n.choose j) : R) :=
  add_pow x y n

/-- The unique exponent vector at degree zero gives 1, even for r = 0. -/
theorem zero_degree {R : Type u} [CommRing R] (r : ℕ) (x : Fin r → R) :
    (∑ k ∈ Finset.piAntidiag Finset.univ 0,
      (↑((0 : ℕ).factorial / ∏ i, (k i).factorial) : R) * ∏ i, x i ^ k i) = 1 := by
  rw [← multinomial_expansion r 0 x, pow_zero]

/-- The empty-family expansion includes both n = 0 and positive n. -/
theorem empty_family {R : Type u} [CommRing R] (n : ℕ) (x : Fin 0 → R) :
    (∑ k ∈ Finset.piAntidiag Finset.univ n,
      (↑(n.factorial / ∏ i, (k i).factorial) : R) * ∏ i, x i ^ k i) =
      if n = 0 then 1 else 0 := by
  rw [← multinomial_expansion 0 n x]
  cases n <;> simp

end FiniteCombinatorics.Counting.Multinomial
