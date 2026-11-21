import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Polynomial.Monic

/-! The bounded coefficient-limit step in paper.tex, Theorem 7.8.
Completeness includes separatedness. No completeness of the full polynomial
ring, finiteness hypothesis on the ideal, or nontriviality assumption is used. -/
universe u
namespace P103.Specs.Ch07.HenselFactorLimit
open Polynomial

def factor_limitType : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (r s : ℕ) (f : R[X]) (g h : ℕ → R[X]),
    (∀ n, (g n).Monic) → (∀ n, (h n).Monic) →
    (∀ n, (g n).natDegree = r) → (∀ n, (h n).natDegree = s) →
    (∀ n k, (g (n+1) - g n).coeff k ∈ I ^ (n+1)) →
    (∀ n k, (h (n+1) - h n).coeff k ∈ I ^ (n+1)) →
    (∀ n k, (f - g n * h n).coeff k ∈ I ^ (n+1)) →
    ∃ G H : R[X], G.Monic ∧ H.Monic ∧ G.natDegree = r ∧ H.natDegree = s ∧
      f = G * H ∧ (∀ n k, (G - g n).coeff k ∈ I ^ (n+1)) ∧
      (∀ n k, (H - h n).coeff k ∈ I ^ (n+1))

end P103.Specs.Ch07.HenselFactorLimit
