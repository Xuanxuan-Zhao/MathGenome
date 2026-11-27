import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.NumberTheory.PrimesCongruentOne

namespace GaloisFormalization.IG

/-- A prime outside a given finite set of primes with `n ∣ p - 1`. -/
theorem exists_fresh_prime (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (_hS : ∀ q ∈ S, Nat.Prime q) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∉ S ∧ n ∣ p - 1 := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hn)
  obtain ⟨p, hp, hbound, hcongr⟩ := Nat.exists_prime_gt_modEq_one (S.sup id) hn0
  refine ⟨p, hp, ?_, (Nat.modEq_iff_dvd' hp.pos).mp hcongr.symm⟩
  intro hpS
  exact (Nat.not_le_of_gt hbound) (Finset.le_sup (f := id) hpS)

end GaloisFormalization.IG
