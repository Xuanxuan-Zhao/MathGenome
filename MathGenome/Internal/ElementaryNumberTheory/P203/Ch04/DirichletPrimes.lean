import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.DirichletPrimes
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace P203.Ch04

/-- Dirichlet's theorem with arbitrary integer residues and real bounds.
The library theorem applies also when the modulus is one. -/
theorem dirichletPrimes : P203Specs.Ch04.DirichletPrimes := by
  intro M hM a ha T
  obtain ⟨n, hn⟩ := exists_nat_gt T
  obtain ⟨q, hqn, hq, hqa⟩ := Nat.forall_exists_prime_gt_and_zmodEq n
    (q := M) (a := a) (Nat.ne_of_gt hM) (Int.isCoprime_iff_gcd_eq_one.mpr ha)
  refine ⟨q, hq.pos, hq, hn.trans ?_, ?_⟩
  · exact_mod_cast hqn
  · exact Int.modEq_iff_dvd.mp hqa.symm

end P203.Ch04
