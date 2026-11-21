import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.Division

/-!
# Division with remainder

Lemma 1.1 (`nt:division`) of `paper.tex`. The witness uses Lean's standard
Euclidean integer quotient and remainder, including for negative dividends.
-/

namespace P203.Ch01

/-- For every integer `a` and positive integer `m`, there is a unique integer
pair `(q, r)` with `a = q * m + r` and `0 ≤ r < m`. -/
theorem divisionWithRemainder : P203Specs.Ch01.DivisionWithRemainder := by
  intro a m hm
  refine ⟨(a / m, a % m), ?_, ?_⟩
  · exact ⟨(Int.ediv_mul_add_emod a m).symm,
      Int.emod_nonneg a (Int.ne_of_gt hm), Int.emod_lt_of_pos a hm⟩
  · rintro ⟨q, r⟩ ⟨heq, hr0, hrm⟩
    have hcanonical : a / m = q ∧ a % m = r :=
      (Int.ediv_emod_unique hm).mpr
        ⟨by simpa only [Int.add_comm, Int.mul_comm] using heq.symm, hr0, hrm⟩
    exact Prod.ext hcanonical.1.symm hcanonical.2.symm

end P203.Ch01
