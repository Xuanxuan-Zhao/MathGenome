import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.GcdBezoutLcm
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch01.Division
import Mathlib.Tactic.Ring

namespace P203.Ch01
open P203Specs.Ch01

/-- Existence of an ordinary division run, by strict descent of the
nonnegative second input. -/
theorem euclideanRun_nat (u v : ℕ) :
    EuclideanRun (u : ℤ) (v : ℤ) (Nat.gcd u v : ℤ) := by
  induction v using Nat.strong_induction_on generalizing u with
  | h v ih =>
    by_cases hv : v = 0
    · subst v
      simpa using EuclideanRun.stop (u : ℤ) (Int.natCast_nonneg u)
    · have hvpos : 0 < v := Nat.pos_of_ne_zero hv
      have htail := ih (u % v) (Nat.mod_lt u hvpos) v
      have hgcd : Nat.gcd v (u % v) = Nat.gcd u v := by
        rw [Nat.gcd_comm v, ← Nat.gcd_rec, Nat.gcd_comm]
      rw [hgcd] at htail
      exact EuclideanRun.step (u / v : ℕ)
        (by exact_mod_cast hvpos)
        (by
          exact_mod_cast (by simpa [Nat.mul_comm] using (Nat.div_add_mod u v).symm :
            u = u / v * v + u % v))
        (Int.natCast_nonneg _) (by exact_mod_cast Nat.mod_lt u hvpos) htail

/-- Every permitted division step preserves the ordinary gcd. -/
theorem euclideanRun_gcd {u v d : ℤ} (h : EuclideanRun u v d) :
    d = (Int.gcd u v : ℤ) := by
  induction h with
  | stop u hu => simp [abs_of_nonneg hu]
  | @step u v r d q hv heq hr hlt tail ih =>
    rw [heq, Int.gcd_mul_right_add_left, Int.gcd_comm]
    exact ih

theorem euclideanAlgorithm : P203Specs.Ch01.EuclideanAlgorithm := by
  intro a b
  constructor
  · simpa [Int.gcd_def, Int.natCast_natAbs] using euclideanRun_nat a.natAbs b.natAbs
  · intro d hd
    simpa only [Int.gcd_def, Int.natAbs_abs] using euclideanRun_gcd hd

theorem gcdBezout : P203Specs.Ch01.GcdBezout := by
  intro a b
  refine ⟨Int.natCast_nonneg _, Int.gcd_dvd_left a b, Int.gcd_dvd_right a b,
    ?_, ⟨Int.gcdA a b, Int.gcdB a b, Int.gcd_eq_gcd_ab a b⟩, ?_⟩
  · intro c hca hcb
    exact Int.dvd_coe_gcd hca hcb
  · ext n
    constructor
    · rintro ⟨x, y, rfl⟩
      obtain ⟨k, hk⟩ := Int.dvd_add
        (dvd_mul_of_dvd_left (Int.gcd_dvd_left a b) x)
        (dvd_mul_of_dvd_left (Int.gcd_dvd_right a b) y)
      exact ⟨k, hk⟩
    · rintro ⟨k, rfl⟩
      refine ⟨Int.gcdA a b * k, Int.gcdB a b * k, ?_⟩
      rw [Int.gcd_eq_gcd_ab]
      ring

theorem zeroGcd : P203Specs.Ch01.ZeroGcd := by
  simp [P203Specs.Ch01.ZeroGcd]

theorem primeDividesProduct : P203Specs.Ch01.PrimeDividesProduct := by
  intro p _ hp a b hab
  have hab' : p.natAbs ∣ a.natAbs * b.natAbs := by
    simpa only [Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr hab
  rcases hp.dvd_mul.mp hab' with ha | hb
  · exact Or.inl (Int.natAbs_dvd_natAbs.mp ha)
  · exact Or.inr (Int.natAbs_dvd_natAbs.mp hb)

theorem coprimeCancellation : P203Specs.Ch01.CoprimeCancellation := by
  intro x y z h hdiv
  exact Int.dvd_of_dvd_mul_right_of_gcd_one hdiv h

theorem lcmProperties : P203Specs.Ch01.LcmProperties := by
  intro a b
  refine ⟨Int.natCast_nonneg _, ?_, ?_, ?_⟩
  · intro hab
    rcases mul_eq_zero.mp hab with ha | hb
    · simp [ha]
    · simp [hb]
  · intro _
    rw [Int.lcm_eq_mul_div, Int.natCast_ediv, Int.natCast_mul,
      ← Int.natCast_mul, ← Int.natAbs_mul, Int.natCast_natAbs]
  · intro M
    exact Int.coe_lcm_dvd_iff.symm

end P203.Ch01
