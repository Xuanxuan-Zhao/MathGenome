import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.RationalRoots
import Mathlib.RingTheory.Localization.Rat
import Mathlib.Tactic.NormNum

namespace P203.Ch05.RationalRoots

/-- The fraction-ring API's numerator and denominator agree up to units with
Lean's normalized rational numerator and positive denominator. -/
theorem normalized_root_divisibility (P : Polynomial ℤ) (r : ℚ)
    (hr : Polynomial.aeval r P = 0) :
    r.num ∣ P.coeff 0 ∧ (r.den : ℤ) ∣ P.leadingCoeff := by
  have hn := num_dvd_of_is_root hr
  have hd := den_dvd_of_is_root hr
  exact ⟨(r.associated_num_den.1.dvd_iff_dvd_left).mp hn,
    (r.associated_num_den.2.dvd_iff_dvd_left).mp hd⟩

theorem rational_roots : P203Specs.Ch05.RationalRoots.NonzeroRoot := by
  intro P _hdegree _hlead p q hq hcop _hnonzero hroot
  have hc : Nat.Coprime p.natAbs q.natAbs := by
    simpa [Nat.coprime_iff_gcd_eq_one, Int.gcd_eq_natAbs] using hcop
  have h := normalized_root_divisibility P ((p : ℚ) / q) hroot
  rwa [Rat.num_div_eq_of_coprime hq hc, Rat.den_div_eq_of_coprime hq hc] at h

theorem zero_root : P203Specs.Ch05.RationalRoots.ZeroRoot := by
  intro P p q hq hcop hz hroot
  have hc : Nat.Coprime p.natAbs q.natAbs := by
    simpa [Nat.coprime_iff_gcd_eq_one, Int.gcd_eq_natAbs] using hcop
  have hp := Rat.num_div_eq_of_coprime hq hc
  have hd := Rat.den_div_eq_of_coprime hq hc
  rw [hz] at hp hd
  refine ⟨?_, by simpa using hp.symm, by simpa using hd.symm⟩
  rw [← Polynomial.coeff_zero_eq_aeval_zero'] at hroot
  change ((P.coeff 0 : ℤ) : ℚ) = 0 at hroot
  exact_mod_cast hroot

theorem monic_root : P203Specs.Ch05.RationalRoots.MonicRoot := by
  intro P hP r hr
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic hP hr
  exact ⟨z, hz⟩

theorem irrational_nth_root : P203Specs.Ch05.RationalRoots.IrrationalNthRoot := by
  intro k m hk hm r hr hpow
  apply irrational_nrt_of_notint_nrt k (m : ℤ) (by simpa using hpow) _ (lt_of_lt_of_le (by decide : 0 < 2) hk)
  rintro ⟨z, hz⟩
  have hznonneg : 0 ≤ z := by exact_mod_cast (hz ▸ hr)
  have hznat : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hznonneg
  apply hm
  refine ⟨z.toNat, ?_⟩
  have hreal : ((z.toNat : ℕ) : ℝ) = r := by
    rw [hz]
    exact_mod_cast hznat
  exact_mod_cast (hreal ▸ hpow)

theorem irrational_sqrt : P203Specs.Ch05.RationalRoots.IrrationalSqrt := by
  intro m hm
  exact irrational_nth_root 2 m (by decide) hm (Real.sqrt (m : ℝ))
    (Real.sqrt_nonneg _) (Real.sq_sqrt (Nat.cast_nonneg m))

end P203.Ch05.RationalRoots
