import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.OddPrimeValuationLift
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch01.FactorizationValuations
import Mathlib.NumberTheory.Multiplicity

namespace P203.Ch02

open P203Specs.Ch01 P203Specs.Ch02

/-- Lifting the exponent for every signed integer congruent to one at an
odd prime, with nonzero differences and the finite valuation formula. -/
theorem oddPrimeValuationLift : OddPrimeValuationLift := by
  intro p hp hodd u hcong hu
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnot : ¬ (p : ℤ) ∣ u := by
    intro hpu
    exact hpInt.not_dvd_one ((dvd_iff_dvd_of_dvd_sub hcong).mp hpu)
  have hbase : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hfinite : primeValuation p (u - 1) ≠ ⊤ :=
    (Ch01.valuationFactorizationBridge p hp (u - 1) hbase).2
  have hlift : primeValuation p (u ^ p - 1) =
      primeValuation p (u - 1) + 1 := by
    simpa only [primeValuation, one_pow] using
      (emultiplicity_pow_prime_sub_pow_prime hpInt hodd hcong hnot)
  have hpower : u ^ p - 1 ≠ 0 := by
    intro hz
    have htop := hlift
    rw [hz, (Ch01.valuationZeroAndUnits p hp).1] at htop
    simpa [hfinite] using htop.symm
  refine ⟨hbase, hpower, hlift, ?_⟩
  rw [hlift, ENat.toNat_add hfinite (by simp)]
  rfl

end P203.Ch02
