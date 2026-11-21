import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.FactorizationValuations

namespace P203.Ch01
open P203Specs.Ch01

theorem uniquePrimeFactorization : UniquePrimeFactorization := by
  constructor
  · intro n hn
    refine ⟨n.primeFactorsList, Nat.prod_primeFactorsList hn.ne',
      fun p hp => Nat.prime_of_mem_primeFactorsList hp, ?_⟩
    exact fun k hk hkp => Nat.primeFactorsList_unique hk hkp
  · exact Nat.primeFactorsList_one

theorem integerPrimeFactorization : IntegerPrimeFactorization := by
  intro n hn
  refine ⟨?_, n.natAbs.primeFactorsList,
    fun p hp => Nat.prime_of_mem_primeFactorsList hp,
    Nat.prod_primeFactorsList (Int.natAbs_ne_zero.mpr hn), ?_,
    fun k hk hkp => Nat.primeFactorsList_unique hk hkp⟩
  · rcases lt_or_gt_of_ne hn with h | h
    · exact Or.inr (Int.sign_eq_neg_one_of_neg h)
    · exact Or.inl (Int.sign_eq_one_of_pos h)
  · rw [Nat.prod_primeFactorsList (Int.natAbs_ne_zero.mpr hn)]
    exact (Int.sign_mul_natAbs n).symm

theorem integerUnits : IntegerUnits := by
  intro n
  exact Int.isUnit_iff

theorem valuationFactorizationBridge : ValuationFactorizationBridge := by
  intro p hp n hn
  have hf : FiniteMultiplicity p n.natAbs :=
    Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, Int.natAbs_pos.mpr hn⟩
  have he : primeValuation p n = (n.natAbs.factorization p : ℕ∞) := by
    rw [primeValuation, ← Int.emultiplicity_natAbs,
      hf.emultiplicity_eq_multiplicity, Nat.multiplicity_eq_factorization hp]
  exact ⟨he, by rw [he]; exact ENat.natCast_ne_top _⟩

theorem valuationZeroAndUnits : ValuationZeroAndUnits := by
  intro p hp
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  simp [primeValuation, emultiplicity_of_one_right hp'.not_isUnit]

theorem valuationProduct : ValuationProduct := by
  intro p hp a b
  exact emultiplicity_mul (Nat.prime_iff_prime_int.mp hp)

theorem valuationPrimePowers : ValuationPrimePowers := by
  intro p _ n j
  exact pow_dvd_iff_le_emultiplicity

theorem valuationDivisibility : ValuationDivisibility := by
  refine ⟨?_, fun b => zero_dvd_iff⟩
  intro a b
  constructor
  · intro hab p _
    exact emultiplicity_le_emultiplicity_of_dvd_right hab
  · intro h
    by_cases hb : b = 0
    · simp [hb]
    have ha : a ≠ 0 := by
      intro ha
      have htwo := h 2 Nat.prime_two
      rw [ha, (valuationZeroAndUnits 2 Nat.prime_two).1] at htwo
      exact (valuationFactorizationBridge 2 Nat.prime_two b hb).2
        (top_le_iff.mp htwo)
    apply Int.natAbs_dvd_natAbs.mp
    apply (Nat.factorization_prime_le_iff_dvd
      (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)).mp
    intro p hp
    have hh := h p hp
    rw [(valuationFactorizationBridge p hp a ha).1,
      (valuationFactorizationBridge p hp b hb).1] at hh
    exact ENat.natCast_le_natCast.mp hh

/-- Finite nonzero case before extending the gcd/lcm formulas at zero. -/
theorem valuation_gcd_lcm_of_ne_zero (p : ℕ) (hp : p.Prime)
    (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    primeValuation p (Int.gcd a b : ℤ) = min (primeValuation p a) (primeValuation p b) ∧
    primeValuation p (Int.lcm a b : ℤ) = max (primeValuation p a) (primeValuation p b) := by
  have ha' := Int.natAbs_ne_zero.mpr ha
  have hb' := Int.natAbs_ne_zero.mpr hb
  have hg : (Int.gcd a b : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_ne_zero_left ha' : Nat.gcd a.natAbs b.natAbs ≠ 0)
  have hl : (Int.lcm a b : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.lcm_ne_zero ha' hb' : Nat.lcm a.natAbs b.natAbs ≠ 0)
  rw [(valuationFactorizationBridge p hp _ hg).1,
    (valuationFactorizationBridge p hp _ hl).1,
    (valuationFactorizationBridge p hp a ha).1,
    (valuationFactorizationBridge p hp b hb).1]
  simp only [Int.natAbs_natCast, Int.gcd_def, Int.lcm,
    Nat.factorization_gcd ha' hb', Nat.factorization_lcm ha' hb',
    Finsupp.inf_apply, Finsupp.sup_apply]
  constructor <;> rfl

theorem valuationGcdLcm : ValuationGcdLcm := by
  intro p hp a b
  by_cases ha : a = 0
  · subst a
    simp [primeValuation, Int.gcd_def, Int.lcm, ← Int.emultiplicity_natAbs, Int.natAbs_abs]
  by_cases hb : b = 0
  · subst b
    simp [primeValuation, Int.gcd_def, Int.lcm, ← Int.emultiplicity_natAbs, Int.natAbs_abs]
  exact valuation_gcd_lcm_of_ne_zero p hp a b ha hb

theorem finiteValuationArithmetic : FiniteValuationArithmetic := by
  intro a b ha hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [valuationProduct p hp a b,
      (valuationFactorizationBridge p hp a ha).1,
      (valuationFactorizationBridge p hp b hb).1]
    rw [← ENat.natCast_add]
    rfl
  · rw [valuationDivisibility.1 a b]
    apply forall_congr'
    intro p
    apply imp_congr_right
    intro hp
    rw [(valuationFactorizationBridge p hp a ha).1,
      (valuationFactorizationBridge p hp b hb).1]
    simp
  · intro p hp
    rw [(valuationGcdLcm p hp a b).1, (valuationGcdLcm p hp a b).2,
      (valuationFactorizationBridge p hp a ha).1,
      (valuationFactorizationBridge p hp b hb).1]
    constructor <;> rfl
  · intro p hp j
    rw [valuationPrimePowers p hp a j,
      (valuationFactorizationBridge p hp a ha).1]
    simp

theorem unequalValuationSum : UnequalValuationSum := by
  intro p _ U V j hU hV
  have hle : ((j + 1 : ℕ) : ℕ∞) ≤ primeValuation p V :=
    pow_dvd_iff_le_emultiplicity.mp hV
  have hlt : primeValuation p U < primeValuation p V := by
    rw [hU]
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self j) hle
  change emultiplicity (p : ℤ) (U + V) = _
  rw [add_comm, emultiplicity_add_of_gt hlt]
  exact hU

end P203.Ch01
