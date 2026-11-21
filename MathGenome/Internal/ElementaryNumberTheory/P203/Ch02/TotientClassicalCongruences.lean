import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.TotientClassicalCongruences
import Mathlib.NumberTheory.Wilson
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.ZMod.Units

namespace P203.Ch02
open P203Specs.Ch02

universe u

/-- Cardinality of the source's unit group equals the standard totient. -/
theorem totient_eq_natTotient (m : ℕ) (hm : 0 < m) : totient m = m.totient := by
  let : NeZero m := ⟨hm.ne'⟩
  unfold totient ResidueUnits
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- Casting the bounded natural representatives gives exactly the bounded
integer representatives, preserving the ordinary gcd condition. -/
private def representativeEquiv (m : ℕ) :
    {a : ℕ // a < m ∧ m.Coprime a} ≃
    {a : ℤ // 0 ≤ a ∧ a < (m : ℤ) ∧ Int.gcd a m = 1} where
  toFun a := ⟨a, Int.natCast_nonneg _, by exact_mod_cast a.property.1, by
    simpa [Int.gcd_natCast_natCast, Nat.gcd_comm] using a.property.2⟩
  invFun a := ⟨a.val.toNat, by omega, by
    have hcast : (a.val.toNat : ℤ) = a.val := Int.toNat_of_nonneg a.property.1
    have h := a.property.2.2
    rw [← hcast, Int.gcd_natCast_natCast, Nat.gcd_comm] at h
    exact h⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv a := by apply Subtype.ext; exact Int.toNat_of_nonneg a.property.1

theorem totientCardinality : TotientCardinality := by
  intro m hm
  refine ⟨totient_eq_natTotient m hm, ?_⟩
  rw [totient_eq_natTotient m hm, Nat.totient_eq_card_lt_and_coprime]
  exact Nat.card_congr (representativeEquiv m)

theorem residueUnitCriterion : ResidueUnitCriterion := by
  intro m a
  rw [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm,
    Int.isCoprime_iff_gcd_eq_one]

theorem totientOne : TotientOne := by
  change totient 1 = 1
  rw [totient_eq_natTotient 1 (by decide), Nat.totient_one]

theorem totientPrimePower : TotientPrimePower := by
  intro p hp k hk
  rw [totient_eq_natTotient _ (pow_pos hp.pos _)]
  exact Nat.totient_prime_pow hp hk

theorem totientProduct : TotientProduct := by
  intro m hm
  rw [totient_eq_natTotient m hm]
  simpa only [one_div] using Nat.totient_eq_mul_prod_factors m

theorem totientMultiplicative : TotientMultiplicative := by
  intro m n hm hn hc
  rw [totient_eq_natTotient _ (Nat.mul_pos hm hn),
    totient_eq_natTotient m hm, totient_eq_natTotient n hn]
  exact Nat.totient_mul hc

theorem finiteGroupOrder : FiniteGroupOrder.{u} := by
  intro G _ _ g
  exact ⟨orderOf_pos g, pow_orderOf_eq_one g,
    fun d hd h => orderOf_le_of_pow_eq_one hd h,
    fun _ => orderOf_dvd_iff_zpow_eq_one.symm, orderOf_dvd_natCard g⟩

theorem eulerCongruence : EulerCongruence := by
  intro m hm a ha
  obtain ⟨u, hu⟩ := (residueUnitCriterion m a).mpr ha
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have h := congrArg (fun v : (ZMod m)ˣ => (v : ZMod m)) (ZMod.pow_totient u)
  have hpow : (a : ZMod m) ^ m.totient = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, hu] using h
  simpa only [Int.cast_sub, Int.cast_pow, Int.cast_one, totient_eq_natTotient m hm]
    using sub_eq_zero.mpr hpow

theorem fermatUnitCongruence : FermatUnitCongruence := by
  intro p hp a ha
  let : Fact p.Prime := ⟨hp⟩
  have hz : (a : ZMod p) ≠ 0 := by
    exact fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa only [Int.cast_sub, Int.cast_pow, Int.cast_one] using
    sub_eq_zero.mpr (ZMod.pow_card_sub_one_eq_one hz)

theorem fermatAllResidues : FermatAllResidues := by
  intro p hp a
  let : Fact p.Prime := ⟨hp⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa only [Int.cast_sub, Int.cast_pow] using
    sub_eq_zero.mpr (ZMod.pow_card (a : ZMod p))

theorem wilsonCriterion : WilsonCriterion := by
  intro m hm
  rw [Nat.prime_iff_fac_equiv_neg_one (ne_of_gt hm)]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_eq_zero_iff_eq_neg]

end P203.Ch02
