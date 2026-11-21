import MathGenome.Internal.Specs.D07.Ch19.GaussianPrimesTwoSquaresPrimeTwoSquareCriterion
import MathGenome.Internal.D07.Ch19.GaussianEuclidean
import MathGenome.Internal.D07.Ch10.UfdPrimeIrreducible
import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The prime two-square criterion via Wilson's theorem and Gaussian
factorization. No Gaussian-prime classification is imported. -/

namespace D07.Ch19.GaussianPrimesTwoSquaresPrimeTwoSquareCriterion

open Specs.D07.Ch19.GaussianPrimesTwoSquaresPrimeTwoSquareCriterion

theorem self_inverse_residues : SelfInverseResidues := by
  intro p hp x hx
  let : Fact p.Prime := ⟨hp⟩
  rw [← mul_eq_one_iff_inv_eq₀ hx]
  exact mul_self_eq_one_iff

theorem inverse_pairing_product : InversePairingProduct := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  exact FiniteField.prod_univ_units_id_eq_neg_one

theorem wilson : Wilson := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  exact ZMod.wilsons_lemma p

theorem factorial_pairing : FactorialPairing := by
  intro p hp
  exact ZMod.factorial_eq_neg_one_pow_mul_half_factorial_sq hp

theorem wilson_square_root : WilsonSquareRoot := by
  intro p hp hp4
  have hodd : Odd p := Nat.odd_iff.mpr (by omega)
  have heven : Even ((p - 1) / 2) := Nat.even_iff.mpr (by omega)
  have hpair := factorial_pairing p hodd
  rw [heven.neg_one_pow, one_mul, wilson p hp] at hpair
  refine ⟨hpair.symm, (Nat.factorial ((p - 1) / 2) : ℤ), ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  simp only [Int.cast_add, Int.cast_pow, Int.cast_natCast, Int.cast_one,
    hpair.symm, neg_add_cancel]

theorem gaussian_nonprime : GaussianNonprime := by
  intro p hp x hpx
  have hprod : (p : GaussianInt) ∣ (⟨x, 1⟩ : GaussianInt) * ⟨x, -1⟩ := by
    obtain ⟨k, hk⟩ := hpx
    refine ⟨(k : GaussianInt), ?_⟩
    ext <;> simp_all [pow_two]
  have hplus : ¬ (p : GaussianInt) ∣ (⟨x, 1⟩ : GaussianInt) := by
    rintro ⟨z, hz⟩
    have him : (1 : ℤ) = p * z.im := by
      simpa using congrArg Zsqrtd.im hz
    have : (p : ℤ) ∣ 1 := ⟨z.im, him⟩
    have : p ∣ 1 := by exact_mod_cast this
    exact hp.not_dvd_one this
  have hminus : ¬ (p : GaussianInt) ∣ (⟨x, -1⟩ : GaussianInt) := by
    rintro ⟨z, hz⟩
    have him : (-1 : ℤ) = p * z.im := by
      simpa using congrArg Zsqrtd.im hz
    have hd : (p : ℤ) ∣ -1 := ⟨z.im, him⟩
    have : (p : ℤ) ∣ 1 := (dvd_neg.mp hd)
    have : p ∣ 1 := by exact_mod_cast this
    exact hp.not_dvd_one this
  have hnp : ¬ Prime (p : GaussianInt) := by
    intro h
    exact (h.dvd_mul.mp hprod).elim hplus hminus
  refine ⟨hprod, hplus, hminus, hnp, ?_⟩
  intro hi
  exact hnp (D07.Ch10.UfdPrimeIrreducible.irreducibleIsPrime GaussianInt _ hi)

theorem gaussian_factor_norms : GaussianFactorNorms := by
  intro p hp hpi
  have hpu : ¬ IsUnit (p : GaussianInt) := by
    rw [← Zsqrtd.norm_eq_one_iff]
    simpa [Zsqrtd.norm_natCast, Int.natAbs_mul] using
      (show p * p ≠ 1 by nlinarith [hp.two_le])
  have hab : ∃ u v : GaussianInt, (p : GaussianInt) = u * v ∧
      ¬ IsUnit u ∧ ¬ IsUnit v := by
    simpa [irreducible_iff, hpu, not_forall, not_or] using hpi
  obtain ⟨u, v, huv, hu, hv⟩ := hab
  have hnorms : u.norm.natAbs = p ∧ v.norm.natAbs = p := by
    apply (hp.mul_eq_prime_sq_iff (mt Zsqrtd.norm_eq_one_iff.mp hu)
      (mt Zsqrtd.norm_eq_one_iff.mp hv)).mp
    rw [← Int.natCast_inj, Int.natCast_mul, Int.natCast_pow,
      GaussianInt.abs_natCast_norm, GaussianInt.abs_natCast_norm,
      ← Zsqrtd.norm_mul, ← huv, Zsqrtd.norm_natCast, pow_two]
  refine ⟨u, v, huv, hu, hv, ?_, ?_⟩
  · simpa only [GaussianInt.abs_natCast_norm] using congrArg (fun n : ℕ => (n : ℤ)) hnorms.1
  · simpa only [GaussianInt.abs_natCast_norm] using congrArg (fun n : ℕ => (n : ℤ)) hnorms.2

theorem prime_two_square_criterion_nat : PrimeTwoSquareCriterionNat := by
  intro p hp
  constructor
  · rintro ⟨a, b, hab⟩
    rcases hp.eq_two_or_odd with htwo | hodd
    · exact Or.inl htwo
    right
    have hmod : (p : ZMod 4) = (a : ZMod 4) ^ 2 + (b : ZMod 4) ^ 2 := by
      simpa using congrArg (fun n : ℤ => (n : ZMod 4)) hab
    by_contra hp4
    have hp3 : p % 4 = 3 := by omega
    rw [← ZMod.natCast_mod p 4, hp3] at hmod
    have hsquares : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ 3 := by decide
    exact hsquares a b hmod.symm
  · rintro (rfl | hp4)
    · exact ⟨1, 1, by norm_num⟩
    obtain ⟨_, x, hx⟩ := wilson_square_root p hp hp4
    obtain ⟨_, _, _, _, hpi⟩ := gaussian_nonprime p hp x hx
    obtain ⟨u, v, _, _, _, hu, _⟩ := gaussian_factor_norms p hp hpi
    exact ⟨u.re, u.im, hu.symm.trans (D07.Ch19.GaussianEuclidean.norm_properties u).1⟩

theorem prime_two_square_criterion : PrimeTwoSquareCriterion := by
  intro p hp
  obtain ⟨hp0, hprime⟩ := hp
  have h := prime_two_square_criterion_nat p.natAbs hprime
  have heq : (p.natAbs : ℤ) = p := Int.natAbs_of_nonneg hp0.le
  rw [heq] at h
  convert h using 2 <;> omega

end D07.Ch19.GaussianPrimesTwoSquaresPrimeTwoSquareCriterion
