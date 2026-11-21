import MathGenome.Internal.Specs.D07.Ch19.GaussianPrimesTwoSquares
import MathGenome.Internal.D07.Ch19.GaussianPrimesTwoSquaresPrimeTwoSquareCriterion
import MathGenome.Internal.D07.Foundations.IntegerArithmetic

/-! Prime representations and the complete Gaussian-prime classification. -/

namespace D07.Ch19.GaussianPrimesTwoSquares

open Specs.D07.Ch19.GaussianPrimesTwoSquares
open D07.Foundations.IntegerArithmetic

theorem prime_two_square_criterion : PrimeTwoSquareCriterion :=
  GaussianPrimesTwoSquaresPrimeTwoSquareCriterion.prime_two_square_criterion

theorem prime_of_prime_norm : PrimeOfPrimeNorm := by
  intro z hz
  apply D07.Ch10.UfdPrimeIrreducible.irreducibleIsPrime GaussianInt z
  refine ⟨?_, ?_⟩
  · intro hu
    have hnorm := Zsqrtd.norm_eq_one_iff.mpr hu
    exact hz.2.ne_one hnorm
  · intro a b hab
    have hnorm : a.norm.natAbs * b.norm.natAbs = z.norm.natAbs := by
      rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hab]
    have ha : a.norm.natAbs ∣ z.norm.natAbs := ⟨b.norm.natAbs, hnorm.symm⟩
    rcases (Nat.dvd_prime hz.2).mp ha with ha | ha
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp ha)
    · have hb : b.norm.natAbs = 1 := by
        rw [ha] at hnorm
        nlinarith [hz.2.two_le]
      exact Or.inr (Zsqrtd.norm_eq_one_iff.mp hb)

theorem one_add_i_prime : OneAddIPrime := by
  apply prime_of_prime_norm
  norm_num [PositivePrime, Zsqrtd.norm]
  exact Nat.prime_two

theorem two_ramifies : TwoRamifies := by
  ext <;> norm_num [pow_two]

theorem norm_two_associates : NormTwoAssociates := by
  intro z
  constructor
  · intro hz
    have hp : Prime z := prime_of_prime_norm z (by
      rw [hz]; norm_num [PositivePrime]; exact Nat.prime_two)
    have hd : z ∣ (2 : GaussianInt) := by
      have h : z ∣ (z.norm : GaussianInt) := by
        rw [Zsqrtd.norm_eq_mul_conj]
        exact dvd_mul_right _ _
      simpa [hz] using h
    have htwo : (2 : GaussianInt) = (⟨1, 1⟩ : GaussianInt) * ⟨1, -1⟩ := by
      ext <;> norm_num
    rw [htwo] at hd
    rcases hp.dvd_mul.mp hd with h | h
    · exact hp.associated_of_dvd one_add_i_prime h
    · have hconj : Prime (⟨1, -1⟩ : GaussianInt) :=
        prime_of_prime_norm _ (by
          norm_num [PositivePrime, Zsqrtd.norm]; exact Nat.prime_two)
      apply (hp.associated_of_dvd hconj h).trans
      apply associated_of_dvd_dvd
      · exact ⟨⟨0, 1⟩, by ext <;> norm_num⟩
      · exact ⟨⟨0, -1⟩, by ext <;> norm_num⟩
  · intro hz
    simpa [Zsqrtd.norm] using Zsqrtd.norm_eq_of_associated (by decide : (-1 : ℤ) ≤ 0) hz

theorem rational_prime_iff_nat (p : ℕ) (hp : p.Prime) :
    Prime (p : GaussianInt) ↔ p % 4 = 3 := by
  constructor
  · intro hpi
    have hns : ¬ ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 := by
      rintro ⟨a, b, hab⟩
      let z : GaussianInt := ⟨a, b⟩
      have hn : z.norm = (p : ℤ) := by
        simpa [z, Zsqrtd.norm, pow_two] using hab.symm
      have hnu : ¬ IsUnit z := by
        rw [← Zsqrtd.norm_eq_one_iff, hn, Int.natAbs_natCast]
        exact hp.ne_one
      have hsu : ¬ IsUnit (star z) := by
        simpa only [← Zsqrtd.norm_eq_one_iff, Zsqrtd.norm_conj] using hnu
      have hmul : (p : GaussianInt) = z * star z := by
        rw [← Zsqrtd.norm_eq_mul_conj, hn]
        simp
      exact (hpi.irreducible.isUnit_or_isUnit hmul).elim hnu hsu
    have hnot : ¬ (p = 2 ∨ p % 4 = 1) :=
      mt (GaussianPrimesTwoSquaresPrimeTwoSquareCriterion.prime_two_square_criterion_nat p hp).mpr hns
    rcases hp.eq_two_or_odd with h | h <;> omega
  · intro hp3
    apply D07.Ch10.UfdPrimeIrreducible.irreducibleIsPrime GaussianInt _
    by_contra hpi
    obtain ⟨u, v, _, _, _, hu, _⟩ :=
      GaussianPrimesTwoSquaresPrimeTwoSquareCriterion.gaussian_factor_norms p hp hpi
    have hs : ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 :=
      ⟨u.re, u.im, hu.symm.trans (GaussianEuclidean.norm_properties u).1⟩
    have h :=
      (GaussianPrimesTwoSquaresPrimeTwoSquareCriterion.prime_two_square_criterion_nat p hp).mp hs
    omega

theorem rational_prime_criterion : RationalPrimeCriterion := by
  intro q hq
  have heq : (q.natAbs : ℤ) = q := Int.natAbs_of_nonneg hq.1.le
  have h := rational_prime_iff_nat q.natAbs hq.2
  have hcast : (q.natAbs : GaussianInt) = (q : GaussianInt) := by
    simpa only [Int.cast_natCast] using congrArg (fun n : ℤ => (n : GaussianInt)) heq
  rw [hcast] at h
  convert h using 2; omega

/-- The integer factorization of the positive norm supplies a rational prime
divisible by the given Gaussian prime. -/
theorem exists_rational_prime_multiple (z : GaussianInt) (hz : Prime z) :
    ∃ p : ℤ, PositivePrime p ∧ z ∣ (p : GaussianInt) := by
  obtain ⟨l, hl, hprod, _⟩ :=
    unique_prime_factorization z.norm (GaussianInt.norm_pos.mpr hz.ne_zero)
  have hnorm : z ∣ (z.norm : GaussianInt) := by
    rw [Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _
  have hcast : ((l.map (Int.castRingHom GaussianInt)).prod) = (z.norm : GaussianInt) := by
    rw [List.prod_hom, hprod]
    rfl
  rw [← hcast] at hnorm
  suffices ∀ l : List ℤ, z ∣ (l.map (Int.castRingHom GaussianInt)).prod →
      ∃ p ∈ l, z ∣ (p : GaussianInt) by
    obtain ⟨p, hp, hzp⟩ := this l hnorm
    exact ⟨p, hl p hp, hzp⟩
  intro l
  induction l with
  | nil =>
    intro h
    exact (hz.not_dvd_one (by simpa using h)).elim
  | cons p l ih =>
    intro h
    have hd : z ∣ (p : GaussianInt) * (l.map (Int.castRingHom GaussianInt)).prod := by
      simpa using h
    rcases hz.dvd_mul.mp hd with hd | hd
    · exact ⟨p, List.mem_cons_self, hd⟩
    · obtain ⟨q, hq, hd⟩ := ih hd
      exact ⟨q, List.mem_cons_of_mem p hq, hd⟩

theorem gaussian_prime_classification : GaussianPrimeClassification := by
  intro z
  constructor
  · intro hz
    obtain ⟨p, hp, b, hb⟩ := exists_rational_prime_multiple z hz
    by_cases hu : IsUnit b
    · have hass : Associated z (p : GaussianInt) := by
        rw [hb]
        exact associated_mul_unit_right z b hu
      exact Or.inr (Or.inl ⟨p, hp, (rational_prime_criterion p hp).mp (hass.prime hz), hass⟩)
    · have hnorms : z.norm.natAbs * b.norm.natAbs = p.natAbs ^ 2 := by
        rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hb, Zsqrtd.norm_intCast,
          Int.natAbs_mul, pow_two]
      have hnormN : z.norm.natAbs = p.natAbs :=
        ((hp.2.mul_eq_prime_sq_iff (mt Zsqrtd.norm_eq_one_iff.mp hz.not_isUnit)
          (mt Zsqrtd.norm_eq_one_iff.mp hu)).mp hnorms).1
      have hnorm : z.norm = p := by
        simpa only [GaussianInt.abs_natCast_norm, Int.natAbs_of_nonneg hp.1.le] using
          congrArg (fun n : ℕ => (n : ℤ)) hnormN
      have hrepr : ∃ a b : ℤ, p = a ^ 2 + b ^ 2 :=
        ⟨z.re, z.im, hnorm.symm.trans (GaussianEuclidean.norm_properties z).1⟩
      rcases (prime_two_square_criterion p hp).mp hrepr with hp2 | hp1
      · exact Or.inl ((norm_two_associates z).mp (hnorm.trans hp2))
      · right; right
        rw [hnorm]
        exact ⟨hp, hp1⟩
  · rintro (hz | ⟨q, hq, hq3, hz⟩ | ⟨hn, _⟩)
    · exact hz.symm.prime one_add_i_prime
    · exact hz.symm.prime ((rational_prime_criterion q hq).mpr hq3)
    · exact prime_of_prime_norm z hn

theorem gaussian_irreducible_classification : GaussianIrreducibleClassification := by
  intro z
  exact (D07.Ch10.UfdPrimeIrreducible.primeIffIrreducible GaussianInt z).symm.trans
    (gaussian_prime_classification z)

end D07.Ch19.GaussianPrimesTwoSquares
