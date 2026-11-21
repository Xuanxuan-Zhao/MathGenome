import MathGenome.Internal.Specs.D07.Ch10.GcdLcm
import MathGenome.Internal.D07.Ch10.Associates
import MathGenome.Internal.D07.Ch10.Divisibility
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Field.Rat
import Lean.Elab.Tactic.Omega

/-! Divisibility definitions and boundary cases for K07.10.gcd_lcm. -/

universe u

namespace D07.Ch10.GcdLcm

open Specs.D07.Ch10.GcdLcm

/-- The canonical source predicates are shared through the independent Specs. -/
def isGcd : DivisorPredicateType.{u} := IsGcd

def isLcm : DivisorPredicateType.{u} := IsLcm

theorem gcdCharacterization : GcdCharacterization.{u} := by
  intro R _ _ a b d
  rfl

theorem lcmCharacterization : LcmCharacterization.{u} := by
  intro R _ _ a b d
  rfl

theorem gcdUniqueUpToAssociates : GcdUniqueUpToAssociates.{u} := by
  intro R _ _ a b d e hd he
  exact (D07.Ch10.Associates.associatesIffMutualDivisibility R d e).mpr
    ⟨he.2.2 d hd.1 hd.2.1, hd.2.2 e he.1 he.2.1⟩

theorem lcmUniqueUpToAssociates : LcmUniqueUpToAssociates.{u} := by
  intro R _ _ a b m n hm hn
  exact (D07.Ch10.Associates.associatesIffMutualDivisibility R m n).mpr
    ⟨hm.2.2 n hn.1 hn.2.1, hn.2.2 m hm.1 hm.2.1⟩

theorem gcdAssociated : GcdAssociated.{u} := by
  intro R _ _ a b d e h
  have hde := (D07.Ch10.Associates.associatesIffMutualDivisibility R d e).mp h
  constructor
  · intro hd
    exact ⟨hde.2.trans hd.1, hde.2.trans hd.2.1,
      fun c hca hcb => (hd.2.2 c hca hcb).trans hde.1⟩
  · intro he
    exact ⟨hde.1.trans he.1, hde.1.trans he.2.1,
      fun c hca hcb => (he.2.2 c hca hcb).trans hde.2⟩

theorem lcmAssociated : LcmAssociated.{u} := by
  intro R _ _ a b m n h
  have hmn := (D07.Ch10.Associates.associatesIffMutualDivisibility R m n).mp h
  constructor
  · intro hm
    exact ⟨hm.1.trans hmn.1, hm.2.1.trans hmn.1,
      fun c hac hbc => hmn.2.trans (hm.2.2 c hac hbc)⟩
  · intro hn
    exact ⟨hn.1.trans hmn.2, hn.2.1.trans hmn.2,
      fun c hac hbc => hmn.1.trans (hn.2.2 c hac hbc)⟩

theorem gcdZeroZero : GcdZeroZero.{u} := by
  intro R _ _ d
  constructor
  · intro hd
    exact (D07.Ch10.Divisibility.zeroDividesIff R d).mp
      (hd.2.2 0 (dvd_refl 0) (dvd_refl 0))
  · rintro rfl
    exact ⟨dvd_refl 0, dvd_refl 0, fun _ hc _ => hc⟩

theorem gcdZeroRight : GcdZeroRight.{u} := by
  intro R _ _ a d
  constructor
  · intro hd
    exact (D07.Ch10.Associates.associatesIffMutualDivisibility R d a).mpr
      ⟨hd.1, hd.2.2 a (dvd_refl a) (dvd_zero a)⟩
  · intro h
    have hda := (D07.Ch10.Associates.associatesIffMutualDivisibility R d a).mp h
    exact ⟨hda.1, dvd_zero d, fun c hc _ => hc.trans hda.2⟩

theorem gcdZeroLeft : GcdZeroLeft.{u} := by
  intro R _ _ a d
  constructor
  · intro hd
    exact (gcdZeroRight R a d).mp
      ⟨hd.2.1, hd.1, fun c hc hz => hd.2.2 c hz hc⟩
  · intro h
    have hd := (gcdZeroRight R a d).mpr h
    exact ⟨hd.2.1, hd.1, fun c hz hc => hd.2.2 c hc hz⟩

theorem lcmZeroRight : LcmZeroRight.{u} := by
  intro R _ _ a m
  constructor
  · intro hm
    exact (D07.Ch10.Divisibility.zeroDividesIff R m).mp hm.2.1
  · rintro rfl
    exact ⟨dvd_zero a, dvd_refl 0, fun _ _ hc => hc⟩

theorem lcmZeroLeft : LcmZeroLeft.{u} := by
  intro R _ _ a m
  constructor
  · intro hm
    exact (D07.Ch10.Divisibility.zeroDividesIff R m).mp hm.1
  · rintro rfl
    exact ⟨dvd_refl 0, dvd_zero a, fun _ hc _ => hc⟩

theorem zeroConventions : ZeroConventions.{u} := by
  intro R _ _ a
  exact ⟨(gcdZeroZero R 0).mpr rfl,
    (gcdZeroRight R a a).mpr (Associated.refl a),
    (gcdZeroLeft R a a).mpr (Associated.refl a),
    (lcmZeroRight R a 0).mpr rfl, (lcmZeroLeft R a 0).mpr rfl⟩

/-!
A domain without gcds: polynomials over ℚ with vanishing linear coefficient.
The subring contains X^n for n ≥ 2, and contains no polynomial of degree 1.
If d were a gcd of X^5 and X^6, then X^2 | d and X^3 | d.
Thus 3 ≤ deg d ≤ 5. Degree 3 is excluded by X^2 | d, degree 4 by
 d | X^5, and degree 5 by d | X^6: each would require a factor of degree 1.
-/

private def cuspRing : Subring (Polynomial ℚ) where
  carrier := {p | p.coeff 1 = 0}
  zero_mem' := by simp
  one_mem' := by
    change (1 : Polynomial ℚ).coeff 1 = 0
    simp [Polynomial.coeff_one]
  add_mem' := by
    intro p q hp hq
    change (p + q).coeff 1 = 0
    rw [Polynomial.coeff_add, hp, hq, add_zero]
  neg_mem' := by
    intro p hp
    change (-p).coeff 1 = 0
    rw [Polynomial.coeff_neg, hp, neg_zero]
  mul_mem' := by
    intro p q hp hq
    change (p * q).coeff 1 = 0
    rw [Polynomial.mul_coeff_one, hp, hq, mul_zero, zero_mul, add_zero]

private noncomputable def cuspPower (n : ℕ) (hn : 2 ≤ n) : cuspRing :=
  ⟨Polynomial.X ^ n, by
    change (Polynomial.X ^ n : Polynomial ℚ).coeff 1 = 0
    rw [Polynomial.coeff_X_pow, ite_eq_right (by omega)]⟩

private theorem cuspPowerDvd {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hmn : 2 ≤ n - m) : cuspPower m hm ∣ cuspPower n hn := by
  refine ⟨cuspPower (n - m) hmn, Subtype.ext ?_⟩
  change (Polynomial.X : Polynomial ℚ) ^ n = Polynomial.X ^ m * Polynomial.X ^ (n - m)
  rw [← pow_add, Nat.add_sub_of_le (by omega : m ≤ n)]

private theorem cuspDegreeNeOne (p : cuspRing) :
    (p : Polynomial ℚ).natDegree ≠ 1 := by
  intro h
  have hc : (p : Polynomial ℚ).leadingCoeff = 0 := by
    rw [← Polynomial.coeff_natDegree, h]
    exact p.property
  have hz := Polynomial.leadingCoeff_eq_zero.mp hc
  simp [hz] at h

private theorem cuspDegrees {n : ℕ} (hn : 2 ≤ n) (p q : cuspRing)
    (h : cuspPower n hn = p * q) :
    (p : Polynomial ℚ).natDegree + (q : Polynomial ℚ).natDegree = n := by
  have hh : (Polynomial.X : Polynomial ℚ) ^ n =
      (p : Polynomial ℚ) * (q : Polynomial ℚ) := congrArg Subtype.val h
  have hpq : (p : Polynomial ℚ) * (q : Polynomial ℚ) ≠ 0 := by
    rw [← hh]
    exact pow_ne_zero n Polynomial.X_ne_zero
  have hdeg := Polynomial.natDegree_mul (mul_ne_zero_iff.mp hpq).1
    (mul_ne_zero_iff.mp hpq).2
  rw [← hh, Polynomial.natDegree_X_pow] at hdeg
  exact hdeg.symm

private theorem cuspNoGcd :
    ¬ ∃ d : cuspRing, IsGcd cuspRing (cuspPower 5 (by decide))
      (cuspPower 6 (by decide)) d := by
  rintro ⟨d, hd⟩
  have h2 : cuspPower 2 (by decide) ∣ d :=
    hd.2.2 _ (cuspPowerDvd (by decide) (by decide) (by decide))
      (cuspPowerDvd (by decide) (by decide) (by decide))
  have h3 : cuspPower 3 (by decide) ∣ d :=
    hd.2.2 _ (cuspPowerDvd (by decide) (by decide) (by decide))
      (cuspPowerDvd (by decide) (by decide) (by decide))
  obtain ⟨q5, h5⟩ := hd.1
  obtain ⟨q6, h6⟩ := hd.2.1
  obtain ⟨q2, h2⟩ := h2
  obtain ⟨q3, h3⟩ := h3
  have hdeg5 := cuspDegrees (by decide) d q5 h5
  have hdeg6 := cuspDegrees (by decide) d q6 h6
  have hd0 : (d : Polynomial ℚ) ≠ 0 := by
    intro hz
    have hh := congrArg Subtype.val h5
    change (Polynomial.X : Polynomial ℚ) ^ 5 = (d : Polynomial ℚ) * q5 at hh
    rw [hz, zero_mul] at hh
    exact (pow_ne_zero 5 Polynomial.X_ne_zero) hh
  have hd2 : (d : Polynomial ℚ).natDegree = 2 + (q2 : Polynomial ℚ).natDegree := by
    have hh := congrArg Subtype.val h2
    change (d : Polynomial ℚ) = Polynomial.X ^ 2 * (q2 : Polynomial ℚ) at hh
    have hq2 : (q2 : Polynomial ℚ) ≠ 0 := by
      intro hz
      apply hd0
      rw [hh, hz, mul_zero]
    rw [hh, Polynomial.natDegree_mul (pow_ne_zero 2 Polynomial.X_ne_zero) hq2,
      Polynomial.natDegree_X_pow]
  have hd3 : 3 ≤ (d : Polynomial ℚ).natDegree := by
    have hh := congrArg Subtype.val h3
    have hdiv : (Polynomial.X : Polynomial ℚ) ^ 3 ∣ (d : Polynomial ℚ) := ⟨q3, hh⟩
    simpa only [Polynomial.natDegree_X_pow] using Polynomial.natDegree_le_of_dvd hdiv hd0
  have hn2 := cuspDegreeNeOne q2
  have hn5 := cuspDegreeNeOne q5
  have hn6 := cuspDegreeNeOne q6
  omega

theorem notEveryDomainHasGcds : NotEveryDomainHasGcds := by
  intro h
  exact cuspNoGcd (h cuspRing (cuspPower 5 (by decide)) (cuspPower 6 (by decide)))

end D07.Ch10.GcdLcm
