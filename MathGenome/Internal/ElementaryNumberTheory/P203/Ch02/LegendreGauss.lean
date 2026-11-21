import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.LegendreGauss
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas

namespace P203.Ch02

noncomputable def legendreSymbol : ℤ → ℕ → ℤ := P203Specs.Ch02.legendreSymbol
def leastPositiveResidue : ℕ → ℤ → ℕ := P203Specs.Ch02.leastPositiveResidue
def gaussCount : ℕ → ℤ → ℕ := P203Specs.Ch02.gaussCount

/-- Integer square congruences and squares in the residue field are equivalent. -/
theorem square_congruence_iff (p : ℕ) (a : ℤ) :
    (∃ x : ℤ, x ^ 2 ≡ a [ZMOD (p : ℤ)]) ↔ IsSquare (a : ZMod p) := by
  constructor
  · rintro ⟨x, hx⟩
    have h := (ZMod.intCast_eq_intCast_iff (x ^ 2) a p).mpr hx
    exact ⟨(x : ZMod p), by simpa [pow_two] using h.symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := ZMod.intCast_surjective y
    refine ⟨x, (ZMod.intCast_eq_intCast_iff (x ^ 2) a p).mp ?_⟩
    simpa [pow_two] using hy.symm

theorem symbol_eq_mathlib (p : ℕ) [Fact p.Prime] (a : ℤ) :
    legendreSymbol a p = legendreSym p a := by
  classical
  unfold legendreSymbol P203Specs.Ch02.legendreSymbol
  by_cases ha : (p : ℤ) ∣ a
  · rw [ite_eq_left ha]
    exact ((legendreSym.eq_zero_iff p a).mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr ha)).symm
  · rw [ite_eq_right ha]
    have ha0 : (a : ZMod p) ≠ 0 := by
      exact fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
    by_cases hs : ∃ x : ℤ, x ^ 2 ≡ a [ZMOD (p : ℤ)]
    · rw [ite_eq_left hs]
      exact ((legendreSym.eq_one_iff p ha0).mpr ((square_congruence_iff p a).mp hs)).symm
    · rw [ite_eq_right hs]
      exact ((legendreSym.eq_neg_one_iff p).mpr
        (fun h => hs ((square_congruence_iff p a).mpr h))).symm

theorem leastPositiveResidue_spec (p : ℕ) (hp : 0 < p) (a : ℤ) :
    1 ≤ leastPositiveResidue p a ∧ leastPositiveResidue p a ≤ p ∧
      (leastPositiveResidue p a : ℤ) ≡ a [ZMOD (p : ℤ)] := by
  let : NeZero p := ⟨hp.ne'⟩
  unfold leastPositiveResidue P203Specs.Ch02.leastPositiveResidue
  split_ifs with hz
  · refine ⟨hp, le_rfl, ?_⟩
    apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
    simp only [Int.cast_natCast, ZMod.natCast_self]
    exact ((ZMod.val_eq_zero _).mp hz).symm
  · refine ⟨by omega, (ZMod.val_lt (a : ZMod p)).le, ?_⟩
    apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
    simp

private theorem half_eq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (p - 1) / 2 = p / 2 := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨k, hk⟩ := hodd
  omega

theorem euler_criterion (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : ℤ) :
    a ^ ((p - 1) / 2) ≡ legendreSymbol a p [ZMOD (p : ℤ)] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
  rw [Int.cast_pow, half_eq p hp, symbol_eq_mathlib]
  exact (legendreSym.eq_pow p a).symm

theorem multiplicativity (p : ℕ) [Fact p.Prime] (_hp : p ≠ 2) (a b : ℤ) :
    legendreSymbol (a * b) p = legendreSymbol a p * legendreSymbol b p := by
  simp only [symbol_eq_mathlib, legendreSym.mul]

/-- No term counted in Gauss's lemma is the zero residue. -/
private theorem term_ne_zero (p : ℕ) [Fact p.Prime] (a : ℤ)
    (ha : ¬(p : ℤ) ∣ a) (i : ℕ) (hi : i ∈ Finset.Icc 1 (p / 2)) :
    ((i : ℤ) * a : ZMod p) ≠ 0 := by
  have hi1 := (Finset.mem_Icc.mp hi).1
  have hi2 := (Finset.mem_Icc.mp hi).2
  have hip : i < p := lt_of_le_of_lt hi2
    (Nat.div_lt_self (Fact.out : p.Prime).pos (by decide))
  have hi0 : (i : ZMod p) ≠ 0 := by
    intro h
    have hz : i % p = 0 := by simpa [ZMod.val_natCast] using congrArg ZMod.val h
    rw [Nat.mod_eq_of_lt hip] at hz
    omega
  have ha0 : (a : ZMod p) ≠ 0 := by
    exact fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  simpa using mul_ne_zero hi0 ha0

theorem gauss_count_eq_mathlib (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a : ℤ) (ha : ¬(p : ℤ) ∣ a) :
    gaussCount p a = ((Finset.Ico 1 (p / 2).succ).filter
      (fun i : ℕ => p / 2 < ((a : ZMod p) * (i : ZMod p)).val)).card := by
  unfold gaussCount P203Specs.Ch02.gaussCount
  rw [half_eq p hp]
  apply congrArg Finset.card
  ext i
  have hinterval : i ∈ Finset.Icc 1 (p / 2) ↔ i ∈ Finset.Ico 1 (p / 2).succ := by
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  by_cases hi : i ∈ Finset.Icc 1 (p / 2)
  · have hz := term_ne_zero p a ha i hi
    have hv : (((i : ℤ) * a : ℤ) : ZMod p).val ≠ 0 := (ZMod.val_eq_zero _).not.mpr (by simpa only [Int.cast_mul, Int.cast_natCast] using hz)
    simp only [Finset.mem_filter, hi, hinterval.mp hi, true_and]
    unfold P203Specs.Ch02.leastPositiveResidue
    rw [ite_eq_right hv]
    have heq : (((i : ℤ) * a : ℤ) : ZMod p) = (a : ZMod p) * (i : ZMod p) := by
      simp [mul_comm]
    rw [heq]
    omega
  · simp only [Finset.mem_filter, hi, false_and, hinterval.not.mp hi]

theorem gauss_lemma (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a : ℤ) (ha : ¬(p : ℤ) ∣ a) :
    legendreSymbol a p = (-1 : ℤ) ^ gaussCount p a := by
  rw [symbol_eq_mathlib, gauss_count_eq_mathlib p hp a ha]
  exact ZMod.gauss_lemma hp (by
    exact fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h))

end P203.Ch02
