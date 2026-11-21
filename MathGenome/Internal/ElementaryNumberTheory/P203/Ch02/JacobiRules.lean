import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.JacobiRules
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch02.QuadraticReciprocity
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace P203.Ch02

/-- The same standard Jacobi symbol as in the independent specification. -/
def jacobiSymbol : ℤ → ℕ → ℤ := P203Specs.Ch02.jacobiSymbol

private theorem jacobi_prod (a : ℤ) (s : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ p ∈ s, f p ≠ 0) :
    jacobiSym a (∏ p ∈ s, f p) = ∏ p ∈ s, jacobiSym a (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp,
      jacobiSym.mul_right' a (hf p (Finset.mem_insert_self p s))
        (Finset.prod_ne_zero_iff.mpr (fun q hq => hf q (Finset.mem_insert_of_mem hq))),
      ih (fun q hq => hf q (Finset.mem_insert_of_mem hq))]

theorem jacobi_factorization : P203Specs.Ch02.JacobiFactorization := by
  intro a m hm
  change jacobiSym a m = _
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hm.pos.ne']
  rw [jacobi_prod]
  · apply Finset.prod_congr rfl
    intro p hp
    let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    rw [jacobiSym.pow_right, ← jacobiSym.legendreSym.to_jacobiSym,
      ← symbol_eq_mathlib]
    rfl
  · intro p hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem jacobi_one : P203Specs.Ch02.JacobiOne := jacobiSym.one_right

theorem jacobi_prime : P203Specs.Ch02.JacobiPrime := by
  intro p _ _ a
  change jacobiSym a p = P203Specs.Ch02.legendreSymbol a p
  rw [← jacobiSym.legendreSym.to_jacobiSym, ← symbol_eq_mathlib]
  rfl

theorem jacobi_reduction : P203Specs.Ch02.JacobiReduction := by
  intro a m hm
  exact ⟨Int.emod_nonneg _ (by exact_mod_cast hm.pos.ne'),
    Int.emod_lt_of_pos _ (by exact_mod_cast hm.pos), jacobiSym.mod_left a m⟩

theorem jacobi_residue_class : P203Specs.Ch02.JacobiResidueClass := by
  intro a b m _ hab
  exact jacobiSym.mod_left' hab

theorem jacobi_multiplicativity : P203Specs.Ch02.JacobiMultiplicativity := by
  constructor
  · intro a b m _
    exact jacobiSym.mul_left a b m
  · intro a m n hm hn
    exact jacobiSym.mul_right' a hm.pos.ne' hn.pos.ne'

theorem jacobi_zero : P203Specs.Ch02.JacobiZero := by
  intro a m hm
  let : NeZero m := ⟨hm.pos.ne'⟩
  change jacobiSym a m = 0 ↔ _
  rw [jacobiSym.eq_zero_iff_not_coprime]
  have hg : 0 < Int.gcd a (m : ℤ) := Int.gcd_pos_iff.mpr
    (Or.inr (by exact_mod_cast hm.pos.ne'))
  omega

theorem jacobi_supplement_neg_one : P203Specs.Ch02.JacobiSupplementNegOne := by
  intro m hm
  change jacobiSym (-1) m = _
  rw [jacobiSym.at_neg_one hm, ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hm),
    odd_half_eq m (Nat.odd_iff.mp hm)]

theorem jacobi_supplement_two : P203Specs.Ch02.JacobiSupplementTwo := by
  intro m hm
  change jacobiSym 2 m = _
  rw [jacobiSym.at_two hm]
  exact chi_eight_eq_source_sign m (Nat.odd_iff.mp hm)

theorem jacobi_reciprocity : P203Specs.Ch02.JacobiReciprocity := by
  intro a m ha hm
  change jacobiSym (a : ℤ) m = _
  rw [odd_half_eq a (Nat.odd_iff.mp ha), odd_half_eq m (Nat.odd_iff.mp hm)]
  exact jacobiSym.quadratic_reciprocity ha hm

open P203Specs.Ch02 (JacobiEvaluation)

/-- Strong induction on the positive odd denominator constructs a finite run.
The extracted odd part divides the positive remainder and is therefore strictly
smaller than the old denominator. -/
theorem jacobi_termination : P203Specs.Ch02.JacobiTermination := by
  intro a m
  induction m using Nat.strong_induction_on generalizing a with
  | h m ih =>
    intro hm
    by_cases hm1 : m = 1
    · subst m
      exact ⟨1, JacobiEvaluation.one a⟩
    have hmgt : 1 < m := by have := hm.pos; omega
    by_cases hr0 : a % (m : ℤ) = 0
    · exact ⟨0, JacobiEvaluation.zero hm hmgt hr0⟩
    let r : ℕ := (a % (m : ℤ)).toNat
    have hr : (r : ℤ) = a % (m : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.pos.ne'))
    have hrpos : 0 < r := by
      have hn := Int.emod_nonneg a (show (m : ℤ) ≠ 0 by exact_mod_cast hm.pos.ne')
      have : (0 : ℤ) < (r : ℤ) := by omega
      exact_mod_cast this
    obtain ⟨v, c, hc, hrc⟩ := Nat.exists_eq_two_pow_mul_odd hrpos.ne'
    have hcm : c < m := by
      have hle : c ≤ r := by
        rw [hrc]
        exact Nat.le_mul_of_pos_left c (by positivity)
      have hrlt : r < m := by
        have := Int.emod_lt_of_pos a (show (0 : ℤ) < m by exact_mod_cast hm.pos)
        exact_mod_cast (show (r : ℤ) < (m : ℤ) by omega)
      omega
    have hrem : a % (m : ℤ) = (2 : ℤ) ^ v * (c : ℤ) := by
      rw [← hr, hrc]
      push_cast
      rfl
    by_cases hc1 : c = 1
    · refine ⟨_, JacobiEvaluation.power (v := v) hm hmgt ?_⟩
      simpa [hc1] using hrem
    obtain ⟨z, hz⟩ := ih c hcm (m : ℤ) hc
    exact ⟨_, JacobiEvaluation.step hm hmgt hc (by have := hc.pos; omega) hcm hrem hz⟩

/-- Correctness follows directly from reduction, extraction of powers of two,
the second supplement, and reciprocity, without any coprimality restriction. -/
theorem jacobi_computation_correct : P203Specs.Ch02.JacobiComputationCorrect := by
  intro a m z hz
  induction hz with
  | one a => exact jacobiSym.one_right a
  | @zero a m hm hm1 hr =>
    change jacobiSym a m = 0
    rw [jacobiSym.mod_left, hr, jacobiSym.zero_left hm1]
  | @power a m v hm hm1 hr =>
    change jacobiSym a m = _
    rw [jacobiSym.mod_left, hr, jacobiSym.pow_left]
    rw [show jacobiSym 2 m = (-1 : ℤ) ^ ((m ^ 2 - 1) / 8) from
      jacobi_supplement_two m hm]
  | @step a m v c z hm hm1 hc hc1 hcm hr next ih =>
    change jacobiSym a m = _
    rw [jacobiSym.mod_left, hr, jacobiSym.mul_left, jacobiSym.pow_left]
    rw [show jacobiSym 2 m = (-1 : ℤ) ^ ((m ^ 2 - 1) / 8) from
      jacobi_supplement_two m hm]
    rw [show jacobiSym (c : ℤ) m =
      (-1 : ℤ) ^ (((c - 1) / 2) * ((m - 1) / 2)) * jacobiSym (m : ℤ) c from
      jacobi_reciprocity c m hc hm]
    change jacobiSym (m : ℤ) c = z at ih
    rw [ih, mul_assoc]

theorem jacobi_computation_unique : P203Specs.Ch02.JacobiComputationUnique := by
  intro a m hm
  obtain ⟨z, hz⟩ := jacobi_termination a m hm
  refine ⟨z, hz, ?_⟩
  intro w hw
  exact (jacobi_computation_correct a m w hw).symm.trans
    (jacobi_computation_correct a m z hz)

/-- The source's counterexample: the value +1 does not certify a square for a
composite modulus. Reduction modulo three excludes a square root modulo 15. -/
theorem jacobi_composite_example : P203Specs.Ch02.JacobiCompositeExample := by
  constructor
  · change jacobiSym 2 15 = 1
    norm_num
  · rintro ⟨x, hx⟩
    have hx3 : x ^ 2 ≡ 2 [ZMOD 3] := hx.of_dvd (by norm_num)
    have hs := (square_congruence_iff 3 2).mp ⟨x, hx3⟩
    have hn : ¬IsSquare (2 : ZMod 3) :=
      ZMod.nonsquare_of_jacobiSym_eq_neg_one (a := 2) (b := 3) (by norm_num)
    exact hn hs

end P203.Ch02
