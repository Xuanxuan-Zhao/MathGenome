import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.PythagoreanTriples
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic.Linarith

namespace P203.Ch04
open P203Specs.Ch04

/-- The sum and difference of the odd leg and hypotenuse determine the
squares of both parameters. Positivity determines the square roots. -/
theorem parameters_unique {a b c r s u v : ℤ}
    (h : Parameters a b c r s) (k : Parameters a b c u v) :
    (u, v) = (r, s) := by
  rcases h with ⟨hs, hsr, ha, hb, hc, hg, hp⟩
  rcases k with ⟨hv, hvu, ka, kb, kc, kg, kp⟩
  have hr : 0 < r := lt_trans hs hsr
  have hu : 0 < u := lt_trans hv hvu
  have hru : u ^ 2 = r ^ 2 := by omega
  have hsv : v ^ 2 = s ^ 2 := by omega
  have hur : u = r := by nlinarith [sq_nonneg (u - r)]
  have hvs : v = s := by nlinarith [sq_nonneg (v - s)]
  exact Prod.ext hur hvs

/-- Theorem 4.1 in fixed odd/even leg order. -/
theorem fixedOrderClassification : FixedOrderClassification := by
  intro a b c ha hb hc heq hg hao
  have ht : PythagoreanTriple a b c := by simpa only [PythagoreanTriple, ← sq] using heq
  obtain ⟨r, s, har, hbr, hcr, hrs, hpar, hr⟩ :=
    PythagoreanTriple.coprime_classification' ht hg hao hc
  have hrpos : 0 < r := by
    by_contra hn
    have hz : r = 0 := by omega
    rw [hz] at hbr
    norm_num at hbr
    omega
  have hspos : 0 < s := by
    by_contra hn
    have hprod : 2 * r * s ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    omega
  have hsr : s < r := by
    by_contra hn
    have hsq : r ^ 2 ≤ s ^ 2 := sq_le_sq₀ (by omega) (by omega) |>.mpr (by omega)
    omega
  have hp : Parameters a b c r s :=
    ⟨hspos, hsr, har, hbr, hcr, hrs, by rcases hpar with h | h <;> omega⟩
  exact ⟨(r, s), hp, fun q hq => parameters_unique hp hq⟩

/-- Theorem 4.1, with the uniqueness of the leg interchange made explicit. -/
theorem primitiveClassification : PrimitiveClassification := by
  intro a b c ha hb hc heq hg
  have ht : PythagoreanTriple a b c := by simpa only [PythagoreanTriple, ← sq] using heq
  have hp := ht.even_odd_of_coprime hg
  refine ⟨hp, ?_⟩
  rcases hp with ⟨hae, hbo⟩ | ⟨hao, hbe⟩
  · refine ⟨true, ?_, ?_⟩
    · simp only [↓reduceIte]
      exact ⟨hbo, hae, fixedOrderClassification b a c hb ha hc
        (by nlinarith [heq]) (by simpa [Int.gcd_comm] using hg) hbo⟩
    · intro swap hswap
      cases swap
      · simp only [Bool.false_eq_true, ↓reduceIte] at hswap
        omega
      · rfl
  · refine ⟨false, ?_, ?_⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨hao, hbe, fixedOrderClassification a b c ha hb hc heq hg hao⟩
    · intro swap hswap
      cases swap
      · rfl
      · simp only [↓reduceIte] at hswap
        omega

/-- The converse part of Theorem 4.1. -/
theorem parametrizationConverse : ParametrizationConverse := by
  intro r s hs hsr hg hp
  dsimp
  have hr : 0 < r := lt_trans hs hsr
  have hpar : r % 2 = 0 ∧ s % 2 = 1 ∨ r % 2 = 1 ∧ s % 2 = 0 := by
    rcases Int.emod_two_eq_zero_or_one r with h | h <;>
      rcases Int.emod_two_eq_zero_or_one s with k | k <;> omega
  have hclass := PythagoreanTriple.coprime_classification.mpr
    ⟨r, s, Or.inl ⟨rfl, rfl⟩, Or.inl rfl, hg, hpar⟩
  refine ⟨?_, by positivity, by positivity, by ring, hclass.2, ?_, ?_⟩
  · nlinarith [sq_nonneg (r - s)]
  · rcases hpar with ⟨h, k⟩ | ⟨h, k⟩ <;>
      simp [sq, Int.sub_emod, Int.mul_emod, h, k]
  · simp [Int.mul_emod]

end P203.Ch04
