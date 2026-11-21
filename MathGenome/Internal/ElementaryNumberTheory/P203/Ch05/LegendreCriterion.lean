import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.LegendreCriterion
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.Convergents

namespace P203

/-- Strict Legendre approximation identifies the exact reduced integer pair
with a convergent, including the initial convergent and negative numerators. -/
theorem legendre_criterion : P203Specs.LegendreCriterion := by
  intro x hx p q hq hpq happrox
  have hcop : Nat.Coprime p.natAbs q.natAbs := hpq
  have hden := Rat.den_div_eq_of_coprime hq hcop
  have hcast : (((p : ℚ) / (q : ℚ) : ℚ) : ℝ) = (p : ℝ) / (q : ℝ) := by
    norm_cast
  have hbound : |x - (((p : ℚ) / (q : ℚ) : ℚ) : ℝ)| <
      1 / (2 * (((p : ℚ) / (q : ℚ)).den : ℝ) ^ 2) := by
    have hd : (((p : ℚ) / (q : ℚ)).den : ℝ) = (q : ℝ) := by
      exact_mod_cast hden
    rw [hd, hcast]
    exact happrox
  obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent hbound
  have hreal : (p : ℝ) / (q : ℝ) =
      (P203Specs.convergentNumerator x n : ℝ) /
        (P203Specs.convergentDenominator x n : ℝ) := by
    rw [← hcast, hn]
    exact (convergent_mathlib_bridge x n).2.2.2.symm
  have hrat : (p : ℚ) / (q : ℚ) =
      (P203Specs.convergentNumerator x n : ℚ) /
        (P203Specs.convergentDenominator x n : ℚ) := by
    exact_mod_cast hreal
  obtain ⟨α, hα⟩ := irrational_completeQuotient_defined x hx n
  have hdigit : P203Specs.partialQuotient x n ≠ none := by
    rw [algorithm_digits, hα]
    simp
  obtain ⟨hqpos, hred⟩ := convergent_reduced x n hdigit
  exact ⟨n, Rat.div_int_inj hq hqpos hcop hred hrat⟩

end P203
