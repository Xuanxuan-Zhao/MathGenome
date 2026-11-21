import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! Canonical scalar data for the Newton--Kantorovich majorant. -/
namespace NumAnalysis206.Newton.Majorant

noncomputable def discriminant (η L : ℝ) : ℝ := Real.sqrt (1 - 2 * η * L)
noncomputable def lowerRoot (η L : ℝ) : ℝ := (1 - discriminant η L) / L
noncomputable def upperRoot (η L : ℝ) : ℝ := (1 + discriminant η L) / L
noncomputable def majorant (η L t : ℝ) : ℝ := η - t + (L / 2) * t ^ 2
/-- Newton update, using the explicit derivative `L * t - 1`. -/
noncomputable def newtonStep (η L t : ℝ) : ℝ := t - majorant η L t / (L * t - 1)
noncomputable def iterate (η L : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => newtonStep η L (iterate η L n)
noncomputable def error (η L : ℝ) (n : ℕ) : ℝ := lowerRoot η L - iterate η L n
noncomputable def coefficient (η L : ℝ) (n : ℕ) : ℝ := L / (2 * (1 - L * iterate η L n))

end NumAnalysis206.Newton.Majorant

namespace Specs.NumAnalysis206.Newton.Majorant
open _root_.NumAnalysis206.Newton.Majorant Filter

/-- The full scalar-majorant obligation, including the double-root boundary case. -/
def statement : Prop := ∀ (η L : ℝ), 0 < η → 0 < L → 2 * η * L ≤ 1 →
  (∀ t, deriv (majorant η L) t = L * t - 1) ∧
  0 ≤ discriminant η L ∧ discriminant η L < 1 ∧
  0 < lowerRoot η L ∧
  majorant η L (lowerRoot η L) = 0 ∧
  majorant η L (upperRoot η L) = 0 ∧
  (∀ t, majorant η L t = (L / 2) * (t - lowerRoot η L) * (t - upperRoot η L)) ∧
  (∀ n, 0 ≤ iterate η L n ∧ iterate η L n < lowerRoot η L ∧
    0 < majorant η L (iterate η L n) ∧ 0 < 1 - L * iterate η L n ∧
    iterate η L n < iterate η L (n + 1) ∧
    0 < error η L n ∧ 0 < coefficient η L n ∧
    majorant η L (iterate η L (n + 1)) = (L / 2) *
      (iterate η L (n + 1) - iterate η L n) ^ 2 ∧
    error η L (n + 1) = coefficient η L n * error η L n ^ 2 ∧
    coefficient η L n * error η L n ≤ 1 / 2 ∧
    (0 < discriminant η L → coefficient η L n ≤ L / (2 * discriminant η L))) ∧
  StrictMono (iterate η L) ∧
  Tendsto (iterate η L) atTop (nhds (lowerRoot η L)) ∧
  (2 * η * L < 1 → lowerRoot η L < upperRoot η L ∧
    ∀ s, lowerRoot η L < s → s < upperRoot η L → majorant η L s < 0) ∧
  (2 * η * L = 1 → discriminant η L = 0 ∧
    lowerRoot η L = upperRoot η L ∧
    deriv (majorant η L) (lowerRoot η L) = 0 ∧
    (∀ t, majorant η L t = (L / 2) * (t - lowerRoot η L) ^ 2) ∧
    ∀ n, error η L (n + 1) = error η L n / 2)

end Specs.NumAnalysis206.Newton.Majorant
