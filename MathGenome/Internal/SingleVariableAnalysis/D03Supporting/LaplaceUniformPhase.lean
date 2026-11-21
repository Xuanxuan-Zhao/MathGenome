import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Supporting.LaplaceUniformPhase
import MathGenome.Internal.SingleVariableAnalysis.D03Supporting.LaplacePeano
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Set
open scoped Topology

namespace D03Supporting

/-- The Peano error is uniformly small for all bounded rescaled increments. -/
theorem laplaceUniformPhase : Specs.D03Supporting.LaplaceUniformPhase := by
  intro a b x₀ φ hab hax hxb hφ hmin hunique hd R hR η hη
  obtain ⟨_, δ, hδ, ρ, _, hρ, hexp⟩ :=
    laplacePeano a b x₀ φ hab hax hxb hφ hmin hunique hd
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  obtain ⟨ε, hε, hsmall⟩ := Metric.tendsto_nhds_nhds.mp hρ
    (η / R ^ 2) (div_pos hη hR2)
  let t : ℝ := min δ ε
  have ht : 0 < t := lt_min hδ hε
  have hc : 0 < R / t + 1 := by positivity
  refine ⟨(R / t + 1) ^ 2, sq_pos_of_pos hc, ?_⟩
  intro lam hlam y hy
  have hlampos : 0 < lam := lt_of_lt_of_le (sq_pos_of_pos hc) hlam
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlampos
  have hcs : R / t + 1 ≤ Real.sqrt lam := by
    calc
      R / t + 1 = Real.sqrt ((R / t + 1) ^ 2) := (Real.sqrt_sq hc.le).symm
      _ ≤ Real.sqrt lam := Real.sqrt_le_sqrt hlam
  have hRt : R / t < Real.sqrt lam := by linarith
  have hRts : R < t * Real.sqrt lam := by
    simpa only [mul_comm] using (div_lt_iff₀ ht).mp hRt
  have hinc : |y / Real.sqrt lam| < t := by
    rw [abs_div, abs_of_pos hs]
    exact (div_lt_iff₀ hs).mpr (lt_of_le_of_lt hy (by nlinarith [hRts]))
  obtain ⟨hmem, heq⟩ := hexp (y / Real.sqrt lam)
    (lt_of_lt_of_le hinc (min_le_left _ _))
  refine ⟨hmem, ?_⟩
  have hrho : |ρ (y / Real.sqrt lam)| < η / R ^ 2 := by
    have hh := hsmall (show dist (y / Real.sqrt lam) 0 < ε by
      simpa only [Real.dist_eq, sub_zero] using
        (lt_of_lt_of_le hinc (min_le_right δ ε)))
    simpa only [Real.dist_eq, sub_zero] using hh
  have hs2 : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlampos.le
  have hscale : lam * (y / Real.sqrt lam) ^ 2 = y ^ 2 := by
    rw [div_pow, hs2]
    field_simp
  have herr : lam * (φ (x₀ + y / Real.sqrt lam) - φ x₀) -
      deriv (deriv φ) x₀ * y ^ 2 / 2 = y ^ 2 * ρ (y / Real.sqrt lam) := by
    rw [heq]
    calc
      _ = deriv (deriv φ) x₀ * (lam * (y / Real.sqrt lam) ^ 2) / 2 +
          (lam * (y / Real.sqrt lam) ^ 2) * ρ (y / Real.sqrt lam) -
          deriv (deriv φ) x₀ * y ^ 2 / 2 := by ring
      _ = _ := by rw [hscale]; ring
  have hy2 : y ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_abs y, abs_nonneg y]
  rw [herr, abs_mul, abs_of_nonneg (sq_nonneg y)]
  calc
    y ^ 2 * |ρ (y / Real.sqrt lam)| ≤ R ^ 2 * |ρ (y / Real.sqrt lam)| :=
      mul_le_mul_of_nonneg_right hy2 (abs_nonneg _)
    _ < R ^ 2 * (η / R ^ 2) := mul_lt_mul_of_pos_left hrho hR2
    _ = η := by field_simp

end D03Supporting
