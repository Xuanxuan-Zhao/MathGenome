import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Supporting.LaplaceCompactUniform
import MathGenome.Internal.SingleVariableAnalysis.D03Supporting.LaplaceUniformPhase
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Set
open scoped Topology

namespace D03Supporting

/-- On the nonpositive half-line the real exponential has derivative at most one. -/
lemma abs_exp_sub_exp_le_of_nonpos {u v : ℝ} (hu : u ≤ 0) (hv : v ≤ 0) :
    |Real.exp u - Real.exp v| ≤ |u - v| := by
  have h := (convex_Iic (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => Real.differentiable_exp x)
    (fun x hx => show ‖deriv Real.exp x‖ ≤ (1 : ℝ) by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
      exact Real.exp_le_one_iff.mpr hx) hv hu
  simpa only [one_mul, Real.norm_eq_abs] using h

/-- The uniform phase estimate and continuity at the interior point control the full amplitude. -/
theorem laplaceCompactUniform : Specs.D03Supporting.LaplaceCompactUniform := by
  intro 𝕂 _ a b x₀ φ g hab hax hxb hφ hmin hunique hd hg R hR ε hε
  have hgc : ContinuousAt g x₀ := hg.continuousAt (Icc_mem_nhds hax hxb)
  obtain ⟨δ, hδ, hgsmall⟩ := Metric.continuousAt_iff.mp hgc (ε / 2) (by positivity)
  let η : ℝ := ε / (2 * (‖g x₀‖ + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨L₁, hL₁, hphase⟩ := laplaceUniformPhase a b x₀ φ hab hax hxb hφ hmin
    hunique hd R hR η hη
  let c : ℝ := R / δ + 1
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨max L₁ (c ^ 2), lt_of_lt_of_le hL₁ (le_max_left _ _), ?_⟩
  intro lam hlam y hy
  have hLlam : L₁ ≤ lam := (le_max_left _ _).trans hlam
  have hlampos : 0 < lam := hL₁.trans_le hLlam
  obtain ⟨hmem, hphaseerr⟩ := hphase lam hLlam y hy
  refine ⟨hmem, ?_⟩
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlampos
  have hcs : c ≤ Real.sqrt lam := by
    calc
      c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hc.le).symm
      _ ≤ Real.sqrt lam := Real.sqrt_le_sqrt ((le_max_right _ _).trans hlam)
  have hRt : R / δ < Real.sqrt lam := by dsimp [c] at hcs; linarith
  have hRds : R < δ * Real.sqrt lam := by
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hRt
  have hinc : |y / Real.sqrt lam| < δ := by
    rw [abs_div, abs_of_pos hs]
    exact (div_lt_iff₀ hs).mpr (hy.trans_lt (by nlinarith [hRds]))
  have hgerr : ‖g (x₀ + y / Real.sqrt lam) - g x₀‖ < ε / 2 := by
    have hx : dist (x₀ + y / Real.sqrt lam) x₀ < δ := by
      simpa only [Real.dist_eq, add_sub_cancel_left] using hinc
    simpa only [dist_eq_norm] using hgsmall hx
  let A : ℝ := lam * (φ (x₀ + y / Real.sqrt lam) - φ x₀)
  let B : ℝ := deriv (deriv φ) x₀ * y ^ 2 / 2
  have hA : 0 ≤ A := mul_nonneg hlampos.le (sub_nonneg.mpr (hmin _ hmem))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have heA : Real.exp (-A) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hA)
  have heerr : |Real.exp (-A) - Real.exp (-B)| < η := by
    calc
      _ ≤ |-A - -B| := abs_exp_sub_exp_le_of_nonpos (neg_nonpos.mpr hA)
        (neg_nonpos.mpr hB)
      _ = |A - B| := by rw [← abs_neg]; congr 1; ring
      _ < η := hphaseerr
  have hηbound : η * ‖g x₀‖ ≤ ε / 2 := by
    have hn := norm_nonneg (g x₀)
    have hden : 0 < 2 * (‖g x₀‖ + 1) := by positivity
    dsimp [η]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  have herror : ‖Real.exp (-A) • g (x₀ + y / Real.sqrt lam) -
      Real.exp (-B) • g x₀‖ < ε := by
    calc
      _ = ‖Real.exp (-A) • (g (x₀ + y / Real.sqrt lam) - g x₀) +
          (Real.exp (-A) - Real.exp (-B)) • g x₀‖ := by
            congr 1
            rw [smul_sub, sub_smul]
            abel
      _ ≤ ‖Real.exp (-A) • (g (x₀ + y / Real.sqrt lam) - g x₀)‖ +
          ‖(Real.exp (-A) - Real.exp (-B)) • g x₀‖ := norm_add_le _ _
      _ = Real.exp (-A) * ‖g (x₀ + y / Real.sqrt lam) - g x₀‖ +
          |Real.exp (-A) - Real.exp (-B)| * ‖g x₀‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_pos (Real.exp_pos _)]
      _ ≤ ‖g (x₀ + y / Real.sqrt lam) - g x₀‖ + η * ‖g x₀‖ := by
        exact add_le_add (by simpa using mul_le_mul_of_nonneg_right heA (norm_nonneg _))
          (mul_le_mul_of_nonneg_right heerr.le (norm_nonneg _))
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hgerr hηbound
      _ = ε := by ring
  simpa only [A, B, neg_mul, neg_div] using herror

end D03Supporting
