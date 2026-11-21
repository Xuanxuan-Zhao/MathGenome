import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Evolution.ConvergenceStability
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Evolution.Definitions
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Evolution.SemigroupBound
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Push

open Filter Topology

namespace NumAnalysis206.Evolution

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X]

/-- Each individual mesh error is bounded by the finite maximum. -/
theorem mesh_error_le (C : ℝ → X →L[𝕜] X) (T : StronglyContinuousSemigroup 𝕜 X)
    {T₀ h : ℝ} (hh : 0 < h) (n : ℕ) (hn : (n : ℝ) * h ≤ T₀) (x : X) :
    ‖(C h ^ n) x - T ((n : ℝ) * h) x‖ ≤ meshError C T T₀ h x := by
  exact_mod_cast (Finset.le_sup (f := fun k : ℕ =>
    ‖(C h ^ k) x - T ((k : ℝ) * h) x‖₊) ((mem_meshIndices_iff hh n).mpr hn))

/-- A single bad sequence is selected before using pointwise convergence and
Banach--Steinhaus, so no common convergence neighborhood is assumed. -/
theorem convergenceImpliesStability :
    Specs.NumAnalysis206.Evolution.convergenceImpliesStability := by
  intro 𝕜 _ X _ _ _ C T T₀ hT₀ hconv
  classical
  by_contra hnot
  change ¬ SmallStepStable C T₀ at hnot
  unfold SmallStepStable at hnot
  push Not at hnot
  have hbad (j : ℕ) : ∃ h : ℝ, 0 < h ∧ h ≤ 1 / ((j : ℝ) + 1) ∧
      ∃ n : ℕ, (n : ℝ) * h ≤ T₀ ∧ (j : ℝ) < ‖C h ^ n‖ := by
    exact hnot (1 / ((j : ℝ) + 1)) (by positivity) j (by positivity)
  choose h hpos hsmall n htime hlarge using hbad
  have hlim : Tendsto h atTop (𝓝 (0 : ℝ)) := by
    exact squeeze_zero (fun j => (hpos j).le) hsmall
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlimRight : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hpos⟩
  obtain ⟨K, _hK, hK⟩ := semigroupCompactBound T T₀ hT₀
  have hpoint (x : X) : ∃ B : ℝ, ∀ j : ℕ, ‖(C (h j) ^ n j) x‖ ≤ B := by
    have herr := (hconv x).comp hlimRight
    obtain ⟨B, hB⟩ := herr.bddAbove_range
    refine ⟨B + K * ‖x‖, fun j => ?_⟩
    calc
      ‖(C (h j) ^ n j) x‖ ≤
          ‖(C (h j) ^ n j) x - T ((n j : ℝ) * h j) x‖ +
            ‖T ((n j : ℝ) * h j) x‖ := by
              simpa only [sub_add_cancel] using
                (norm_add_le ((C (h j) ^ n j) x - T ((n j : ℝ) * h j) x)
                  (T ((n j : ℝ) * h j) x))
      _ ≤ meshError C T T₀ (h j) x + K * ‖x‖ := by
        apply add_le_add (mesh_error_le C T (hpos j) (n j) (htime j) x)
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right
            (hK _ ⟨mul_nonneg (Nat.cast_nonneg _) (hpos j).le, htime j⟩)
            (norm_nonneg _))
      _ ≤ B + K * ‖x‖ := add_le_add (hB (Set.mem_range_self j)) le_rfl
  obtain ⟨B, hB⟩ := banach_steinhaus (g := fun j => C (h j) ^ n j) hpoint
  obtain ⟨j, hj⟩ := exists_nat_gt B
  exact (not_lt_of_ge (hB j)) (hj.trans (hlarge j))

end NumAnalysis206.Evolution
