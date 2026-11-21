import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Continuous
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Criterion
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.ExtremeValues
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.HeineCantor
import Mathlib.Analysis.Complex.Basic

/-!
K03.08.continuous: continuous scalar functions are Darboux integrable.
On a fine partition uniform continuity bounds each closed-cell oscillation.
The lengths telescope to b-a, so a tolerance ε/(2(b-a)) gives a gap ≤ ε/2.
The complex result applies the real result to the two continuous components.
-/
namespace SingleVariableAnalysis.Riemann
open scoped BigOperators

/-- The distance between two points of a partition cell is at most its length. -/
theorem dist_le_cellLength {a b : ℝ} (P : Partition a b) (i : Fin P.n)
    {x y : ℝ} (hx : x ∈ cell P i) (hy : y ∈ cell P i) :
    dist x y ≤ cellLength P i := by
  rw [Real.dist_eq, abs_le]
  change -(P.point i.succ - P.point i.castSucc) ≤ x - y ∧
    x - y ≤ P.point i.succ - P.point i.castSucc
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- A pairwise bound on values controls the supremum minus the infimum,
without requiring either extremum to be attained. -/
theorem cell_oscillation_le (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (i : Fin P.n) (η : ℝ)
    (hη : ∀ x ∈ cell P i, ∀ y ∈ cell P i, |f x - f y| ≤ η) :
    cellSupremum f P hf i - cellInfimum f P hf i ≤ η := by
  apply sub_le_iff_le_add.mpr
  apply (cell_bounds f P hf i).2.2
  rintro _ ⟨x, hx, rfl⟩
  have hlo : f x - η ≤ cellInfimum f P hf i := by
    apply (cell_bounds f P hf i).1.2
    rintro _ ⟨y, hy, rfl⟩
    have hxy := (abs_le.mp (hη x hx y hy)).2
    linarith
  linarith

/-- Relative continuity on an ordered compact interval implies real Darboux
integrability, including the degenerate interval. -/
theorem real_continuous_integrable :
    Specs.SingleVariableAnalysis.Ch08.Continuous.realContinuousIntegrable := by
  intro f a b hab hc
  rcases lt_or_eq_of_le hab with hab | rfl
  · obtain ⟨M, _hM, hbound⟩ := real_compact_bounded f (Set.Icc a b) isCompact_Icc hc
    have hf : BoundedOnInterval f a b := by
      constructor
      · refine ⟨-M, ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        exact (abs_le.mp (hbound x hx)).1
      · refine ⟨M, ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        exact (abs_le.mp (hbound x hx)).2
    apply (darboux_criterion f hab hf).mpr
    intro ε hε
    let η := ε / (2 * (b-a))
    have hη : 0 < η := div_pos hε (mul_pos (by norm_num) (sub_pos.mpr hab))
    obtain ⟨δ, hδ, hu⟩ := heine_cantor f (Set.Icc a b) isCompact_Icc hc η hη
    obtain ⟨P, _hmeshpos, hmesh⟩ := arbitrarily_fine hab δ hδ
    have hosc (i : Fin P.n) :
        cellSupremum f P hf i - cellInfimum f P hf i ≤ η := by
      apply cell_oscillation_le f P hf i η
      intro x hx y hy
      have hd : dist x y < δ :=
        (dist_le_cellLength P i hx hy).trans_lt ((cellLength_le_mesh P i).trans_lt hmesh)
      have hxy := hu x (cell_subset_interval P i hx) y (cell_subset_interval P i hy) hd
      exact (show |f x - f y| < η by simpa only [Real.dist_eq] using hxy).le
    have hlength : (∑ i : Fin P.n, cellLength P i) = b-a := by
      change (∑ i : Fin P.n, (P.point i.succ - P.point i.castSucc)) = b-a
      rw [sum_cell_differences, P.last, P.first]
    have hgap : upperSum f P hf - lowerSum f P hf ≤ η * (b-a) := by
      calc
        upperSum f P hf - lowerSum f P hf =
            ∑ i : Fin P.n, (cellSupremum f P hf i - cellInfimum f P hf i) *
              cellLength P i := by
          simp only [upperSum, lowerSum, D.upperSumValue, D.lowerSumValue,
            sub_mul, Finset.sum_sub_distrib]
        _ ≤ ∑ i : Fin P.n, η * cellLength P i :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hosc i) (cell_positive P i).le
        _ = η * (b-a) := by rw [← Finset.mul_sum, hlength]
    have hηlength : η * (b-a) = ε / 2 := by
      dsimp [η]
      field_simp [ne_of_gt (sub_pos.mpr hab)]
    refine ⟨P, ?_⟩
    rw [hηlength] at hgap
    linarith
  · exact realIntegrable_degenerate f a

/-- Complex integrability uses the actual real and imaginary components. -/
theorem complex_continuous_integrable :
    Specs.SingleVariableAnalysis.Ch08.Continuous.complexContinuousIntegrable := by
  intro f a b hab hc
  have hfc := relativeContinuous_continuousOn f (Set.Icc a b) hc
  constructor
  · apply real_continuous_integrable (fun x => (f x).re) hab
    intro x hx
    apply (relativeContinuousAt_within_iff _ _ _).mpr
    exact Complex.continuous_re.continuousAt.comp_continuousWithinAt (hfc x hx)
  · apply real_continuous_integrable (fun x => (f x).im) hab
    intro x hx
    apply (relativeContinuousAt_within_iff _ _ _).mpr
    exact Complex.continuous_im.continuousAt.comp_continuousWithinAt (hfc x hx)

end SingleVariableAnalysis.Riemann
