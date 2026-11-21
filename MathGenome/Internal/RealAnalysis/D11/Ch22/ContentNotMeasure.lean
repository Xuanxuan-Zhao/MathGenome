import MathGenome.Internal.RealAnalysis.D11.Ch22.EuclideanDimension
import MathGenome.Internal.RealAnalysis.D11.Ch22.ExponentThreshold
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.ContentNotMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The unit square distinguishes unrestricted content from Hausdorff mass.
The single-set cover bounds the former. Positive two-dimensional outer mass
and the exponent threshold force infinite one-dimensional outer mass.
-/

noncomputable section
open Set Metric
open scoped NNReal ENNReal

universe u

namespace D11.Ch22.ContentNotMeasure
open D11.Ch03

def unrestrictedContent {X : Type u} [MetricSpace X]
    (s : ℝ≥0) (E : Set X) : ℝ≥0∞ :=
  Specs.D11.Ch22.ContentNotMeasure.unrestrictedContentValue s E

/-- Using the target set itself as the only nonempty covering set. -/
theorem unrestrictedContent_le_diameter {X : Type u} [MetricSpace X]
    (s : ℝ≥0) (E : Set X) : unrestrictedContent s E ≤ ediam E ^ (s : ℝ) := by
  classical
  let U : ℕ → Set X := fun n => if n = 0 then E else ∅
  have hU : E ⊆ ⋃ n, U n := by
    intro x hx
    exact mem_iUnion.mpr ⟨0, by simpa [U] using hx⟩
  unfold unrestrictedContent Specs.D11.Ch22.ContentNotMeasure.unrestrictedContentValue
  refine iInf_le_of_le U (iInf_le_of_le hU ?_)
  calc
    (∑' n, ⨆ _ : (U n).Nonempty, ediam (U n) ^ (s : ℝ)) =
        ⨆ _ : E.Nonempty, ediam E ^ (s : ℝ) := by
      rw [tsum_eq_single 0]
      · simp [U]
      · intro n hn
        simp [U, hn]
    _ ≤ ediam E ^ (s : ℝ) := iSup_le fun _ => le_rfl

theorem square_diameter :
    ediam (closedBox (0 : Fin 2 → ℝ) 1) = ENNReal.ofReal (Real.sqrt 2) := by
  have hdist : ∀ x ∈ closedBox (0 : Fin 2 → ℝ) 1,
      ∀ y ∈ closedBox (0 : Fin 2 → ℝ) 1, dist x y ≤ Real.sqrt 2 := by
    intro x hx y hy
    rw [EuclideanSpace.dist_eq]
    apply Real.sqrt_le_sqrt
    have hcoord (j : Fin 2) : dist (x j) (y j) ^ 2 ≤ 1 := by
      rw [Real.dist_eq, sq_abs]
      have hxi := hx j
      have hyi := hy j
      change 0 ≤ x j ∧ x j ≤ 1 at hxi
      change 0 ≤ y j ∧ y j ≤ 1 at hyi
      nlinarith [sq_nonneg (x j - y j),
        mul_nonneg (sub_nonneg.mpr (by linarith : x j - y j ≤ 1))
          (by linarith : 0 ≤ 1 + (x j - y j))]
    simpa only [Fin.sum_univ_two, show (1 : ℝ) + 1 = 2 by norm_num]
      using add_le_add (hcoord 0) (hcoord 1)
  apply le_antisymm
  · apply ediam_le
    intro x hx y hy
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hdist x hx y hy)
  · have hzero : (0 : Point 2) ∈ closedBox (0 : Fin 2 → ℝ) 1 := by
      intro j
      exact ⟨le_rfl, zero_le_one⟩
    have hone : (WithLp.toLp 2 (fun _ : Fin 2 => (1 : ℝ)) : Point 2) ∈
        closedBox (0 : Fin 2 → ℝ) 1 := by
      intro j
      exact ⟨zero_le_one, le_rfl⟩
    have h := edist_le_ediam_of_mem hzero hone
    simpa [edist_dist, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq] using h

theorem content_not_measure :
    Specs.D11.Ch22.ContentNotMeasure.contentNotMeasureStatement := by
  change unrestrictedContent 1 (closedBox (0 : Fin 2 → ℝ) 1) ≤
      ENNReal.ofReal (Real.sqrt 2) ∧
    hausdorffOuterMeasure 1 (closedBox (0 : Fin 2 → ℝ) 1) = ∞
  constructor
  · simpa only [NNReal.coe_one, ENNReal.rpow_one, square_diameter] using
      unrestrictedContent_le_diameter 1 (closedBox (0 : Fin 2 → ℝ) 1)
  · have hp := (EuclideanDimension.cube_mass 2 (by decide) 1 (by norm_num)).1
    exact hausdorffOuterMeasure_eq_top_of_pos 1 2 _ (by norm_num) hp

end D11.Ch22.ContentNotMeasure
