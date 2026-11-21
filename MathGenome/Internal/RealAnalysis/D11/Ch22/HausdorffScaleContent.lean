import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HausdorffScaleContent
import Mathlib.MeasureTheory.Measure.Hausdorff

/-! Diameter-cover content with the conventions of paper.tex:6012–6017. -/

noncomputable section

open Set Metric MeasureTheory
open scoped NNReal ENNReal

universe u

namespace D11.Ch22

/-- `H^s_δ(E)` for a genuine metric space. Empty sequence entries encode unused
slots of an at most countable cover. The coefficient in the diameter cost is one.
At exponent zero a nonempty singleton, like every nonempty set, costs one. -/
def hausdorffScaleContent {X : Type u} [MetricSpace X]
    (s δ : ℝ≥0) (E : Set X) : ℝ≥0∞ :=
  Specs.D11.Ch22.hausdorffScaleContentValue s δ E

/-- Bridge to Mathlib's scale outer measure. In particular it uses `≤ δ`, and
`boundedBy` removes the cost of empty entries and retains the prescribed cost
of every nonempty set, including singletons. -/
theorem hausdorffScaleContent_eq_pre {X : Type u} [MetricSpace X]
    (s δ : ℝ≥0) (E : Set X) :
    hausdorffScaleContent s δ E =
      OuterMeasure.mkMetric'.pre (fun U : Set X => ediam U ^ (s : ℝ))
        (δ : ℝ≥0∞) E := by
  classical
  unfold hausdorffScaleContent Specs.D11.Ch22.hausdorffScaleContentValue
  simp only [OuterMeasure.mkMetric'.pre, OuterMeasure.boundedBy_apply, extend]
  apply iInf_congr
  intro U
  apply iInf_congr
  intro hU
  by_cases hδ : ∀ n, ediam (U n) ≤ (δ : ℝ≥0∞)
  · simp only [iInf_pos hδ]
    congr 1 with n : 1
    simp only [iInf_pos (hδ n)]
  · rw [iInf_neg hδ]
    symm
    obtain ⟨n, hn⟩ := not_forall.mp hδ
    apply ENNReal.tsum_eq_top_of_eq_top
    refine ⟨n, ?_⟩
    have hne : (U n).Nonempty := by
      rcases ediam_pos_iff.mp (lt_of_le_of_lt zero_le (lt_of_not_ge hn)) with
        ⟨x, hx, _⟩
      exact ⟨x, hx⟩
    simp only [iSup_pos hne, iInf_neg hn]

@[simp]
theorem hausdorffScaleContent_empty {X : Type u} [MetricSpace X] (s δ : ℝ≥0) :
    hausdorffScaleContent s δ (∅ : Set X) = 0 := by
  rw [hausdorffScaleContent_eq_pre]
  exact measure_empty

@[simp]
theorem hausdorffScaleContent_zero_singleton {X : Type u} [MetricSpace X]
    (δ : ℝ≥0) (x : X) : hausdorffScaleContent 0 δ ({x} : Set X) = 1 := by
  classical
  apply le_antisymm
  · rw [hausdorffScaleContent_eq_pre]
    simpa using
      (OuterMeasure.mkMetric'.pre_le (m := fun U : Set X => ediam U ^ (0 : ℝ))
        (r := (δ : ℝ≥0∞)) (s := ({x} : Set X)) (by simp))
  · unfold hausdorffScaleContent Specs.D11.Ch22.hausdorffScaleContentValue
    simp only [NNReal.coe_zero, ENNReal.rpow_zero, le_iInf_iff]
    intro U hU _
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hU (mem_singleton x))
    calc
      (1 : ℝ≥0∞) = ⨆ _ : (U n).Nonempty, (1 : ℝ≥0∞) := by simp [show (U n).Nonempty from ⟨x, hn⟩]
      _ ≤ ∑' k, ⨆ _ : (U k).Nonempty, (1 : ℝ≥0∞) :=
        ENNReal.le_tsum (f := fun k => ⨆ _ : (U k).Nonempty, (1 : ℝ≥0∞)) n

@[simp]
theorem hausdorffScaleContent_singleton {X : Type u} [MetricSpace X]
    (s δ : ℝ≥0) (hs : 0 < s) (x : X) :
    hausdorffScaleContent s δ ({x} : Set X) = 0 := by
  apply le_antisymm _ zero_le
  rw [hausdorffScaleContent_eq_pre]
  have hs' : (0 : ℝ) < s := hs
  simpa [ENNReal.zero_rpow_of_pos hs'] using
    (OuterMeasure.mkMetric'.pre_le (m := fun U : Set X => ediam U ^ (s : ℝ))
      (r := (δ : ℝ≥0∞)) (s := ({x} : Set X)) (by simp))

theorem hausdorffScaleContent_eq_top_of_no_cover {X : Type u} [MetricSpace X]
    (s δ : ℝ≥0) (E : Set X)
    (h : ¬ ∃ U : ℕ → Set X, E ⊆ ⋃ n, U n ∧
      ∀ n, ediam (U n) ≤ (δ : ℝ≥0∞)) :
    hausdorffScaleContent s δ E = ∞ := by
  unfold hausdorffScaleContent Specs.D11.Ch22.hausdorffScaleContentValue
  apply top_unique
  simp only [le_iInf_iff]
  intro U hU hδ
  exact False.elim (h ⟨U, hU, hδ⟩)

end D11.Ch22
