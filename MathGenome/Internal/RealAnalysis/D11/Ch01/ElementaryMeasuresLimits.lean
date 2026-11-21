import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.ElementaryMeasuresLimits
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Basic.ENNReal.BigOperators

/-!
Elementary measures and increasing setwise limits, paper.tex:296–315, 341–359.
The witnesses below are measures on the original sigma-algebra. Their values
are asserted only for measurable sets, so native outer values do not enlarge
the measurable domain. The last construction uses the upstream source-measure
representation and proves countable additivity by commuting an increasing
supremum with a nonnegative series via finite partial sums.
-/

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

universe u

namespace D11.Ch01.ElementaryMeasuresLimits

theorem counting_measure {α : Type u} [MeasurableSpace α] : ∃ c : Measure α,
    (∀ (s : Set α), MeasurableSet s → ∀ hs : s.Finite,
      c s = (hs.toFinset.card : ℝ≥0∞)) ∧
    (∀ (s : Set α), MeasurableSet s → s.Infinite → c s = ∞) := by
  refine ⟨Measure.count, ?_, ?_⟩
  · intro s hs hfin
    exact Measure.count_apply_finite' hfin hs
  · intro s _hs hinf
    exact Measure.count_apply_infinite hinf

theorem point_measure {α : Type u} [MeasurableSpace α] (x : α) : ∃ δ : Measure α,
    ∀ (s : Set α), MeasurableSet s → δ s = s.indicator (fun _ => (1 : ℝ≥0∞)) x := by
  exact ⟨Measure.dirac x, fun _ hs => Measure.dirac_apply' x hs⟩

theorem atomic_measure {α : Type u} [MeasurableSpace α] (x : ℕ → α) (a : ℕ → ℝ≥0∞) :
    ∃ μ : Measure α, ∀ (s : Set α), MeasurableSet s →
      μ s = ∑' n, a n * s.indicator (fun _ => (1 : ℝ≥0∞)) (x n) := by
  refine ⟨Measure.sum (fun n => a n • Measure.dirac (x n)), ?_⟩
  intro s hs
  simp only [Measure.sum_apply _ hs, Measure.smul_apply, Measure.dirac_apply' _ hs,
    smul_eq_mul, Pi.one_def]

theorem weighted_sum {α : Type u} [MeasurableSpace α]
    (μ : ℕ → Measure α) (a : ℕ → ℝ≥0) :
    ∃ ν : Measure α, ∀ (s : Set α), MeasurableSet s →
      ν s = ∑' n, (a n : ℝ≥0∞) * μ n s := by
  refine ⟨Measure.sum (fun n => (a n : ℝ≥0∞) • μ n), ?_⟩
  intro s hs
  simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]

theorem weighted_sum_real {α : Type u} [MeasurableSpace α]
    (μ : ℕ → Measure α) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    ∃ ν : Measure α, ∀ (s : Set α), MeasurableSet s →
      ν s = ∑' n, ENNReal.ofReal (a n) * μ n s := by
  obtain ⟨ν, hν⟩ := weighted_sum μ (fun n => ⟨a n, ha n⟩)
  refine ⟨ν, fun s hs => (hν s hs).trans ?_⟩
  apply tsum_congr
  intro n
  exact congrArg (fun c => c * μ n s)
    (ENNReal.coe_nnreal_eq (⟨a n, ha n⟩ : ℝ≥0))

/-- Increasing suprema commute with nonnegative series. No finite-value or
summability restriction is needed for extended nonnegative reals. -/
theorem iSup_tsum_of_monotone (b : ℕ → ℕ → ℝ≥0∞)
    (hb : ∀ j, Monotone (fun n => b n j)) :
    (⨆ n, ∑' j, b n j) = ∑' j, ⨆ n, b n j := by
  simp only [ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  exact iSup_congr fun s => (ENNReal.finsetSum_iSup_of_monotone hb).symm

theorem increasing_limit {α : Type u} [MeasurableSpace α] (μ : ℕ → Measure α)
    (hμ : ∀ (s : Set α), MeasurableSet s → Monotone (fun n => μ n s)) :
    ∃ ν : Measure α, ∀ (s : Set α), MeasurableSet s →
      ν s = (⨆ n, μ n s) ∧ Tendsto (fun n => μ n s) atTop (𝓝 (ν s)) := by
  let p : MeasureDefinitions.SourceMeasure α :=
    { value := fun s => ⨆ n, μ n s.1
      empty := by simp
      iUnion := by
        intro E hd
        change (⨆ n, μ n (⋃ j, (E j).1)) = ∑' j, ⨆ n, μ n (E j).1
        simp_rw [measure_iUnion hd (fun j => (E j).2)]
        exact iSup_tsum_of_monotone _ (fun j => hμ _ (E j).2) }
  refine ⟨MeasureDefinitions.measureOfSource p, ?_⟩
  intro s hs
  have heq : MeasureDefinitions.measureOfSource p s = ⨆ n, μ n s :=
    MeasureDefinitions.measureOfSource_apply p s hs
  exact ⟨heq, heq.symm ▸ tendsto_atTop_iSup (hμ s hs)⟩

end D11.Ch01.ElementaryMeasuresLimits
