import MathGenome.Internal.RealAnalysis.D11.Ch18.PolishCompactTightness
import MathGenome.Internal.RealAnalysis.D11.Ch18.MetricClosedRegular
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.PolishTightnessRegular

/-!
# Ulam regularity of finite Borel measures on complete separable metric spaces

This completes paper.tex:5402–5411. Compact tightness is the independently
proved upstream theorem, whose hypotheses are finite mass, completeness,
and separability. The metric approximation theorem applies because every
ball has mass at most the finite total mass.

For a Borel set E, intersect a closed inner approximation F with a tight
compact set H. This gives a compact subset of E. Its missing mass is bounded
by the sum of the two errors, each strictly less than ε/2. The open outer
approximation from metric regularity already has error less than ε/2.
-/

namespace D11.Ch18.PolishTightnessRegular

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

universe u

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

/-- The compact-tightness part of Ulam's theorem, with no extra regularity input. -/
theorem compact_tightness {X : Type u} [MetricSpace X] [CompleteSpace X]
    [SeparableSpace X] (μ : @Measure X (borel X)) (hμ : μ univ < ∞)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set X, IsCompact K ∧ μ (univ \ K) < ENNReal.ofReal ε :=
  PolishCompactTightness.compact_tightness μ hμ ε hε

/-- Full Borel compact-inner/open-outer approximation, including both strict
error bounds, on every complete separable metric space. -/
theorem polish_tightness_regular {X : Type u} [MetricSpace X] [CompleteSpace X]
    [SeparableSpace X] (μ : @Measure X (borel X)) (hμ : μ univ < ∞)
    (E : Set X) (hE : MeasurableSet[borel X] E) (ε : ℝ) (hε : 0 < ε) :
    ∃ K U : Set X, IsCompact K ∧ IsOpen U ∧ K ⊆ E ∧ E ⊆ U ∧
      μ (E \ K) < ENNReal.ofReal ε ∧ μ (U \ E) < ENNReal.ofReal ε := by
  let : BorelSpace X := ⟨rfl⟩
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨H, hH, hmassH⟩ := compact_tightness μ hμ (ε / 2) hhalf
  have hball : ∀ (x : X) (r : ℝ), 0 < r → μ (Metric.ball x r) < ∞ := by
    intro x r _
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) hμ
  obtain ⟨U, F, hU, hF, hEU, hFE, hmassU, hmassF⟩ :=
    MetricClosedRegular.metric_closed_regular μ hball E hE (ε / 2) hhalf
  have hhalflt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε)
  refine ⟨H ∩ F, U, hH.inter_right hF, hU,
    (inter_subset_right.trans hFE), hEU, ?_, hmassU.trans hhalflt⟩
  have hsub : E \ (H ∩ F) ⊆ (E \ F) ∪ (univ \ H) := by
    intro x hx
    by_cases hxH : x ∈ H
    · exact Or.inl ⟨hx.1, fun hxF => hx.2 ⟨hxH, hxF⟩⟩
    · exact Or.inr ⟨mem_univ x, hxH⟩
  calc
    μ (E \ (H ∩ F)) ≤ μ ((E \ F) ∪ (univ \ H)) := measure_mono hsub
    _ ≤ μ (E \ F) + μ (univ \ H) := measure_union_le _ _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add hmassF hmassH
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add hhalf.le hhalf.le]
      congr 1
      exact add_halves ε

end D11.Ch18.PolishTightnessRegular
