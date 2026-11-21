import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.PolishCompactTightness
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# Compact tightness of finite Borel measures on complete separable metric spaces

This is the tightness stage of paper.tex:5402–5411, independently of metric
closed regularity and the subsequent approximation of individual Borel sets.

The library theorem `exists_isCompact_closure_measure_compl_lt` constructs a
set with compact closure and small complement using a dense sequence, finite
selections from countable uniform-ball covers, and completeness plus total
boundedness. Its hypotheses require only finite mass, measurable opens,
second countability, and complete pseudometrizability. The latter two follow
from the separable complete metric structure here. Passing to the closure
can only reduce the missing mass. This application therefore assumes none
of the tightness or Radon conclusions being established.
-/

namespace D11.Ch18.PolishCompactTightness

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

universe u

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

/-- Ulam compact tightness, including empty spaces and the zero measure. -/
theorem compact_tightness {X : Type u} [MetricSpace X] [CompleteSpace X]
    [SeparableSpace X] (μ : @Measure X (borel X)) (hμ : μ univ < ∞)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set X, IsCompact K ∧ μ (univ \ K) < ENNReal.ofReal ε := by
  let : BorelSpace X := ⟨rfl⟩
  let : IsFiniteMeasure μ := ⟨hμ⟩
  obtain ⟨A, hA, hmass⟩ := exists_isCompact_closure_measure_compl_lt μ
    (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  refine ⟨closure A, hA, lt_of_le_of_lt (measure_mono ?_) hmass⟩
  exact fun x hx => fun hxA => hx.2 (subset_closure hxA)

end D11.Ch18.PolishCompactTightness
