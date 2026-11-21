import MathGenome.Internal.RealAnalysis.D11.Ch02.Caratheodory
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.MetricOuterBorel

/-!
# Metric outer measures make Borel sets measurable

The native metric-outer-measure theorem is general: it does not assume that
the outer measure is Hausdorff, finite, or sigma-finite. Its separation
hypothesis is checked below against the paper's positive real distance bound.
We then restrict to Borel sets using `OuterMeasure.toMeasure`, and reuse the
shared complete measure on the full Carathéodory sigma-algebra.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch22.MetricOuterBorel

/-- Native separation is exactly a positive real lower bound on cross distances.
This includes pairs with an empty member. -/
theorem separation_iff {X : Type u} [MetricSpace X] (A B : Set X) :
    Metric.AreSeparated A B ↔
      ∃ r : ℝ, 0 < r ∧ ∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y := by
  constructor
  · rintro ⟨r, hr, hdist⟩
    obtain ⟨s, _hs_nonneg, hs_pos, hsr⟩ := ENNReal.lt_iff_exists_real_btwn.mp
      (pos_iff_ne_zero.mpr hr)
    refine ⟨s, ENNReal.ofReal_pos.mp hs_pos, ?_⟩
    intro x hx y hy
    exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp
      (by simpa only [← edist_dist] using hsr.le.trans (hdist x hx y hy))
  · rintro ⟨r, hr, hdist⟩
    refine ⟨ENNReal.ofReal r, (ENNReal.ofReal_pos.mpr hr).ne', ?_⟩
    intro x hx y hy
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hdist x hx y hy)

/-- The metric outer measure predicate retains arbitrary, possibly nonmeasurable,
sets in its additivity hypothesis. -/
theorem isMetric_iff {X : Type u} [MetricSpace X] (m : OuterMeasure X) :
    m.IsMetric ↔
      ∀ A B : Set X,
        (∃ r : ℝ, 0 < r ∧ ∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) →
        m (A ∪ B) = m A + m B := by
  constructor
  · intro hm A B hAB
    exact hm A B ((separation_iff A B).mpr hAB)
  · intro hm A B hAB
    exact hm A B ((separation_iff A B).mp hAB)

theorem borel_le_caratheodory {X : Type u} [MetricSpace X]
    (m : OuterMeasure X) (hm : m.IsMetric) : borel X ≤ m.caratheodory :=
  hm.borel_le_caratheodory

/-- The full source conclusion, including the exact domains of both restrictions.
Completeness concerns the full Carathéodory restriction. -/
theorem metric_outer_borel {X : Type u} [MetricSpace X] (m : OuterMeasure X)
    (hm : ∀ A B : Set X,
      (∃ r : ℝ, 0 < r ∧ ∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) →
      m (A ∪ B) = m A + m B) :
    (∀ B : Set X, MeasurableSet[borel X] B →
      ∀ E : Set X, m E = m (E ∩ B) + m (E \ B)) ∧
    (∃ μ : @Measure X (borel X),
      ∀ B : Set X, MeasurableSet[borel X] B → μ B = m B) ∧
    (∀ C : Set X, (∀ E : Set X, m E = m (E ∩ C) + m (E \ C)) →
      D11.Ch02.Caratheodory.measure m C = m C) ∧
    @Measure.IsComplete X (D11.Ch02.Caratheodory.measurableSpace m)
      (D11.Ch02.Caratheodory.measure m) := by
  have hBorel : borel X ≤ m.caratheodory :=
    borel_le_caratheodory m ((isMetric_iff m).mpr hm)
  refine ⟨fun B hB => hBorel B hB, ?_, ?_,
    D11.Ch02.Caratheodory.measure_isComplete m⟩
  · exact ⟨@OuterMeasure.toMeasure X (borel X) m hBorel,
      fun B hB => @toMeasure_apply X (borel X) m hBorel B hB⟩
  · intro C hC
    exact D11.Ch02.Caratheodory.measure_apply m C hC

end D11.Ch22.MetricOuterBorel
