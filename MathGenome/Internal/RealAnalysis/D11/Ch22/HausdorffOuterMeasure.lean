import MathGenome.Internal.RealAnalysis.D11.Ch22.HausdorffScaleContent
import MathGenome.Internal.RealAnalysis.D11.Ch22.MetricOuterBorel
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HausdorffOuterMeasure

/-! # Hausdorff outer measure from small diameter covers

The supremum uses finite positive scales and the shared scale contents. A
cofinality argument identifies it with the native metric-outer-measure
construction for the cost `ediam U ^ s`. In particular this uses `mkMetric'`,
which retains nonempty singleton costs, including at exponent zero. All
evaluation and separation statements concern arbitrary subsets.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped NNReal ENNReal

universe u

namespace D11.Ch22

/-- The coefficient-one Hausdorff outer measure, with counting at exponent zero. -/
def hausdorffOuterMeasure {X : Type u} [MetricSpace X] (s : ℝ≥0) : OuterMeasure X :=
  Specs.D11.Ch22.HausdorffOuterMeasure.outerMeasureValue s

theorem hausdorffScaleContent_antitone {X : Type u} [MetricSpace X]
    (s : ℝ≥0) (E : Set X) :
    Antitone (fun δ : ℝ≥0 => hausdorffScaleContent s δ E) := by
  intro δ ε hδε
  change hausdorffScaleContent s ε E ≤ hausdorffScaleContent s δ E
  rw [hausdorffScaleContent_eq_pre, hausdorffScaleContent_eq_pre]
  exact OuterMeasure.mkMetric'.mono_pre _ (ENNReal.coe_le_coe.mpr hδε) E

/-- Evaluation is exactly the supremum of the fixed covering infima. -/
theorem hausdorffOuterMeasure_apply {X : Type u} [MetricSpace X]
    (s : ℝ≥0) (E : Set X) :
    hausdorffOuterMeasure s E =
      ⨆ (δ : ℝ≥0) (_ : 0 < δ), hausdorffScaleContent s δ E := by
  simp only [hausdorffOuterMeasure,
    Specs.D11.Ch22.HausdorffOuterMeasure.outerMeasureValue,
    OuterMeasure.iSup_apply, hausdorffScaleContent_eq_pre]

/-- Positive finite radii are cofinal toward zero among all positive extended
radii. This bridge does not alter the exponent-zero cost. -/
theorem hausdorffOuterMeasure_eq_mkMetric' {X : Type u} [MetricSpace X]
    (s : ℝ≥0) :
    hausdorffOuterMeasure (X := X) s =
      OuterMeasure.mkMetric' (fun U : Set X => ediam U ^ (s : ℝ)) := by
  unfold hausdorffOuterMeasure Specs.D11.Ch22.HausdorffOuterMeasure.outerMeasureValue
    OuterMeasure.mkMetric'
  apply le_antisymm
  · refine iSup₂_le fun δ hδ => ?_
    exact le_iSup₂_of_le (δ : ℝ≥0∞) (by exact_mod_cast hδ) le_rfl
  · refine iSup₂_le fun r hr => ?_
    obtain ⟨δ, hδ, hδr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
    have hδ' : (0 : ℝ≥0) < δ := by exact_mod_cast hδ
    exact le_iSup₂_of_le δ hδ' (OuterMeasure.mkMetric'.mono_pre _ hδr.le)

/-- The outer-measure axioms apply without any measurability hypothesis. -/
theorem hausdorffOuterMeasure_axioms {X : Type u} [MetricSpace X] (s : ℝ≥0) :
    hausdorffOuterMeasure s (∅ : Set X) = 0 ∧
    Monotone (fun E : Set X => hausdorffOuterMeasure s E) ∧
    ∀ E : ℕ → Set X, hausdorffOuterMeasure s (⋃ n, E n) ≤
      ∑' n, hausdorffOuterMeasure s (E n) := by
  exact ⟨measure_empty, fun _ _ h => measure_mono h, fun E => measure_iUnion_le E⟩

theorem hausdorffOuterMeasure_isMetric {X : Type u} [MetricSpace X] (s : ℝ≥0) :
    (hausdorffOuterMeasure (X := X) s).IsMetric := by
  rw [hausdorffOuterMeasure_eq_mkMetric']
  exact OuterMeasure.mkMetric'_isMetric _

/-- Positive distance separation includes cases in which one set is empty. -/
theorem hausdorffOuterMeasure_union_of_separated {X : Type u} [MetricSpace X]
    (s : ℝ≥0) (A B : Set X)
    (hAB : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) :
    hausdorffOuterMeasure s (A ∪ B) =
      hausdorffOuterMeasure s A + hausdorffOuterMeasure s B :=
  (MetricOuterBorel.isMetric_iff _).mp (hausdorffOuterMeasure_isMetric s) A B hAB

theorem hausdorffOuterMeasure_borel_le {X : Type u} [MetricSpace X] (s : ℝ≥0) :
    borel X ≤ (hausdorffOuterMeasure (X := X) s).caratheodory :=
  MetricOuterBorel.borel_le_caratheodory _ (hausdorffOuterMeasure_isMetric s)

/-- The Borel restriction is a measure; the full Carathéodory restriction is
the shared complete measure, agreeing on every splitting-measurable set. -/
theorem hausdorffOuterMeasure_restrictions {X : Type u} [MetricSpace X] (s : ℝ≥0) :
    (∀ B : Set X, MeasurableSet[borel X] B →
      ∀ E : Set X, hausdorffOuterMeasure s E =
        hausdorffOuterMeasure s (E ∩ B) + hausdorffOuterMeasure s (E \ B)) ∧
    (∃ μ : @Measure X (borel X),
      ∀ B : Set X, MeasurableSet[borel X] B → μ B = hausdorffOuterMeasure s B) ∧
    (∀ C : Set X,
      (∀ E : Set X, hausdorffOuterMeasure s E =
        hausdorffOuterMeasure s (E ∩ C) + hausdorffOuterMeasure s (E \ C)) →
      D11.Ch02.Caratheodory.measure (hausdorffOuterMeasure s) C =
        hausdorffOuterMeasure s C) ∧
    @Measure.IsComplete X
      (D11.Ch02.Caratheodory.measurableSpace (hausdorffOuterMeasure s))
      (D11.Ch02.Caratheodory.measure (hausdorffOuterMeasure s)) := by
  exact MetricOuterBorel.metric_outer_borel (hausdorffOuterMeasure s)
    (hausdorffOuterMeasure_union_of_separated s)

end D11.Ch22
