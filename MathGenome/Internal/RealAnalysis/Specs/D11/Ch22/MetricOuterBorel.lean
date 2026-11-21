import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Caratheodory
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
Independent statements for paper.tex:6030–6040, D11.22.metric_outer_borel.

The hypothesis quantifies over arbitrary subsets, with a positive real lower
bound on all cross distances. The separation bridge checks the native predicate
even for empty sets. The conclusion uses the Borel sigma-algebra and the exact
shared full Carathéodory sigma-algebra, not the completion of the Borel measure.
There are no nonemptiness, separability, or mass assumptions. No particular
Hausdorff covering convention is used by this general theorem.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace Specs.D11.Ch22.MetricOuterBorel

def separation_iff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (A B : Set X),
    Metric.AreSeparated A B ↔
      ∃ r : ℝ, 0 < r ∧ ∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y

def isMetric_iff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (m : OuterMeasure X),
    m.IsMetric ↔
      ∀ A B : Set X,
        (∃ r : ℝ, 0 < r ∧ ∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) →
        m (A ∪ B) = m A + m B

def borel_le_caratheodory : Prop :=
  ∀ {X : Type u} [MetricSpace X] (m : OuterMeasure X),
    m.IsMetric → borel X ≤ m.caratheodory

/-- Borel splitting, a measure agreeing on every Borel set, and exact agreement
and completeness on the full shared Carathéodory domain. -/
def metric_outer_borel : Prop :=
  ∀ {X : Type u} [MetricSpace X] (m : OuterMeasure X),
    (∀ A B : Set X,
      (∃ r : ℝ, 0 < r ∧ ∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) →
      m (A ∪ B) = m A + m B) →
    (∀ B : Set X, MeasurableSet[borel X] B →
      ∀ E : Set X, m E = m (E ∩ B) + m (E \ B)) ∧
    (∃ μ : @Measure X (borel X),
      ∀ B : Set X, MeasurableSet[borel X] B → μ B = m B) ∧
    (∀ C : Set X, (∀ E : Set X, m E = m (E ∩ C) + m (E \ C)) →
      _root_.Specs.D11.Ch02.Caratheodory.measure_value m C = m C) ∧
    @Measure.IsComplete X
      (_root_.Specs.D11.Ch02.Caratheodory.measurableSpace_value m)
      (_root_.Specs.D11.Ch02.Caratheodory.measure_value m)

end Specs.D11.Ch22.MetricOuterBorel
