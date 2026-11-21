import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
Independent statements for paper.tex, d10:09:cantor-intersection and
d10:14:nested-closed. Completeness is the chapter's sequence completeness
for the specified metric. Diameters take values in ℝ≥0∞; no boundedness
or nonempty ambient-space assumption is imposed. Natural-number indexing
starts at zero, as in the accepted metric conventions.
-/

open Set Filter
open scoped Topology ENNReal
universe u

namespace Specs.D10Topology.Ch09.CantorIntersection
open Specs.D10Topology.Ch09.MetricConventions

/-- Shrinking extended diameters force uniqueness, even without completeness. -/
def shrinking_intersection_subsingleton : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (F : ℕ → Set X),
    Tendsto (fun n => diameter d.toPseudoMetricSpace (F n)) atTop (𝓝 0) →
    (⋂ n, F n).Subsingleton

/-- The forward direction, also the singleton conclusion repeated in chapter 14. -/
def cantor_intersection_singleton : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    SequentiallyComplete d.toPseudoMetricSpace →
    ∀ F : ℕ → Set X, Antitone F →
      (∀ n, (F n).Nonempty) →
      (∀ n, IsClosed[metricTopology d.toPseudoMetricSpace] (F n)) →
      Tendsto (fun n => diameter d.toPseudoMetricSpace (F n)) atTop (𝓝 0) →
      ∃ x : X, (⋂ n, F n) = {x}

/-- Nonempty nested closed intersections with shrinking diameter characterize completeness. -/
def complete_iff_cantor_intersection : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    SequentiallyComplete d.toPseudoMetricSpace ↔
      ∀ F : ℕ → Set X, Antitone F →
        (∀ n, (F n).Nonempty) →
        (∀ n, IsClosed[metricTopology d.toPseudoMetricSpace] (F n)) →
        Tendsto (fun n => diameter d.toPseudoMetricSpace (F n)) atTop (𝓝 0) →
        (⋂ n, F n).Nonempty

end Specs.D10Topology.Ch09.CantorIntersection
