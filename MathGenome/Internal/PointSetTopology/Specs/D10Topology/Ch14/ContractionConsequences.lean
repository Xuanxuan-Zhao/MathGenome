import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.Banach

/-! Independent statements of paper.tex, d10:14:iterate-contraction and
 d10:14:fixed-point-stability. Distances and sequential completeness are the
 canonical Chapter 9 objects. The uniform pointwise perturbation inequality
 expresses the bounded-supremum hypothesis without an extra boundedness premise.
 No continuity hypothesis is placed on the map whose iterate contracts. -/
universe u
namespace Specs.D10Topology.Ch14.ContractionConsequences
open Specs.D10Topology.Ch09.MetricConventions

/-- A positive iterate being a contraction suffices for existence and uniqueness. -/
def iterate_contraction : Prop :=
  ∀ {X : Type u} (d : MetricSpace X), Nonempty X →
    SequentiallyComplete d.toPseudoMetricSpace →
    ∀ (T : X → X) (m : ℕ) (q : ℝ), 1 ≤ m → 0 ≤ q → q < 1 →
    (∀ x y, distance d.toPseudoMetricSpace (T^[m] x) (T^[m] y) ≤
      q * distance d.toPseudoMetricSpace x y) →
    ∃! p : X, T p = p

/-- Fixed points exist uniquely and satisfy the quantitative perturbation bound.
The same real constant q controls both maps, and q = 0 is allowed. -/
def fixed_point_stability : Prop :=
  ∀ {X : Type u} (d : MetricSpace X), Nonempty X →
    SequentiallyComplete d.toPseudoMetricSpace →
    ∀ (S T : X → X) (q δ : ℝ), 0 ≤ q → q < 1 →
    (∀ x y, distance d.toPseudoMetricSpace (S x) (S y) ≤
      q * distance d.toPseudoMetricSpace x y) →
    (∀ x y, distance d.toPseudoMetricSpace (T x) (T y) ≤
      q * distance d.toPseudoMetricSpace x y) →
    (∀ x, distance d.toPseudoMetricSpace (S x) (T x) ≤ δ) →
    ∃ pS pT : X, S pS = pS ∧ T pT = pT ∧
      (∀ x, S x = x → x = pS) ∧ (∀ x, T x = x → x = pT) ∧
      distance d.toPseudoMetricSpace pS pT ≤ δ / (1 - q)

end Specs.D10Topology.Ch14.ContractionConsequences
