import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Independent statements for metric comparison and its explicit counterexamples.
The sequence indexed here by n : ℕ is the paper's sequence indexed by n+1 ≥ 1.
The Euclidean metric is the ℓ² metric, including dimension zero. -/
open Set
universe u v
namespace Specs.D10Topology.Ch09.MetricComparison
open Specs.D10Topology.Ch09.MetricConventions

abbrev OpenUnitInterval := Set.Ioo (0 : ℝ) 1
noncomputable def tangentMap (x : OpenUnitInterval) : ℝ :=
  Real.tan (Real.pi * (x.val - 1 / 2))

noncomputable def reciprocalSequence (n : ℕ) : OpenUnitInterval :=
  ⟨1 / ((n : ℝ) + 2), by
    constructor
    · positivity
    · have : (1 : ℝ) < (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
      exact (div_lt_one (by positivity)).mpr this⟩

def topology_comparison : Prop :=
  ∀ {X : Type u} (d e : MetricSpace X),
    TopologicallyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace ↔
      (∀ x ε, 0 < ε → ∃ δ > 0, ball d.toPseudoMetricSpace x δ ⊆ ball e.toPseudoMetricSpace x ε) ∧
      (∀ x ε, 0 < ε → ∃ δ > 0, ball e.toPseudoMetricSpace x δ ⊆ ball d.toPseudoMetricSpace x ε)

def truncated_metric : Prop :=
  ∀ {X : Type u} (d : MetricSpace X), ∃ e : MetricSpace X,
    (∀ x y, distance e.toPseudoMetricSpace x y = min 1 (distance d.toPseudoMetricSpace x y)) ∧
    UniformlyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace

def bilipschitz_implies_uniform : Prop :=
  ∀ {X : Type u} (d e : MetricSpace X),
    BilipschitzEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace →
    UniformlyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace

def uniform_implies_topological : Prop :=
  ∀ {X : Type u} (d e : MetricSpace X),
    UniformlyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace →
    TopologicallyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace

def real_truncation_counterexample : Prop :=
  ∃ e : MetricSpace ℝ,
    (∀ x y, distance e.toPseudoMetricSpace x y = min 1 |x-y|) ∧
    UniformlyEquivalent Real.metricSpace.toPseudoMetricSpace e.toPseudoMetricSpace ∧
    ¬ BilipschitzEquivalent Real.metricSpace.toPseudoMetricSpace e.toPseudoMetricSpace

def euclidean_complete : Prop :=
  ∀ n : ℕ, SequentiallyComplete (inferInstance : MetricSpace (EuclideanSpace ℝ (Fin n))).toPseudoMetricSpace

/-- Exact usual metric, exact tangent pullback, and all three uniform distinctions. -/
def interval_counterexample : Prop :=
  let d : MetricSpace OpenUnitInterval := inferInstance
  ∃ e : MetricSpace OpenUnitInterval,
    (∀ x y, distance e.toPseudoMetricSpace x y = |tangentMap x - tangentMap y|) ∧
    TopologicallyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace ∧
    ¬ UniformlyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace ∧
    CauchySequence d.toPseudoMetricSpace reciprocalSequence ∧
    ¬ CauchySequence e.toPseudoMetricSpace reciprocalSequence ∧
    ¬ SequentiallyComplete d.toPseudoMetricSpace ∧
    SequentiallyComplete e.toPseudoMetricSpace ∧
    TotallyBounded d.toPseudoMetricSpace ∧
    ¬ TotallyBounded e.toPseudoMetricSpace

/-- The one-coordinate compact cube already witnesses the embedding cautions. -/
def cube_embedding_counterexample : Prop :=
  let d : MetricSpace OpenUnitInterval := inferInstance
  ∃ f : OpenUnitInterval → Set.Icc (0 : ℝ) 1,
    Topology.IsEmbedding f ∧ ¬ IsClosed (Set.range f) ∧
    ¬ Isometry d.toPseudoMetricSpace
      (inferInstance : MetricSpace (Set.Icc (0 : ℝ) 1)).toPseudoMetricSpace f ∧
    ¬ SequentiallyComplete d.toPseudoMetricSpace

/-- A cube embedding can turn a non-Cauchy sequence into a Cauchy sequence. -/
def cube_cauchy_counterexample : Prop :=
  let d : MetricSpace OpenUnitInterval := inferInstance
  let k : MetricSpace (Set.Icc (0 : ℝ) 1) := inferInstance
  ∃ (e : MetricSpace OpenUnitInterval) (f : OpenUnitInterval → Set.Icc (0 : ℝ) 1),
    (∀ x y, distance e.toPseudoMetricSpace x y = |tangentMap x - tangentMap y|) ∧
    TopologicallyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace ∧
    @Topology.IsEmbedding _ _ (metricTopology e.toPseudoMetricSpace)
      (metricTopology k.toPseudoMetricSpace) f ∧
    ¬ CauchySequence e.toPseudoMetricSpace reciprocalSequence ∧
    CauchySequence k.toPseudoMetricSpace (f ∘ reciprocalSequence)

/-- In particular this applies to every embedding into a compact cube. -/
def incomplete_embedding_not_closed : Prop :=
  ∀ {X : Type u} {Y : Type v} (d : MetricSpace X)
    [t : TopologicalSpace Y] [CompactSpace Y] (f : X → Y),
    @Topology.IsEmbedding X Y (metricTopology d.toPseudoMetricSpace) t f →
    ¬ SequentiallyComplete d.toPseudoMetricSpace → ¬ IsClosed (Set.range f)

end Specs.D10Topology.Ch09.MetricComparison
