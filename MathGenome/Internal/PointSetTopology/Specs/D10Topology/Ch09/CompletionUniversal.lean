import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricCompletion

/-! Independent statements for paper.tex, d10:09:completion-universal.
The completion and all metric predicates are the canonical upstream objects.
The Lipschitz parameter is real, including the degenerate negative-parameter
cases of the source inequality. No nonemptiness assumption is imposed.
-/

open Set
universe u v w

namespace Specs.D10Topology.Ch09.CompletionUniversal
open MetricConventions MetricCompletion

/-- Existence and uniqueness among uniformly continuous extensions. -/
def completion_extension : Prop :=
  ∀ {X : Type u} {Y : Type v} (d : MetricSpace X) (e : MetricSpace Y) (f : X → Y),
    SequentiallyComplete e.toPseudoMetricSpace →
    UniformlyContinuous d.toPseudoMetricSpace e.toPseudoMetricSpace f →
    ∃! g : completionValue d → Y,
      UniformlyContinuous (completionMetricValue d).toPseudoMetricSpace e.toPseudoMetricSpace g ∧
      g ∘ completionEmbeddingValue d = f

/-- Uniqueness holds even among merely continuous extensions. -/
def completion_extension_unique : Prop :=
  ∀ {X : Type u} {Y : Type v} (d : MetricSpace X) (e : MetricSpace Y)
    (f : X → Y) (g h : completionValue d → Y),
    @Continuous _ _ (metricTopology (completionMetricValue d).toPseudoMetricSpace)
      (metricTopology e.toPseudoMetricSpace) g →
    @Continuous _ _ (metricTopology (completionMetricValue d).toPseudoMetricSpace)
      (metricTopology e.toPseudoMetricSpace) h →
    g ∘ completionEmbeddingValue d = f → h ∘ completionEmbeddingValue d = f → g = h

/-- Every continuous extension preserves the original Lipschitz constant. -/
def completion_lipschitz : Prop :=
  ∀ {X : Type u} {Y : Type v} (d : MetricSpace X) (e : MetricSpace Y)
    (L : ℝ) (f : X → Y) (g : completionValue d → Y),
    Lipschitz d.toPseudoMetricSpace e.toPseudoMetricSpace L f →
    @Continuous _ _ (metricTopology (completionMetricValue d).toPseudoMetricSpace)
      (metricTopology e.toPseudoMetricSpace) g →
    g ∘ completionEmbeddingValue d = f →
    Lipschitz (completionMetricValue d).toPseudoMetricSpace e.toPseudoMetricSpace L g

/-- Any two complete dense isometric extensions of X are uniquely isometric. -/
def completions_unique : Prop :=
  ∀ {X : Type u} {Z : Type v} {W : Type w}
    (d : MetricSpace X) (e : MetricSpace Z) (k : MetricSpace W)
    (i : X → Z) (j : X → W),
    SequentiallyComplete e.toPseudoMetricSpace → SequentiallyComplete k.toPseudoMetricSpace →
    Isometry d.toPseudoMetricSpace e.toPseudoMetricSpace i →
    Isometry d.toPseudoMetricSpace k.toPseudoMetricSpace j →
    @DenseRange Z (metricTopology e.toPseudoMetricSpace) X i →
    @DenseRange W (metricTopology k.toPseudoMetricSpace) X j →
    ∃! T : Z → W, IsometricIsomorphism e k T ∧ T ∘ i = j

/-- The reciprocal is continuous on the usual open unit interval. -/
def reciprocal_continuous : Prop :=
  Continuous (fun x : Ioo (0 : ℝ) 1 => (x.val)⁻¹)

/-- It has no continuous extension to the completion of that specified metric. -/
def reciprocal_no_extension : Prop :=
  let d : MetricSpace (Ioo (0 : ℝ) 1) := inferInstance
  ¬ ∃ g : completionValue d → ℝ,
    @Continuous _ _ (metricTopology (completionMetricValue d).toPseudoMetricSpace)
      (inferInstance : TopologicalSpace ℝ) g ∧
    g ∘ completionEmbeddingValue d = (fun x => (x.val)⁻¹)

end Specs.D10Topology.Ch09.CompletionUniversal
