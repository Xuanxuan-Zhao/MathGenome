import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricCompletion
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions

/-! The completion theorem d10:09:completion.

We fix Mathlib's Hausdorff uniform completion and its extending metric. This
construction needs no chosen point of X. The canonical isometry and density
are library theorems about this very metric; the accepted metric-conventions
bridge converts filter completeness to the paper's Cauchy-sequence definition.
The universal extension property is a separately allocated obligation.
-/

universe u

namespace D10Topology.Ch09

/-- The fixed completion of the specified metric, for use in subsequent results. -/
abbrev MetricCompletion {X : Type u} (d : MetricSpace X) : Type u :=
  @UniformSpace.Completion X d.toUniformSpace

/-- The canonical metric extending d, with its original completion uniformity. -/
@[instance_reducible] noncomputable def completionMetric {X : Type u} (d : MetricSpace X) :
    MetricSpace (MetricCompletion d) :=
  @UniformSpace.Completion.instMetricSpace X d.toPseudoMetricSpace

/-- The canonical map into the fixed completion. -/
def completionEmbedding {X : Type u} (d : MetricSpace X) : X → MetricCompletion d :=
  @UniformSpace.Completion.coe' X d.toUniformSpace

theorem completion_complete {X : Type u} (d : MetricSpace X) :
    SequentiallyComplete (completionMetric d).toPseudoMetricSpace := by
  let := d
  exact (sequentiallyComplete_iff_mathlib _).mpr
    (UniformSpace.Completion.completeSpace X)

theorem completion_isometry {X : Type u} (d : MetricSpace X) :
    Isometry d.toPseudoMetricSpace (completionMetric d).toPseudoMetricSpace
      (completionEmbedding d) := by
  let := d
  exact (isometry_iff_mathlib _ _ _).mpr UniformSpace.Completion.coe_isometry

theorem completion_injective {X : Type u} (d : MetricSpace X) :
    Function.Injective (completionEmbedding d) := by
  let := d
  exact UniformSpace.Completion.coe_isometry.injective

theorem completion_isEmbedding {X : Type u} (d : MetricSpace X) :
    @Topology.IsEmbedding X (MetricCompletion d)
      (metricTopology d.toPseudoMetricSpace)
      (metricTopology (completionMetric d).toPseudoMetricSpace)
      (completionEmbedding d) := by
  let := d
  exact UniformSpace.Completion.coe_isometry.isEmbedding

theorem completion_dense {X : Type u} (d : MetricSpace X) :
    @DenseRange (MetricCompletion d)
      (metricTopology (completionMetric d).toPseudoMetricSpace) X
      (completionEmbedding d) := by
  let := d
  exact UniformSpace.Completion.denseRange_coe

theorem completion_empty {X : Type u} [IsEmpty X] (d : MetricSpace X) :
    IsEmpty (MetricCompletion d) := by
  let := d
  exact ⟨fun q =>
    ((UniformSpace.Completion.nonempty_completion_iff X).mp ⟨q⟩).elim isEmptyElim⟩

/-- Every metric space has a complete metric extension with dense isometric image. -/
theorem exists_metric_completion {X : Type u} (d : MetricSpace X) :
    ∃ (Xhat : Type u) (e : MetricSpace Xhat) (j : X → Xhat),
      SequentiallyComplete e.toPseudoMetricSpace ∧
      Isometry d.toPseudoMetricSpace e.toPseudoMetricSpace j ∧
      Function.Injective j ∧
      @Topology.IsEmbedding X Xhat (metricTopology d.toPseudoMetricSpace)
        (metricTopology e.toPseudoMetricSpace) j ∧
      @DenseRange Xhat (metricTopology e.toPseudoMetricSpace) X j :=
  ⟨MetricCompletion d, completionMetric d, completionEmbedding d,
    completion_complete d, completion_isometry d, completion_injective d,
    completion_isEmbedding d, completion_dense d⟩

end D10Topology.Ch09
