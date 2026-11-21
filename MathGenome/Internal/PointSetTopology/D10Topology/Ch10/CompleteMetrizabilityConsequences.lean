import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch10.CompleteMetrizabilityConsequences
import MathGenome.Internal.PointSetTopology.D10Topology.Ch10.CompleteGdeltaNecessary
import MathGenome.Internal.PointSetTopology.D10Topology.Ch10.CompleteGdeltaSufficient
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricCompletion
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.CauchyBasics
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Irrational

/-! The consequences of d10:10:complete-gdelta and its corollary.
We use complete compatible metrics as witnesses, never assert completeness
of an arbitrary compatible metric, and permit empty spaces and index types. -/

open Set Topology
open scoped Topology
universe u v w
namespace D10Topology.Ch10
open Ch09

/-- Complete metrizability is invariant under homeomorphism. The library
transports a complete metric along a closed embedding; a homeomorphism is one. -/
theorem completelyMetrizable_of_homeomorph {X : Type u} {Y : Type v}
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (h : X ≃ₜ Y)
    (hY : CompletelyMetrizable tY) : CompletelyMetrizable tX := by
  let : TopologicalSpace.IsCompletelyMetrizableSpace Y :=
    (completelyMetrizable_iff_mathlib _).mp hY
  exact (completelyMetrizable_iff_mathlib _).mpr
    h.isClosedEmbedding.IsCompletelyMetrizableSpace

/-- The ambient metric need not be complete, and the embedding need not
preserve the chosen complete metric's distances or Cauchy sequences. -/
theorem completelyMetrizable_image_isGdelta
    {X : Type u} {Y : Type v} (t : TopologicalSpace X) (e : MetricSpace Y)
    (f : X → Y) (hX : CompletelyMetrizable t)
    (hf : @IsEmbedding X Y t (metricTopology e.toPseudoMetricSpace) f) :
    @IsGδ Y (metricTopology e.toPseudoMetricSpace) (range f) := by
  obtain ⟨d, rfl, hd⟩ := hX
  let := d
  let := e
  let : CompleteSpace X := (sequentiallyComplete_iff_mathlib _).mp hd
  exact isGdelta_range_of_complete hf

/-- An arbitrary embedding into a complete metric space detects complete
metrizability by the G_delta property of its range. -/
theorem completelyMetrizable_iff_gdelta_range
    {X : Type u} {Y : Type v} (t : TopologicalSpace X) (e : MetricSpace Y)
    (f : X → Y) (he : SequentiallyComplete e.toPseudoMetricSpace)
    (hf : @IsEmbedding X Y t (metricTopology e.toPseudoMetricSpace) f) :
    CompletelyMetrizable t ↔
      @IsGδ Y (metricTopology e.toPseudoMetricSpace) (range f) := by
  constructor
  · intro hX
    exact completelyMetrizable_image_isGdelta t e f hX hf
  · intro hG
    let := t
    let := e
    have hR := complete_gdelta_sufficient e (range f) he hG
    exact completelyMetrizable_of_homeomorph hf.toHomeomorph hR

/-- The completion of any compatible metric may be used in the criterion. -/
theorem completelyMetrizable_iff_gdelta_completion
    {X : Type u} (t : TopologicalSpace X) (d : MetricSpace X)
    (hd : metricTopology d.toPseudoMetricSpace = t) :
    CompletelyMetrizable t ↔
      @IsGδ (MetricCompletion d) (metricTopology (completionMetric d).toPseudoMetricSpace)
        (range (completionEmbedding d)) := by
  subst t
  exact completelyMetrizable_iff_gdelta_range _ (completionMetric d)
    (completionEmbedding d) (completion_complete d) (completion_isEmbedding d)

/-- G_delta subspaces inherit complete metrizability from the topology. -/
theorem gdelta_subspace_completelyMetrizable {X : Type u}
    (t : TopologicalSpace X) (A : Set X) (hX : CompletelyMetrizable t)
    (hA : @IsGδ X t A) :
    CompletelyMetrizable (t.induced (Subtype.val : A → X)) := by
  obtain ⟨d, rfl, hd⟩ := hX
  exact complete_gdelta_sufficient d A hd hA

theorem open_subspace_completelyMetrizable {X : Type u}
    (t : TopologicalSpace X) (A : Set X) (hX : CompletelyMetrizable t)
    (hA : IsOpen[t] A) :
    CompletelyMetrizable (t.induced (Subtype.val : A → X)) := by
  let := t
  exact gdelta_subspace_completelyMetrizable t A hX hA.isGδ

theorem countable_intersection_completelyMetrizable
    {X : Type u} {ι : Type w} [Countable ι]
    (t : TopologicalSpace X) (G : ι → Set X) (hX : CompletelyMetrizable t)
    (hG : ∀ i, IsOpen[t] (G i)) :
    CompletelyMetrizable (t.induced (Subtype.val : (⋂ i, G i) → X)) := by
  let := t
  exact gdelta_subspace_completelyMetrizable t _ hX (IsGδ.iInter_of_isOpen hG)

/-- Closed sets retain completeness of the chosen complete metric itself. -/
theorem closed_subspace_completelyMetrizable {X : Type u}
    (t : TopologicalSpace X) (A : Set X) (hX : CompletelyMetrizable t)
    (hA : IsClosed[t] A) :
    CompletelyMetrizable (t.induced (Subtype.val : A → X)) := by
  obtain ⟨d, rfl, hd⟩ := hX
  exact ⟨MetricSpace.induced Subtype.val Subtype.val_injective d, rfl,
    closed_subspace_complete d A hd hA⟩

/-- The usual irrational subspace is a countable intersection of the open
complements of rational singletons in the complete real line. -/
theorem irrationals_completelyMetrizable :
    CompletelyMetrizable
      ((inferInstance : TopologicalSpace ℝ).induced
        (Subtype.val : {x : ℝ // Irrational x} → ℝ)) := by
  apply complete_gdelta_sufficient (inferInstance : MetricSpace ℝ) {x | Irrational x}
  · exact (sequentiallyComplete_iff_mathlib _).mpr inferInstance
  · exact IsGδ.setOfPred_irrational

end D10Topology.Ch10
