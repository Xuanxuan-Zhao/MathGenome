import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricCompletion
import Mathlib.Topology.GDelta.Basic
import Mathlib.NumberTheory.Real.Irrational

/-! Independent specifications of the consequences in d10:10:complete-gdelta
and d10:10:open-gdelta-complete. Completeness always means existence of a new
compatible complete metric. The topology on every subset is the induced one.
No separability or nonemptiness is assumed. -/

open scoped Topology
universe u v w
namespace Specs.D10Topology.Ch10.CompleteMetrizabilityConsequences
open Specs.D10Topology.Ch09.MetricConventions
open Specs.D10Topology.Ch09.MetricCompletion

/-- Every metric embedding of a completely metrizable space has G_delta range. -/
def completelyMetrizable_image_isGdelta : Prop :=
  ∀ {X : Type u} {Y : Type v} (t : TopologicalSpace X) (e : MetricSpace Y)
    (f : X → Y), CompletelyMetrizable t →
    @Topology.IsEmbedding X Y t (metricTopology e.toPseudoMetricSpace) f →
    @IsGδ Y (metricTopology e.toPseudoMetricSpace) (Set.range f)

/-- In particular this applies to every completion, since only an embedding
into a complete metric space is needed for the equivalence. -/
def completelyMetrizable_iff_gdelta_range : Prop :=
  ∀ {X : Type u} {Y : Type v} (t : TopologicalSpace X) (e : MetricSpace Y)
    (f : X → Y), SequentiallyComplete e.toPseudoMetricSpace →
    @Topology.IsEmbedding X Y t (metricTopology e.toPseudoMetricSpace) f →
    (CompletelyMetrizable t ↔
      @IsGδ Y (metricTopology e.toPseudoMetricSpace) (Set.range f))

/-- Every compatible metric, whether complete itself or not, can be used. -/
def completelyMetrizable_iff_gdelta_completion : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (d : MetricSpace X),
    metricTopology d.toPseudoMetricSpace = t →
    (CompletelyMetrizable t ↔
      @IsGδ (completionValue d) (metricTopology (completionMetricValue d).toPseudoMetricSpace)
        (Set.range (completionEmbeddingValue d)))

def gdelta_subspace_completelyMetrizable : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (A : Set X),
    CompletelyMetrizable t → @IsGδ X t A →
    CompletelyMetrizable (t.induced (Subtype.val : A → X))

def open_subspace_completelyMetrizable : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (A : Set X),
    CompletelyMetrizable t → IsOpen[t] A →
    CompletelyMetrizable (t.induced (Subtype.val : A → X))

def countable_intersection_completelyMetrizable : Prop :=
  ∀ {X : Type u} {ι : Type w} [Countable ι] (t : TopologicalSpace X) (G : ι → Set X),
    CompletelyMetrizable t → (∀ i, IsOpen[t] (G i)) →
    CompletelyMetrizable (t.induced (Subtype.val : (⋂ i, G i) → X))

def closed_subspace_completelyMetrizable : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (A : Set X),
    CompletelyMetrizable t → IsClosed[t] A →
    CompletelyMetrizable (t.induced (Subtype.val : A → X))

def irrationals_completelyMetrizable : Prop :=
  CompletelyMetrizable
    ((inferInstance : TopologicalSpace ℝ).induced (Subtype.val : {x : ℝ // Irrational x} → ℝ))

end Specs.D10Topology.Ch10.CompleteMetrizabilityConsequences
