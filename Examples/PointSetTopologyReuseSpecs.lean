import MathGenome

/-! Independent downstream statements for admission of PointSetTopology.
These are explicit mathematical applications, rather than name-existence checks.
The candidate curator preserves D10Topology.* and D04.* declaration names.
-/

open Set
universe u v

namespace Specs.GenomeTopologyProbe

def arbitrary_products : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @CompactSpace (X i) (tX i)) →
      @CompactSpace (∀ i, X i) (@Pi.topologicalSpace I X tX)

def closed_set_separation : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], NormalSpace X →
    ∀ A B : Set X, IsClosed A → IsClosed B → Disjoint A B →
      ∃ f : X → unitInterval, Continuous f ∧
        (∀ x ∈ A, f x = 0) ∧ (∀ x ∈ B, f x = 1)

def interval_extension : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], NormalSpace X →
    ∀ A : Set X, IsClosed A → ∀ a b : ℝ, a ≤ b →
      ∀ f : A → Icc a b, Continuous f →
        ∃ F : X → Icc a b, Continuous F ∧ ∀ x : A, F x = f x

def compact_neighborhood : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X],
    ∀ C U : Set X, IsCompact C → IsOpen U → C ⊆ U →
      ∃ V : Set X, IsOpen V ∧ C ⊆ V ∧ V ⊆ closure V ∧
        closure V ⊆ U ∧ IsCompact (closure V)

def canonical_metric_completion : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    @CompleteSpace (D10Topology.Ch09.MetricCompletion d)
      (D10Topology.Ch09.completionMetric d).toUniformSpace ∧
    @_root_.Isometry X (D10Topology.Ch09.MetricCompletion d)
      (@PseudoMetricSpace.toPseudoEMetricSpace X d.toPseudoMetricSpace)
      (@PseudoMetricSpace.toPseudoEMetricSpace (D10Topology.Ch09.MetricCompletion d)
        (D10Topology.Ch09.completionMetric d).toPseudoMetricSpace)
      (D10Topology.Ch09.completionEmbedding d) ∧
    @DenseRange (D10Topology.Ch09.MetricCompletion d)
      (D10Topology.Ch09.completionMetric d).toUniformSpace.toTopologicalSpace X
      (D10Topology.Ch09.completionEmbedding d)

def euclidean_compact_bridge : Prop :=
  ∀ (n : ℕ) (K : Set (D04.E n)), IsClosed K →
    (∃ B : ℝ, ∀ x ∈ K, ‖x‖ ≤ B) → D10Topology.Ch05.SubspaceCompact K

end Specs.GenomeTopologyProbe
