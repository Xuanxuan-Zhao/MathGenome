import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.CategoryInterface
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions

/-! Independent statements of paper.tex, d10:14:baire-subspaces.
Every conclusion uses the induced topology on the named subset. Empty
subspaces are allowed. Density is required only in the general Baire-space
case, not for the complete metric or LCH ambient spaces. -/

open Set
universe u

namespace Specs.D10Topology.Ch14.BaireSubspaces

def open_subspace_baire : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], CategoryInterface.baireValue X →
    ∀ A : Set X, IsOpen A → CategoryInterface.baireValue A

def dense_gdelta_subspace_baire : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], CategoryInterface.baireValue X →
    ∀ A : Set X, IsGδ A → Dense A → CategoryInterface.baireValue A

def gdelta_subspace_complete_metric_baire : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    Ch09.MetricConventions.SequentiallyComplete d.toPseudoMetricSpace →
    ∀ A : Set X,
      @IsGδ X (Ch09.MetricConventions.metricTopology d.toPseudoMetricSpace) A →
      @CategoryInterface.baireValue A
        (TopologicalSpace.induced (Subtype.val : A → X)
          (Ch09.MetricConventions.metricTopology d.toPseudoMetricSpace))

def gdelta_subspace_lch_baire : Prop :=
  ∀ {X : Type u} [TopologicalSpace X],
    Ch11.LocalCompactConventions.LCH X →
    ∀ A : Set X, IsGδ A → CategoryInterface.baireValue A

end Specs.D10Topology.Ch14.BaireSubspaces
