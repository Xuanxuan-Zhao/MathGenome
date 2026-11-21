import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies

/-! Independent statement of paper.tex, `d10:13:ascoli` (a).
The domain is any topological space and the target is any metric space.
The closure and compactness both use the explicitly defined compact-open
topology on all continuous maps. No nonemptiness, completeness, separation
or local compactness hypothesis is imposed. -/

universe u v

namespace Specs.D10Topology.Ch13.AscoliSufficiency

open FunctionTopologies

def ascoli_sufficiency : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (A : Set (ContinuousMaps X Y)),
    Equicontinuous A → PointwiseRelativelyCompact A →
    @IsCompact (ContinuousMaps X Y) compactOpenContinuousTopology
      (@closure (ContinuousMaps X Y) compactOpenContinuousTopology A)

end Specs.D10Topology.Ch13.AscoliSufficiency
