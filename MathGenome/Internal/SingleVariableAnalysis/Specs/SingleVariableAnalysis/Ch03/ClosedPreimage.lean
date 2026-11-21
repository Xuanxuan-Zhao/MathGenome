import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Continuity

/-!
Independent specification for K03.03.closed_preimage (paper.tex:521–529).

Both source and target are arbitrary metric subspaces, with their induced
metrics and topologies. Thus `IsOpen (U : Set F)` and `IsClosed (C : Set F)`
mean relative openness and closedness in the target, and the preimages are
tested in the source subtype E. The continuity predicate below is the
upstream, unpunctured epsilon–delta predicate on the entire source subtype.
No nonemptiness, openness, closedness or compactness of E or F is assumed.
-/
namespace Specs.SingleVariableAnalysis.Ch03.ClosedPreimage

open Specs.SingleVariableAnalysis.Ch03.Continuity
universe u v

/-- Bridge from the upstream metric definition on a whole space. -/
def relativeContinuousUnivIff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y] (f : X → Y),
    relativeContinuousValue f Set.univ ↔ Continuous f

/-- Every relative open target set has relative open preimage, exactly for
the epsilon–delta continuous maps between the two metric subspaces. -/
def metricSubspaceContinuousIffOpenPreimage : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (F : Set Y) (f : E → F),
    relativeContinuousValue f Set.univ ↔
      ∀ U : Set F, IsOpen U → IsOpen (f ⁻¹' U)

/-- The equivalent characterization by all relative closed target sets. -/
def metricSubspaceContinuousIffClosedPreimage : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (F : Set Y) (f : E → F),
    relativeContinuousValue f Set.univ ↔
      ∀ C : Set F, IsClosed C → IsClosed (f ⁻¹' C)

end Specs.SingleVariableAnalysis.Ch03.ClosedPreimage
