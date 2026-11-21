import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.VectorMeasureVariation
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import Mathlib.Topology.Algebra.Module.Basic

/-! Independent statements for `fa2:p4:reflexive-measure-range`.
The vector measure is countably additive in norm, and its variation is the
finite-partition variation. No density, separability, or scalar control
measure is assumed. Both real and complex scalars are included. -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
universe u v
namespace ExpandedFA.PartIV.ReflexiveMeasureRangeSpec

/-- The literal closed scalar-linear span of all values of the measure.
Nonmeasurable sets have value zero in the native vector-measure interface. -/
def rangeSpan (𝕜 : Type) [RCLike 𝕜] {X : Type u} {Y : Type v}
    [MeasurableSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (m : VectorMeasure X Y) : Submodule 𝕜 Y :=
  (Submodule.span 𝕜 (range m)).topologicalClosure

def CompactRange : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {Y : Type v}
    [MeasurableSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [CompleteSpace Y], P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 Y →
    ∀ m : VectorMeasure X Y, m.variation univ < ∞ →
      IsCompact (closure (range m))

def SeparableReflexiveSpan : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {Y : Type v}
    [MeasurableSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [CompleteSpace Y], P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 Y →
    ∀ m : VectorMeasure X Y, m.variation univ < ∞ →
      SeparableSpace (rangeSpan 𝕜 m) ∧ CompleteSpace (rangeSpan 𝕜 m) ∧
        P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 (rangeSpan 𝕜 m)

end ExpandedFA.PartIV.ReflexiveMeasureRangeSpec
