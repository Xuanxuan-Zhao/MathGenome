import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.Continuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.ClosedPreimage

/-!
# Open and closed preimages in metric subspaces

K03.03.closed_preimage, paper.tex:521–529. The canonical subtype topology
is the relative topology, as identified by `relativeOpen_iff` and
`relativeClosed_iff` in the upstream continuity module. We first connect
its epsilon–delta predicate to `Continuous` on a whole metric space.
Mathlib's `continuous_def` then gives the open-preimage criterion, and
`continuous_iff_isClosed` gives its equivalent closed-preimage criterion
by taking complements. These results are applied to E and F themselves,
so neither subspace is required to be open or closed in its ambient space.
-/
namespace SingleVariableAnalysis

universe u v

theorem relativeContinuous_univ_iff
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    RelativeContinuous f Set.univ ↔ Continuous f := by
  simp only [RelativeContinuous, Set.mem_univ, forall_const,
    relativeContinuousAt_within_iff, continuousWithinAt_univ,
    continuous_iff_continuousAt]

theorem metricSubspace_continuous_iff_open_preimage
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (F : Set Y) (f : E → F) :
    RelativeContinuous f Set.univ ↔
      ∀ U : Set F, IsOpen U → IsOpen (f ⁻¹' U) :=
  (relativeContinuous_univ_iff f).trans continuous_def

theorem metricSubspace_continuous_iff_closed_preimage
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (F : Set Y) (f : E → F) :
    RelativeContinuous f Set.univ ↔
      ∀ C : Set F, IsClosed C → IsClosed (f ⁻¹' C) :=
  (relativeContinuous_univ_iff f).trans continuous_iff_isClosed

end SingleVariableAnalysis
