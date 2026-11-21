import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.LCHLocalFiniteBridge

/-!
The local/compact finiteness bridge of paper.tex:5338–5345.

The native finiteness classes have already been identified with the shared
predicates. A compact neighborhood gives finite mass near each point in
the forward direction. The reverse direction bounds a compact set by a
finite cover of finite-mass neighborhoods. Neither argument requires any
measure regularity or a nonempty underlying space.
-/
namespace D11.Ch18

open MeasureTheory

universe u

/-- On an LCH Hausdorff space, a positive Borel measure is finite on
compact sets iff every point has an open neighborhood of finite mass. -/
theorem compactFinite_iff_locallyFinite
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borelSpace X)) :
    compactFinite μ ↔ locallyFinite μ := by
  constructor
  · intro h
    let : IsFiniteMeasureOnCompacts μ := (compactFinite_iff μ).mp h
    exact (locallyFinite_iff μ).mpr
      isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  · intro h
    let : IsLocallyFiniteMeasure μ := (locallyFinite_iff μ).mp h
    exact (compactFinite_iff μ).mpr
      isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure

end D11.Ch18
