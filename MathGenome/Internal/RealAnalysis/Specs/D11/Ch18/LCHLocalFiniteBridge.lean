import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates

/-!
Independent statement of paper.tex:5338–5345.
The domain is exactly the Borel sigma-algebra on a locally compact Hausdorff
space. Both predicates retain the quantifiers fixed in the shared Specs;
there is no nonemptiness, countability, or regularity hypothesis.
-/
namespace Specs.D11.Ch18.LCHLocalFiniteBridge

open MeasureTheory

universe u

/-- Compact finiteness is equivalent to an open finite-mass neighborhood
at every point, including when the underlying space is empty. -/
def compactFinite_iff_locallyFinite : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)),
    RadonPredicates.compactFiniteValue μ ↔ RadonPredicates.locallyFiniteValue μ

end Specs.D11.Ch18.LCHLocalFiniteBridge
