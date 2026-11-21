import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarDefinition

/-!
Independent specification for `paper.tex:5864–5866`,
`D11.21.haar_existence`.

The measurable space is exactly the Borel sigma-algebra. The shared Haar
predicate requires nonzero mass, compact finiteness, outer regularity on
Borel sets, compact inner regularity on opens, and left invariance on Borel
sets. No countability or sigma-finiteness hypothesis is imposed.
-/

namespace Specs.D11.Ch21.HaarExistence

open MeasureTheory

universe u

/-- Every Hausdorff locally compact topological group admits a left Haar measure. -/
def haar_existence : Prop :=
  ∀ (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G],
    ∃ μ : @Measure G (borel G), HaarDefinition.leftHaarValue μ

end Specs.D11.Ch21.HaarExistence
