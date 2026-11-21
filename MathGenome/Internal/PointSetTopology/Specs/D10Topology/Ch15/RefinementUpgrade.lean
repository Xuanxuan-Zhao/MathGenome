import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.LocallyFiniteConventions
import Mathlib.Topology.Separation.Regular

/-! Independent statement of paper.tex, d10:15:michael.
Regularity does not include T₁. Cover and refinement indices use the same
universe as the space, as in the canonical `ParacompactSpace` interface.
Empty spaces, empty families and repeated indexed members are permitted. -/

open Set
universe u

namespace Specs.D10Topology.Ch15.RefinementUpgrade

def refinement_upgrade : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], RegularSpace X →
    (∀ (I : Type u) (U : I → Set X), (∀ i, IsOpen (U i)) →
      (⋃ i, U i) = univ → ∃ (J : Type u) (V : J → Set X),
        (∀ j, IsOpen (V j)) ∧ LocallyFiniteConventions.SigmaLocallyFinite V ∧
          LocallyFiniteConventions.CoverRefinement U V) →
    LocallyFiniteConventions.Paracompact X

end Specs.D10Topology.Ch15.RefinementUpgrade
