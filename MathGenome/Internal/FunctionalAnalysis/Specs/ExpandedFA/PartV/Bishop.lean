import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.AntisymmetricSets

/-! Bishop's theorem, `fa2:p5:bishop`, paper.tex 23416–23446.
The algebra may be nonunital and need not be self-adjoint. -/
namespace ExpandedFA.PartV.BishopSpec
open Set
open AntisymmetricSetsSpec
universe u

def BishopTheorem : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (A : NonUnitalSubalgebra ℂ C(K, ℂ)), IsClosed (A : Set C(K, ℂ)) →
    ∀ g : C(K, ℂ),
    (∀ S : Set K, IsMaximalClosedAntisymmetric A S →
      ∃ f ∈ A, ∀ x ∈ S, g x = f x) → g ∈ A

end ExpandedFA.PartV.BishopSpec
