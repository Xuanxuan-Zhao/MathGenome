import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointBorelCohomology

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.PinnedPairDescent

open Pinning (AttachedDatum PinnedGroup)
open RootGroups (AdditiveLine)
open GeometricRadicals (IsReductive IsTorus)
open GeometricBorelConjugacy (IsKBorel)
open RankOneFlag (IsGeometricallyMaximal)
open AdjointBorelCohomology (PinnedTwist)
open AutomorphismSequence (AdjointQuotient SplitSequence)

variable {k : Type u} [Field k]
variable (K : Type u) [Field K] [Algebra k K]
variable {L : AdditiveLine k} {P : PinnedGroup L}
variable {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}

/-- The group and rational Borel pair descended along the specified pinned lift. -/
structure DescendedPair (ω : Gal(K/k) →* Aut D.toBased) where
  group : AffineAlgebraicGroup k
  reductive : IsReductive group
  borel : ClosedSubgroup group.val
  torus : ClosedSubgroup group.val
  isKBorel : IsKBorel borel
  isTorus : IsTorus torus.group
  isMaximal : IsGeometricallyMaximal torus
  inclusion : torus.group ⟶ borel.group
  inclusion_comm : inclusion ≫ borel.inclusion = torus.inclusion
  data : PinnedTwist (P := P) K D l borel torus
  outer_eq : data.outer = ω

/-- Effective finite Galois descent of the pinned Borel and maximal torus. -/
def Statement : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {L : AdditiveLine k} {P : PinnedGroup L} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G},
    SplitSequence P D l Q → ∀ ω : Gal(K/k) →* Aut D.toBased,
      Nonempty (DescendedPair (l := l) K ω)

end LinearAlgebraicGroups.Specs.PinnedPairDescent
