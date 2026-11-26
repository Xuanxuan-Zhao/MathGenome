import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.TorsorObstruction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.BorelProper

universe u

namespace LinearAlgebraicGroups.Specs.Relative.RationalFlagLifting

open BorelProper (IsParabolic)
open TorsorObstruction (rationalCosetMap)

/-- For a connected reductive group over an arbitrary field and a parabolic
over that field, the canonical map from rational right cosets to rational
points of the right fppf quotient is bijective. -/
def CanonicalCosetMapBijective : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    IsParabolic G P → Function.Bijective (rationalCosetMap P)

end LinearAlgebraicGroups.Specs.Relative.RationalFlagLifting
