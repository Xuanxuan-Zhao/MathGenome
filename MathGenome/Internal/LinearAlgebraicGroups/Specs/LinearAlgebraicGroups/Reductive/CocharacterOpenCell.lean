import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open AlgebraicGeometry

universe u

namespace LinearAlgebraicGroups.Specs.CocharacterDynamics

open LinearAlgebraicGroups.CocharacterDynamics
open CharacterDescent (Cocharacter)

/-- The three-factor multiplication for a cocharacter and its opposite is an
open immersion. -/
def BigCell : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    (cochar : Cocharacter G.val) (D : LimitDecomposition cochar)
    (Dneg : LimitDecomposition (oppositeCocharacter cochar)),
    IsOpenImmersion (bigCellMap D Dneg).left

/-- In a smooth connected group the three limit subgroups are geometrically
connected. -/
def GeometricallyConnectedLimitSubgroups : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    [ConnectedSpace G.val.X.left] (cochar : Cocharacter G.val) (D : LimitDecomposition cochar),
    GeometricallyConnected D.parabolic.group.X.hom ∧
      GeometricallyConnected D.contracting.group.X.hom ∧
      GeometricallyConnected D.centralizer.group.X.hom

end LinearAlgebraicGroups.Specs.CocharacterDynamics
