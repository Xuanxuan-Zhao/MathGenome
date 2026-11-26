import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open AlgebraicGeometry

universe u

namespace LinearAlgebraicGroups.Specs

/-- Cartier's theorem for affine group schemes of finite type over a field. -/
def CharacteristicZeroSmoothness : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (G : AffineAlgebraicGroup k),
    Smooth G.1.X.hom

end LinearAlgebraicGroups.Specs
