import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.Definitions

open AlgebraicGeometry CategoryTheory
open Specs.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement (complement)

namespace Specs.CommutativeAlgebraNotes.ExtensionAcrossSupport

universe u

/-- The restriction to the complement of the ideal's vanishing locus is an
isomorphism exactly when the ideal has grade at least two on the module. -/
def restrictionIsIsoIffGradeType : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M],
    IsIso (tilde.toOpen M (complement R I)) ↔ 2 ≤ AdvCommAlg.Depth.grade I M

end Specs.CommutativeAlgebraNotes.ExtensionAcrossSupport
