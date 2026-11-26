import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalQuotientMixing

set_option autoImplicit false

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.ExceptionalCompletionMixingCases

open ExceptionalLocalRadicalGeneration (HasAbsoluteTypeE)
open LocalQuotientMixing (MixingCases)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- A simply connected absolutely almost simple group of absolute type
`E₆`, `E₇` or `E₈` over a nonarchimedean local field satisfies the local
mixing case predicate on the original affine group. -/
def ExceptionalMixingCases : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (J : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple J → GeometricallySimplyConnected J →
    (HasAbsoluteTypeE J 6 ∨ HasAbsoluteTypeE J 7 ∨ HasAbsoluteTypeE J 8) →
    MixingCases J

end LinearAlgebraicGroups.Specs.Arithmetic.ExceptionalCompletionMixingCases
