import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalQuotientMixing

set_option autoImplicit false

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianCompletionMixingCases

open GeometricRadicals (IsSemisimple)
open LocalQuotientMixing (MixingCases)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open TrialitarianLocalForms (D4Diagram)

/-- A finite local form with a marked `D₄` diagram satisfies the local
mixing hypotheses on the given group. The diagram may lose transitivity
under scalar extension from the global field. -/
def Statement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (J : AffineAlgebraicGroup F),
    IsSemisimple J → GeometricallySimplyConnected J → D4Diagram J → MixingCases J

end LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianCompletionMixingCases
