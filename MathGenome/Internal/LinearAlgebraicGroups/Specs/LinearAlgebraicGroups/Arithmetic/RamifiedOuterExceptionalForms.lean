import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalFormsOverUnramifiedFields
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

open CategoryTheory

namespace LinearAlgebraicGroups.Specs.RamifiedOuterExceptionalForms

open AutomorphismSequence (AdjointQuotient SplitSequence relativePoints)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology (restriction)
open Descent.Forms (SchemeModels)
open ExceptionalFormsOverUnramifiedFields (HasTypeE)
open ExceptionalLocalRootCoordinates (ramificationIndex)
open GeometricBorelConjugacy (IsQuasiSplit)
open GeometricRadicals (IsSemisimple)
open Pinning (AttachedDatum PinnedGroup)
open QuasiSplitInnerForms (outerHom)
open RelativeFormComparison (fieldTest transportedAut)
open RootGroups (AdditiveLine)
open SimplyConnectedLattice (GeometricallySimplyConnected)

universe u

/-- A simply connected outer form of type E₆ over a nonarchimedean local field
is quasi-split if its quadratic diagram field is ramified. The split model,
separable trivialization, and outer action use the same pinned datum. -/
def RamifiedOuterQuasiSplit : Prop :=
  ∀ (F S : Type u) [Field F] [Field S] [Algebra F S] [IsSepClosure F S]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {A : AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q),
    IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G → HasTypeE D 6 →
    ∀ (L : FiniteGaloisIntermediateField F S) [ValuativeRel L] [TopologicalSpace L]
      [IsNonarchimedeanLocalField L] [ValuativeExtension F L],
      Module.finrank F L = 2 → 1 < ramificationIndex F L →
      ∀ (ω : Gal(L/F) →* Aut D.toBased), ω ≠ 1 →
      ∀ (H : SchemeModels S P.pair.G)
        (i : relativePoints P.pair.G.val (fieldTest F S) ≅
          relativePoints H.val.val (fieldTest F S)),
        (∀ σ, outerHom (S := S) E (transportedAut F S i σ) = ω (restriction L σ)) →
        IsQuasiSplit H.val

end LinearAlgebraicGroups.Specs.RamifiedOuterExceptionalForms
