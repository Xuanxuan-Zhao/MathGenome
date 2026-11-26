import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AutomorphismSequence

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.CentralCoverPinnedLift

open AutomorphismSequence (forgetPinning)
open CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open GeometricRadicals (IsSemisimple IsSplitTorus)
open Pinning (PinnedGroup)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (AdditiveLine)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- A pinned automorphism of the target lifts through the given marked
simply connected central isogeny, including for a nonsmooth kernel. -/
def PinnedAutomorphismLifting : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k}
    (H : AffineAlgebraicGroup k) (P : PinnedGroup A),
    IsSemisimple H → IsSemisimple P.pair.G → GeometricallySimplyConnected H →
    ∀ (T : ClosedSubgroup H.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
      ∀ (q : H.val ⟶ P.pair.G.val) (qT : T.group ⟶ P.pair.T.group),
        IsCentralIsogeny q → IsTorusRestriction q qT →
        ∀ b : Aut P, ∃ c : Aut H.val,
          c.asIso.hom ≫ q = q ≫ (forgetPinning.mapAut P b).asIso.hom

end LinearAlgebraicGroups.Specs.CentralCoverPinnedLift
