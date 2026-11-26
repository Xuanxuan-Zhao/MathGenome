import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescent

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianLeviDescent

open _root_.LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
  (DiagramPresentation)
open CharacterDescent (Cocharacter)
open GeometricBorelConjugacy (IsQuasiSplit)
open GeometricRadicals (IsSemisimple)
open RelativeFormComparison (IsInduced)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (baseChangedAlgebraicGroup)

/-- An isotropic simply connected trialitarian form descends quasi-splitness
from the cubic field marked by the three outer vertices. The marking uses the
relative comparison induced by an isomorphism of the actual scalar extensions. -/
def QuasiSplitDescent : Prop :=
  ∀ (F E S : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field E] [Field S] [Algebra F E] [Algebra F S]
    [Algebra E S] [IsScalarTower F E S]
    [Module.Finite F E] [Algebra.IsSeparable F E] [IsSepClosure F S],
    Module.finrank F E = 3 → ∀ (G : AffineAlgebraicGroup F) (D : DiagramPresentation G E S)
      (e : (groupBaseChange F S).obj D.pinned.pair.G.val ≅ (groupBaseChange F S).obj G.val),
      IsInduced F S e D.form →
      IsSemisimple G → GeometricallySimplyConnected G →
      (∃ (c : Cocharacter G.val) (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes c g) →
      IsQuasiSplit (baseChangedAlgebraicGroup E G) →
      IsQuasiSplit G

end LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianLeviDescent
