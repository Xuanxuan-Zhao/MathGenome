import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.IsogenyLattices

open AbstractPairing (Datum)
open CentralIsogenies (CentralIsogenyComparison IsCentralIsogeny IsTorusRestriction)
open CharacterDescent (Cocharacter)
open GeometricRadicals (IsSemisimple IsSplitTorus)
open Pinning (AttachedDatum SplitBorelPair)
open RankOneFlag (IsGeometricallyMaximal)
open SimplyConnectedLattice (AdjointForm GeometricallySimplyConnected corootLattice corootLatticeOf)

/-- The split simply connected cover identifies its cocharacters with the
coroot lattice of the given pair via pushforward. The given group is
geometrically simply connected exactly when its coroots generate all cocharacters. -/
def SimplyConnectedForm : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsSemisimple G →
    ∀ (T : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
      ∃ comm : IsCommMonObj T.group.X, letI := comm
        ∃ D : Datum T,
          (GeometricallySimplyConnected G ↔ corootLatticeOf D = ⊤) ∧
          ∃ (S : SplitBorelPair k) (E : AttachedDatum S)
            (f : S.G.val ⟶ G.val) (fT : S.T.group ⟶ T.group),
            IsSemisimple S.G ∧ GeometricallySimplyConnected S.G ∧
            IsCentralIsogeny f ∧ IsTorusRestriction f fT ∧ corootLattice E = ⊤ ∧
            letI := E.comm
            ∃ e : Additive (Cocharacter S.T.group) ≃ₗ[ℤ] corootLatticeOf D,
              ∀ c : Cocharacter S.T.group,
                (e (Additive.ofMul c)).val = Additive.ofMul (c ≫ fT)

/-- The central-isogeny comparison and the adjoint and simply connected
lattice identifications over an arbitrary field. -/
def Statement : Prop :=
  CentralIsogenyComparison.{u} ∧ AdjointForm.{u} ∧ SimplyConnectedForm.{u}

end LinearAlgebraicGroups.Specs.IsogenyLattices
