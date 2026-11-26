import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import Mathlib.FieldTheory.Galois.Basic

universe u

namespace LinearAlgebraicGroups.Specs.CentralCoverDescent

open CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open GeometricRadicals (IsSemisimple IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (baseChangedAlgebraicGroup)

/-- The simply connected central cover descends through a given finite
Galois splitting extension and covers the specified maximal torus. -/
def CoverDescent : Prop :=
  ∀ {K E : Type u} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (G : AffineAlgebraicGroup K), IsSemisimple G →
    let G' := baseChangedAlgebraicGroup E G
    ∀ (S : ClosedSubgroup G'.val), IsSplitTorus S.group → IsGeometricallyMaximal S →
      ∃ (H : AffineAlgebraicGroup K) (q : H.val ⟶ G.val),
        IsSemisimple H ∧ GeometricallySimplyConnected H ∧
        let H' := baseChangedAlgebraicGroup E H
        let q' := (groupBaseChange K E).map q
        IsCentralIsogeny q' ∧
          ∃ (T : ClosedSubgroup H'.val) (qT : T.group ⟶ S.group),
            IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧ IsTorusRestriction q' qT

end LinearAlgebraicGroups.Specs.CentralCoverDescent
