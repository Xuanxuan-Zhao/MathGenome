import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.IsogenyFlagComparison

universe u

namespace LinearAlgebraicGroups.Specs.SimplyConnectedFlagCover

open CategoryTheory
open AbstractPairing (Root)
open BorelsAndChambers (subgroupRoots)
open CentralIsogenies (IsCentralIsogeny characterPullback)
open CharacterPairing (absoluteRoots)
open FlagLineBundle (OppositeBorelPair)
open GeometricRadicals (IsSemisimple)
open IsogenyFlagComparison (Restrictions)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- The simply connected central cover can be marked over the specified
negative Borel, with pullback preserving the positive system. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (G : AffineAlgebraicGroup k), IsSemisimple G → ∀ P : OppositeBorelPair G,
    ∃ (G' : AffineAlgebraicGroup k) (P' : OppositeBorelPair G')
      (f : G'.val ⟶ G.val),
      IsSemisimple G' ∧ GeometricallySimplyConnected G' ∧ IsCentralIsogeny f ∧
      ∃ r : Restrictions f P' P,
        (∀ β : Root P.torus, characterPullback r.torus β.val ∈ absoluteRoots P'.torus) ∧
        ∀ (β : Root P.torus)
          (hβ : characterPullback r.torus β.val ∈ absoluteRoots P'.torus),
          (⟨characterPullback r.torus β.val, hβ⟩ : Root P'.torus) ∈
            subgroupRoots P'.torus P'.positive ↔ β ∈ subgroupRoots P.torus P.positive

end LinearAlgebraicGroups.Specs.SimplyConnectedFlagCover
