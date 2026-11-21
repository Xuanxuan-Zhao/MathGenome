import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.CantorModel
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.QuasiComponents

/-! Independent statements of paper.tex, d10:18:cantor-characterization.
The target is the actual product of discrete binary factors indexed by positive
integers, with its product topology. No isolated points means that no singleton
is open. Zero-dimensionality and total disconnectedness are the canonical
Chapter 6 predicates, not definitions in terms of the desired homeomorphism. -/

open Set TopologicalSpace
universe u
namespace Specs.D10Topology.Ch18.CantorCharacterization
open _root_.D10Topology.Ch06.QuasiComponentsData
open Specs.D10Topology.Ch18.CantorModel

def cantor_characterization : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [Nonempty X] [CompactSpace X]
    [MetrizableSpace X], ZeroDimensional X →
    (∀ x : X, ¬ IsOpen ({x} : Set X)) → Nonempty (X ≃ₜ CantorSpace)

def cantor_characterization_totallyDisconnected : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [Nonempty X] [CompactSpace X]
    [MetrizableSpace X], TotallyDisconnected X →
    (∀ x : X, ¬ IsOpen ({x} : Set X)) → Nonempty (X ≃ₜ CantorSpace)

def cantor_characterization_hypotheses : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X],
    ZeroDimensional X ↔ TotallyDisconnected X

end Specs.D10Topology.Ch18.CantorCharacterization
