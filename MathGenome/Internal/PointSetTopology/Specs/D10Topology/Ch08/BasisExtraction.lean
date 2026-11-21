import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions

/-!
Independent statements for paper.tex, d10:08:basis-extraction (lines 1055–1059).
The extracted basis is a subfamily of the given basis for the same topology.
Countable includes finite and empty; no nonemptiness or separation hypothesis
is imposed on the basis-extraction statement. The singleton statement uses
exactly first countability and T1, with the upstream neighborhood convention.
-/

open Set
universe u

namespace Specs.D10Topology.Ch08.BasisExtraction

def basis_contains_countable_basis : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    CountabilityConventions.secondCountableValue t →
    ∀ C : Set (Set X), Ch01.BasesAndNeighborhoods.BasisFor t C →
      ∃ B : Set (Set X), B ⊆ C ∧ B.Countable ∧
        Ch01.BasesAndNeighborhoods.BasisFor t B

def singleton_gdelta_of_firstCountable_t1 : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    CountabilityConventions.firstCountableValue t →
    Ch07.SeparationConventions.t1Value X →
    ∀ x : X, Ch07.SeparationConventions.gdeltaValue ({x} : Set X)

end Specs.D10Topology.Ch08.BasisExtraction
