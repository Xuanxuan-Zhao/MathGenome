import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.LocallyFiniteConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions
import Mathlib.Topology.Bases

/-!
Independent statements of paper.tex, d10:15:perfect-normal.
The basis is a family of subsets of the given space; its local-finiteness
layers use the canonical indexed convention. Regularity and T1 are separate
hypotheses. Empty spaces, bases, layers, and prescribed sets are allowed.
-/

open Set TopologicalSpace
universe u

namespace Specs.D10Topology.Ch15.PerfectNormal

open Specs.D10Topology.Ch15.LocallyFiniteConventions

def sigmaLocallyFinite_basis_normal : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [RegularSpace X] [T1Space X]
    (B : Set (Set X)), IsTopologicalBasis B →
    SigmaLocallyFinite (fun b : B => (b : Set X)) → NormalSpace X

def sigmaLocallyFinite_basis_closed_gdelta : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [RegularSpace X] [T1Space X]
    (B : Set (Set X)), IsTopologicalBasis B →
    SigmaLocallyFinite (fun b : B => (b : Set X)) →
    ∀ F : Set X, IsClosed F → IsGδ F

def sigmaLocallyFinite_basis_cozero : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [RegularSpace X] [T1Space X]
    (B : Set (Set X)), IsTopologicalBasis B →
    SigmaLocallyFinite (fun b : B => (b : Set X)) →
    ∀ O : Set X, IsOpen O → ∃ f : X → unitInterval,
      Continuous f ∧ O = {x | 0 < (f x : ℝ)}

end Specs.D10Topology.Ch15.PerfectNormal
