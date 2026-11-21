import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.BasisExtraction
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.BasesAndNeighborhoods
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationConventions
import Mathlib.Topology.Separation.GDelta

/-!
The two conclusions of paper.tex, d10:08:basis-extraction.
The basis bridge preserves the paper's union-of-basis-members formulation.
The first-countability bridge allows arbitrary neighborhoods in local bases.
-/

open Set
universe u

namespace D10Topology.Ch08

variable {X : Type u} [t : TopologicalSpace X]

/-- Every prescribed basis of a second countable space contains a countable basis,
including when the underlying space is empty. -/
theorem basis_contains_countable_basis (h : SecondCountable t)
    (C : Set (Set X)) (hC : Ch01.BasisFor t C) :
    ∃ B : Set (Set X), B ⊆ C ∧ B.Countable ∧ Ch01.BasisFor t B := by
  let : SecondCountableTopology X := h
  obtain ⟨B, hBC, hc, hB⟩ := ((Ch01.basis_iff_mathlib t C).mp hC).exists_countable
  exact ⟨B, hBC, hc, (Ch01.basis_iff_mathlib t B).mpr hB⟩

/-- First countability and T1 suffice for each singleton to be G_delta. -/
theorem singleton_gdelta_of_firstCountable_t1 (h : FirstCountable t)
    (h1 : Ch07.T1 X) (x : X) : Ch07.GDelta ({x} : Set X) := by
  let : FirstCountableTopology X := firstCountable_iff_mathlib.mp h
  let : T1Space X := h1
  exact IsGδ.singleton x

end D10Topology.Ch08
