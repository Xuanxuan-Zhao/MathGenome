import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformizableTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformTopology
import Mathlib.Topology.UniformSpace.Uniformizable

/-! The uniformizability corollary of paper.tex (`d10:12:uniformizable`).
Mathlib's complete regularity uses 0 at the point and 1 on the closed set;
the accepted Chapter 7 bridge reverses these values. Its uniformizability
theorem proves equality of topologies without any point-separation assumption.
The accepted Chapter 12 bridge identifies that topology with the paper's
entourage-section construction, including the degenerate empty uniformity.
-/

universe u

namespace D10Topology.Ch12

theorem uniformTopology_completelyRegular {X : Type u} [UniformSpace X] :
    @Ch07.CompletelyRegular X uniformTopology := by
  rw [uniformTopology_eq_canonical]
  exact (Ch07.completelyRegular_iff_mathlib X).mpr inferInstance

theorem uniformizable_iff_completelyRegular (X : Type u) [t : TopologicalSpace X] :
    (∃ uX : UniformSpace X, @uniformTopology X uX = t) ↔
      Ch07.CompletelyRegular X := by
  have htop (uX : UniformSpace X) :
      @uniformTopology X uX = uX.toTopologicalSpace :=
    @uniformTopology_eq_canonical X uX
  simp_rw [htop]
  exact completelyRegularSpace_iff_exists_uniformSpace.symm.trans
    (Ch07.completelyRegular_iff_mathlib X).symm

theorem separated_uniformTopology_tychonoff {X : Type u} [UniformSpace X]
    (h : Separated (X := X)) : @Ch07.Tychonoff X uniformTopology := by
  exact ⟨uniformTopology_completelyRegular,
    uniformTopology_hausdorff_iff_separated.mpr h⟩

theorem empty_uniformizable (X : Type u) [t : TopologicalSpace X] [IsEmpty X] :
    ∃ uX : UniformSpace X, @uniformTopology X uX = t := by
  apply (uniformizable_iff_completelyRegular X).mpr
  intro F hF x
  exact isEmptyElim x

end D10Topology.Ch12
