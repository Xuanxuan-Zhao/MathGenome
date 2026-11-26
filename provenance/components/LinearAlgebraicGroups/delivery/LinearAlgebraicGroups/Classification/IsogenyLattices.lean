import Specs.LinearAlgebraicGroups.Classification.IsogenyLattices
import LinearAlgebraicGroups.Classification.CentralIsogenies
import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import Batteries.Tactic.OpenPrivate

universe u

namespace LinearAlgebraicGroups.Classification.IsogenyLattices

open Specs.IsogenyLattices
open CentralIsogenies (centralIsogenyComparison)
open SimplyConnectedLattice (adjointForm latticeCriterion splitCover)
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies

private theorem simplyConnectedForm : SimplyConnectedForm.{u} := by
  intro k _ G hG T hsplit hmax
  obtain ⟨comm, ⟨D⟩⟩ :=
    RootData.AbstractPairing.abstractPairing G (reductive_of_semisimple G hG) T hsplit hmax
  let _ := comm
  exact ⟨comm, D, latticeCriterion G hG T hsplit hmax D, splitCover G hG T hsplit hmax D⟩

/-- Central isogenies identify the roots, root group schemes and coroots.
For split semisimple groups the adjoint and simply connected forms have
the root character lattice and the coroot cocharacter lattice, respectively. -/
theorem isogenyLattices : Statement.{u} :=
  ⟨centralIsogenyComparison, adjointForm, simplyConnectedForm⟩

end LinearAlgebraicGroups.Classification.IsogenyLattices
