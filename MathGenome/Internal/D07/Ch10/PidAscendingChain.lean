import MathGenome.Internal.Specs.D07.Ch10.PidAscendingChain
import MathGenome.Internal.D07.Ch10.PidDefinition
import Mathlib.RingTheory.Noetherian.Defs

/-!
Ascending ideal chains and maximal members of collections in a PID,
`lem:pid-acc`, paper.tex:1965–1976.

Each ideal has a singleton generating set, hence is finitely generated.
The Noetherian characterizations then give both the stabilization of increasing
sequences and the maximal-member assertion for arbitrary nonempty collections.
-/

universe u

namespace D07.Ch10.PidAscendingChain

open Specs.D07.Ch10.PidAscendingChain

/-- A PID is Noetherian because each ideal has a singleton generating set. -/
theorem noetherian_of_pid (R : Type u) [CommRing R]
    (h : D07.Ch10.PidDefinition.IsPID R) : IsNoetherian R R := by
  constructor
  intro I
  obtain ⟨a, ha⟩ := h.2 I
  exact ⟨{a}, by simpa only [Finset.coe_singleton] using ha.symm⟩

theorem ascending_chains_stabilize : AscendingChainsStabilize.{u} := by
  intro R _ h I hI
  have hN : IsNoetherian R R := noetherian_of_pid R h
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr hN
    (⟨I, hI⟩ : ℕ →o Ideal R)
  exact ⟨n, fun m hm => (hn m hm).symm⟩

theorem nonempty_collection_has_maximal_member :
    NonemptyCollectionHasMaximalMember.{u} := by
  intro R _ h S hS
  have hN : IsNoetherian R R := noetherian_of_pid R h
  obtain ⟨I, hIS, hmax⟩ := set_has_maximal_iff_noetherian.mpr hN S hS
  refine ⟨I, hIS, ?_⟩
  intro J hJS hIJ
  exact (eq_of_le_of_not_lt hIJ (hmax J hJS)).symm

end D07.Ch10.PidAscendingChain
