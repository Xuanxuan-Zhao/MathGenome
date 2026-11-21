import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.ClosureCalculus
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.BasesAndNeighborhoods

/-!
Closure, interior, boundary, density and accumulation points, in the exact
scope of paper.tex, d10:01:closure-def, closure-test and closure-laws.
We reuse the canonical Mathlib objects, proving their descriptions in the
paper's set and neighborhood language. In particular frontier is identified
with the intersection of the two closures before its calculus is used, and
derivedSet is identified with the punctured neighborhood test. Local bases
may consist of nonopen neighborhoods. No separation axiom is assumed.
-/

open Set
open scoped Topology
universe u

namespace D10Topology.Ch01

variable {X : Type u} [t : TopologicalSpace X]

theorem closure_eq_closed_intersection (A : Set X) :
    closure A = ⋂₀ {F : Set X | IsClosed F ∧ A ⊆ F} := rfl

theorem interior_eq_open_union (A : Set X) :
    interior A = ⋃₀ {U : Set X | IsOpen U ∧ U ⊆ A} := rfl

theorem boundary_eq_closure_inter (A : Set X) :
    frontier A = closure A ∩ closure Aᶜ := frontier_eq_closure_inter_closure

theorem dense_iff_closure_univ (A : Set X) :
    Dense A ↔ closure A = univ := dense_iff_closure_eq

theorem closure_neighborhood_test (A : Set X) (x : X) :
    x ∈ closure A ↔ ∀ N : Set X, Neighborhood t x N → (N ∩ A).Nonempty := by
  constructor
  · intro hx N hN
    obtain ⟨U, hU, hxU, hUN⟩ := hN
    obtain ⟨y, hyU, hyA⟩ := mem_closure_iff.mp hx U hU hxU
    exact ⟨y, hUN hyU, hyA⟩
  · intro h
    apply mem_closure_iff.mpr
    intro U hU hxU
    exact h U ⟨U, hU, hxU, Subset.rfl⟩

theorem interior_neighborhood_test (A : Set X) (x : X) :
    x ∈ interior A ↔ Neighborhood t x A := by
  rw [neighborhood_iff_mem_nhds]
  exact mem_interior_iff_mem_nhds

theorem closure_localBase_test (A : Set X) (x : X) (L : Set (Set X)) (hL : LocalBase t x L) :
    x ∈ closure A ↔ ∀ V ∈ L, (V ∩ A).Nonempty := by
  rw [closure_neighborhood_test]
  constructor
  · intro h V hV
    exact h V (hL.1 V hV)
  · intro h N hN
    obtain ⟨V, hV, hVN⟩ := hL.2 N hN
    obtain ⟨y, hyV, hyA⟩ := h V hV
    exact ⟨y, hVN hyV, hyA⟩

theorem interior_localBase_test (A : Set X) (x : X) (L : Set (Set X)) (hL : LocalBase t x L) :
    x ∈ interior A ↔ ∃ V ∈ L, V ⊆ A := by
  rw [interior_neighborhood_test]
  constructor
  · exact hL.2 A
  · rintro ⟨V, hV, hVA⟩
    exact neighborhood_mono t x V A (hL.1 V hV) hVA

theorem derivedSet_eq_neighborhood_test (A : Set X) :
    derivedSet A = {x | ∀ N : Set X, Neighborhood t x N → (N ∩ (A \ {x})).Nonempty} := by
  ext x
  change AccPt x (Filter.principal A) ↔ _
  rw [accPt_principal_iff_clusterPt, ← mem_closure_iff_clusterPt]
  exact closure_neighborhood_test (A \ {x}) x

theorem closure_eq_union_derivedSet (A : Set X) :
    closure A = A ∪ derivedSet A := closure_eq_self_union_derivedSet A

theorem dense_iff_meets_open (A : Set X) :
    Dense A ↔ ∀ U : Set X, IsOpen U → U.Nonempty → (A ∩ U).Nonempty := by
  simpa only [inter_comm A] using (dense_iff_inter_open (s := A))

theorem closure_extensive (A : Set X) :
    A ⊆ closure A := subset_closure

theorem closure_monotone (A B : Set X) (hAB : A ⊆ B) :
    closure A ⊆ closure B := closure_mono hAB

theorem closure_idempotent (A : Set X) :
    closure (closure A) = closure A := closure_closure

theorem closure_of_empty :
    closure (∅ : Set X) = ∅ := closure_empty

theorem closure_binary_union (A B : Set X) :
    closure (A ∪ B) = closure A ∪ closure B := closure_union

theorem closure_finite_union (F : Set (Set X)) (hF : F.Finite) :
    closure (⋃₀ F) = ⋃ A ∈ F, closure A := hF.closure_sUnion

theorem closed_iff_closure_fixed (A : Set X) :
    IsClosed A ↔ closure A = A := closure_eq_iff_isClosed.symm

theorem interior_eq_complement_closure (A : Set X) :
    interior A = (closure Aᶜ)ᶜ := interior_eq_compl_closure_compl

theorem boundary_eq_closure_sdiff_interior (A : Set X) :
    frontier A = closure A \ interior A := rfl

theorem interior_intersection (A B : Set X) :
    interior (A ∩ B) = interior A ∩ interior B := interior_inter

theorem boundary_closed (A : Set X) :
    IsClosed (frontier A) := isClosed_frontier

theorem boundary_empty_iff_clopen (A : Set X) :
    frontier A = ∅ ↔ IsClopen A := isClopen_iff_frontier_eq_empty.symm

end D10Topology.Ch01
