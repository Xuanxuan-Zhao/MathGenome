import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.CompactExhaustion
import Mathlib.Topology.Compactness.SigmaCompact

/-! Compact exhaustion and the full basic-topology proposition M01.01.

Local compactness and second countability give sigma compactness. Mathlib's
compact exhaustion then supplies the compact sets and their interior nesting.
Every point in K j belongs to the interior of K (j+1), so the interiors with
positive index cover the manifold. This argument requires no chosen point and
also applies to an empty manifold (where every subset, hence every K j, is empty).
-/

namespace SmoothManifolds.TopologicalManifold

open Set
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]

theorem exists_compact_exhaustion (A : TopologicalManifold n kind M) :
    ∃ K : ℕ → Set M,
      (∀ j, IsCompact (K j)) ∧
      (∀ j, K j ⊆ interior (K (j + 1))) ∧
      (⋃ (j : ℕ) (_ : 1 ≤ j), interior (K j)) = univ := by
  let := A.locallyCompactSpace
  let := A.secondCountable
  let K := CompactExhaustion.choice M
  refine ⟨K, K.isCompact, K.subset_interior_succ, ?_⟩
  apply eq_univ_of_forall
  intro p
  obtain ⟨j, hj⟩ := K.exists_mem p
  exact mem_iUnion.mpr ⟨j + 1, mem_iUnion.mpr
    ⟨Nat.succ_le_succ (Nat.zero_le j), K.subset_interior_succ j hj⟩⟩

/-- Basic topology of a manifold, with the entire conclusion of M01.01. -/
theorem basic_topology (A : TopologicalManifold n kind M) :
    LocallyCompactSpace M ∧ LocallyPathConnectedSpace M ∧
    (∃ C : Set (ModelChart n kind M), C.Countable ∧ C ⊆ A.atlas ∧
      ∀ p : M, ∃ c ∈ C, p ∈ c.source) ∧
    ParacompactSpace M ∧
    (∃ K : ℕ → Set M,
      (∀ j, IsCompact (K j)) ∧
      (∀ j, K j ⊆ interior (K (j + 1))) ∧
      (⋃ (j : ℕ) (_ : 1 ≤ j), interior (K j)) = univ) ∧
    (∀ p : M, IsOpen (connectedComponent p) ∧
      IsPathConnected (connectedComponent p)) ∧
    (Set.range (connectedComponent (α := M))).Countable :=
  ⟨A.locallyCompactSpace, A.locallyPathConnectedSpace, A.countable_chart_cover,
    A.paracompactSpace, A.exists_compact_exhaustion,
    fun p => ⟨A.isOpen_connectedComponent p, A.isPathConnected_connectedComponent p⟩,
    A.countable_connectedComponents⟩

end SmoothManifolds.TopologicalManifold
