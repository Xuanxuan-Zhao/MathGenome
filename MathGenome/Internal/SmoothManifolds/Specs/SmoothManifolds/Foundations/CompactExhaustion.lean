import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Topology

/-! Independent statements for the compact-exhaustion conclusion and the complete
basic-topology proposition M01.01 (paper.tex, lines 74–81).
The sequence is indexed by naturals, with the covering assertion using j ≥ 1,
as in the manuscript. No compactness or nonemptiness of the manifold is assumed. -/

namespace Specs.SmoothManifolds.Foundations.CompactExhaustion

open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
universe u

def exists_compact_exhaustionType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M],
    TopologicalManifold n kind M →
      ∃ K : ℕ → Set M,
        (∀ j, IsCompact (K j)) ∧
        (∀ j, K j ⊆ interior (K (j + 1))) ∧
        (⋃ (j : ℕ) (_ : 1 ≤ j), interior (K j)) = Set.univ

/-- The full conclusion, including the local topology and components supplied
by the preceding goal, for either model and every dimension. -/
def basic_topologyType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (A : TopologicalManifold n kind M),
    LocallyCompactSpace M ∧ LocallyPathConnectedSpace M ∧
    (∃ C : Set (ModelChart n kind M), C.Countable ∧ C ⊆ A.atlas ∧
      ∀ p : M, ∃ c ∈ C, p ∈ c.source) ∧
    ParacompactSpace M ∧
    (∃ K : ℕ → Set M,
      (∀ j, IsCompact (K j)) ∧
      (∀ j, K j ⊆ interior (K (j + 1))) ∧
      (⋃ (j : ℕ) (_ : 1 ≤ j), interior (K j)) = Set.univ) ∧
    (∀ p : M, IsOpen (connectedComponent p) ∧
      IsPathConnected (connectedComponent p)) ∧
    (Set.range (connectedComponent (α := M))).Countable

end Specs.SmoothManifolds.Foundations.CompactExhaustion
