import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.SubspacesExhaustion
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.CompactShrinking

/-!
Subspaces and exhaustions (paper.tex, d10:11:exhaustion).
The closed-subspace assertion uses weak local compactness, so requires no
Hausdorff hypothesis. For open subspaces, the upstream LCH bridge permits
using arbitrarily small compact neighborhoods.

Mathlib's compact exhaustion has the exact compactness, interior nesting,
and covering properties required here. Its construction starts with the
empty set and uses finite compact-neighborhood covers, so includes empty X
and empty covering members. We pass to its positive-indexed tail explicitly.
-/

open Set
universe u

namespace D10Topology.Ch11

theorem closed_subspace_locallyCompact {X : Type u} [TopologicalSpace X]
    (hX : LocallyCompact X) (A : Set X) (hA : IsClosed A) :
    LocallyCompact A := by
  let : WeaklyLocallyCompactSpace X :=
    (locallyCompact_iff_weaklyLocallyCompactSpace X).mp hX
  exact (locallyCompact_iff_weaklyLocallyCompactSpace A).mpr
    hA.weaklyLocallyCompactSpace

theorem open_subspace_lch {X : Type u} [TopologicalSpace X]
    (hX : LCH X) (A : Set X) (hA : IsOpen A) : LCH A := by
  let : T2Space X := hX.2
  let : LocallyCompactSpace X := (locallyCompact_iff_locallyCompactSpace X).mp hX.1
  exact ⟨locallyCompact_of_mathlib_locallyCompactSpace A hA.locallyCompactSpace,
    inferInstance⟩

theorem sigmaCompact_iff_exhaustion (X : Type u) [TopologicalSpace X]
    (hX : LCH X) :
    SigmaCompact X ↔ ∃ K : ℕ → Set X,
      (∀ n, IsCompact (K (n + 1))) ∧
      (∀ n, K (n + 1) ⊆ interior (K (n + 2))) ∧
      (⋃ n, K (n + 1)) = univ := by
  constructor
  · intro h
    let : WeaklyLocallyCompactSpace X :=
      (locallyCompact_iff_weaklyLocallyCompactSpace X).mp hX.1
    let : SigmaCompactSpace X := (sigmaCompact_iff_sigmaCompactSpace X).mp h
    let E := CompactExhaustion.choice X
    refine ⟨E, (fun n => E.isCompact (n + 1)),
      (fun n => E.subset_interior_succ (n + 1)), ?_⟩
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨n, hn⟩ := E.exists_mem x
    exact ⟨n, E.subset_succ n hn⟩
  · rintro ⟨K, hK, _, hcover⟩
    exact (sigmaCompact_iff_sequence X).mpr ⟨fun n => K (n + 1), hK, hcover⟩

theorem exhaustion_contains_compact {X : Type u} [TopologicalSpace X]
    (K : ℕ → Set X) (hK : ∀ n, IsCompact (K (n + 1)))
    (hstep : ∀ n, K (n + 1) ⊆ interior (K (n + 2)))
    (hcover : (⋃ n, K (n + 1)) = univ) (C : Set X) (hC : IsCompact C) :
    ∃ n : ℕ, 1 ≤ n ∧ C ⊆ K n := by
  let E : CompactExhaustion X := ⟨fun n => K (n + 1), hK, hstep, hcover⟩
  obtain ⟨n, hn⟩ := E.exists_superset_of_isCompact hC
  exact ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), hn⟩

end D10Topology.Ch11
