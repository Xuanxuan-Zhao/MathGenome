import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Algebra.Ring.Real

/-!
Independent statements of paper.tex, d10:15:compact-atlas-embedding.
Euclidean coordinates use finite products of the usual real line. In the
finite-atlas theorem O may be any subspace, with no openness assumption.
Neither dimension nor the number of charts is required to be positive.
The second statement spells out local Euclidean charts of a topological
n-manifold; compactness and Hausdorffness are the only global assumptions.
-/

open Set Topology
universe u

namespace Specs.D10Topology.Ch15.CompactAtlasEmbedding

def compact_finite_atlas_embedding : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (k n : ℕ) (U : Fin k → Set X) (O : Fin k → Set (Fin n → ℝ)),
    (∀ i, IsOpen (U i)) → (∀ x, ∃ i, x ∈ U i) →
    (∀ i, U i ≃ₜ O i) →
    ∃ F : X → Fin (k * (n + 1)) → ℝ, IsEmbedding F

def compact_manifold_embedding : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ),
    (∀ x : X, ∃ U : Set X, ∃ O : Set (Fin n → ℝ),
      IsOpen U ∧ IsOpen O ∧ x ∈ U ∧ Nonempty (U ≃ₜ O)) →
    ∃ m : ℕ, ∃ F : X → Fin m → ℝ, IsEmbedding F

end Specs.D10Topology.Ch15.CompactAtlasEmbedding
