import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions

/-!
Independent statements of paper.tex, d10:11:exhaustion.
Subtypes carry their induced topology. Local compactness is the source's
one-compact-neighborhood predicate, without any separation axiom.

For the exhaustion statements, `K (n + 1)` indexes precisely the positive
integers. `K 0` is unused and unrestricted. All interiors are ambient in X.
Empty spaces, empty compact members, and empty compact subsets are allowed.
-/

open Set
universe u

namespace Specs.D10Topology.Ch11.SubspacesExhaustion

open Specs.D10Topology.Ch11.LocalCompactConventions

def closed_subspace_locallyCompact : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LocallyCompact X →
    ∀ A : Set X, IsClosed A → LocallyCompact A

def open_subspace_lch : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LCH X →
    ∀ A : Set X, IsOpen A → LCH A

def sigmaCompact_iff_exhaustion : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], LCH X →
    (SigmaCompact X ↔ ∃ K : ℕ → Set X,
      (∀ n, IsCompact (K (n + 1))) ∧
      (∀ n, K (n + 1) ⊆ interior (K (n + 2))) ∧
      (⋃ n, K (n + 1)) = univ)

/-- The containment conclusion holds for every exhaustion with the stated
properties; no separation or local compactness is needed for this implication. -/
def exhaustion_contains_compact : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (K : ℕ → Set X),
    (∀ n, IsCompact (K (n + 1))) →
    (∀ n, K (n + 1) ⊆ interior (K (n + 2))) →
    (⋃ n, K (n + 1)) = univ →
    ∀ C : Set X, IsCompact C → ∃ n : ℕ, 1 ≤ n ∧ C ⊆ K n

end Specs.D10Topology.Ch11.SubspacesExhaustion
