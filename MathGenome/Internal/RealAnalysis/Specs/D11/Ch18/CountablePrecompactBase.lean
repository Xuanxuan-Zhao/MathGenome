import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Hausdorff

/-!
Independent statements for the topology stage of
`paper.tex`, Theorem `d11:18:baire-borel-second-countable`.
Precompact means that the closure in the ambient space is compact.
No nonemptiness assumption is imposed on the space or on any set.
-/

open Set TopologicalSpace

universe u

namespace Specs.D11.Ch18

/-- A countable topological base of open sets with compact closure. -/
def CountablePrecompactBase : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X],
    ∃ B : Set (Set X), B.Countable ∧ IsTopologicalBasis B ∧
      ∀ V ∈ B, IsOpen V ∧ IsCompact (closure V)

/-- Each open set is exactly the union of a sequence of compact subsets of itself.
Empty and finite covers can be padded with empty compact sets. -/
def OpenCompactCover : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (U : Set X), IsOpen U →
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n) ∧ K n ⊆ U) ∧ U = ⋃ n, K n

/-- Each compact set is exactly a countable intersection of ambient open sets.
The same assertion includes the empty compact set. -/
def CompactOpenIntersection : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : Set X), IsCompact K →
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ K = ⋂ n, U n

end Specs.D11.Ch18
