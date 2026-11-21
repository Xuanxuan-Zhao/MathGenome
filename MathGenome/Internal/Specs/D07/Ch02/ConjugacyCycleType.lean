import MathGenome.Internal.Specs.D07.Ch02.CycleDecomposition
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
Independent specification of `K07.02.conjugacy_cycle_type`
(paper.tex:551–561). The ambient finite set may be empty. Conjugacy is
in its full permutation group, with rightmost-first composition.
The bridge to written decompositions identifies Mathlib's cycle type
with the multiset of lengths of precisely the nontrivial listed cycles.
-/

namespace Specs.D07.Ch02.ConjugacyCycleType

universe u

/-- Lengths of nontrivial cycles; fixed points contribute no entries. -/
noncomputable def cycleLengths {X : Type u} [Finite X] (σ : Equiv.Perm X) : Multiset ℕ := by
  classical
  letI := Fintype.ofFinite X
  exact σ.cycleType

/-- This cycle type agrees with every accepted written disjoint-cycle decomposition. -/
def DecompositionCycleLengths : Prop :=
  ∀ (X : Type u) [Finite X] (σ : Equiv.Perm X) (L : List (List X)),
    CycleDecomposition.Decomposition σ L →
      cycleLengths σ = (L.map List.length : Multiset ℕ)

/-- The complete conjugacy criterion on the same finite ambient set. -/
def ConjugacyIffCycleLengths : Prop :=
  ∀ (X : Type u) [Finite X] (σ τ : Equiv.Perm X),
    (∃ b : Equiv.Perm X, b * σ * b⁻¹ = τ) ↔ cycleLengths σ = cycleLengths τ

/-- Relabelling a written cycle requires no finiteness of the ambient set. -/
def ConjugateListedCycle : Prop :=
  ∀ (X : Type u) (b : Equiv.Perm X) (l : List X) (hl : l.Nodup),
    b * PermutationConvention.cycleConstructorValue X l hl * b⁻¹ =
      PermutationConvention.cycleConstructorValue X (l.map b) (hl.map b.injective)

end Specs.D07.Ch02.ConjugacyCycleType
