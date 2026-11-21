import MathGenome.Internal.Specs.D07.Ch06.SimpleGroupsBoundaryAlternatingSimplicity
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
Independent statements for `K07.06.simple_groups_boundary`, paper.tex:1103–1131.
`IsSimpleGroup` includes nontriviality. Commutativity in the classification is
a conclusion/premise expressed on the original group operation, rather than
an extra structural assumption on every group considered. Finite groups include
the trivial group. The alternating groups are the canonical sign kernels from
the chapter-two interface; the four-letter boundary is stated for every finite
carrier of cardinality four.
-/

namespace Specs.D07.Ch06.SimpleGroupsBoundary

universe u

def SimpleGroupCharacterization : Prop :=
  ∀ (G : Type u) [Group G], IsSimpleGroup G ↔
    Nontrivial G ∧ ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤

def TrivialNotSimple : Prop :=
  ∀ (G : Type u) [Group G] [Subsingleton G], ¬ IsSimpleGroup G

def FiniteSimpleAbelianClassification : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    (IsSimpleGroup G ∧ ∀ x y : G, x * y = y * x) ↔
      IsCyclic G ∧ (Nat.card G).Prime

def PrimeOrderSimple : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ),
    p.Prime → Nat.card G = p → IsSimpleGroup G

def AlternatingSimple : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (n : ℕ), Nat.card X = n → 5 ≤ n →
    IsSimpleGroup (alternatingGroup X)

def AlternatingNonabelian : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (n : ℕ), Nat.card X = n → 5 ≤ n →
    ∃ σ τ : alternatingGroup X, σ * τ ≠ τ * σ

/-- The Klein four subgroup witnesses the failure of simplicity at four letters. -/
def AlternatingFourNormalWitness : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X], Nat.card X = 4 →
    ∃ V : Subgroup (alternatingGroup X),
      V.Normal ∧ V ≠ ⊥ ∧ V ≠ ⊤ ∧ Nat.card V = 4

def AlternatingFourNotSimple : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X], Nat.card X = 4 →
    ¬ IsSimpleGroup (alternatingGroup X)

end Specs.D07.Ch06.SimpleGroupsBoundary
