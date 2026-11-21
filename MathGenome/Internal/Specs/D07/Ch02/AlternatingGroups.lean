import MathGenome.Internal.Specs.D07.Ch01.KernelImage
import MathGenome.Internal.Specs.D07.Ch02.SymmetricOrder
import MathGenome.Internal.Specs.D07.Ch02.TranspositionsParity
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
Independent specification of `K07.02.alternating_groups`, paper.tex:539–555.
The canonical alternating subgroup uses the accepted integer-unit-valued sign.
All carriers here are finite, as required for that sign; empty carriers are allowed.
Three-cycles in the generation statement are the accepted written cycles of
exactly three distinct entries, with rightmost-first permutation composition.
-/

namespace Specs.D07.Ch02.AlternatingGroups

universe u

/-- Evenness means sign one, with the very same sign as the upstream entry. -/
def EvenPermutations : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (σ : Equiv.Perm X),
    σ ∈ alternatingGroup X ↔ TranspositionsParity.signValue X σ = 1

def KernelIdentity : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X],
    alternatingGroup X = (TranspositionsParity.signValue X).ker

/-- Normality has no lower bound on the finite cardinality. -/
def NormalSubgroup : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X], (alternatingGroup X).Normal

def IndexTwo : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (n : ℕ), Nat.card X = n → 2 ≤ n →
    (alternatingGroup X).index = 2

/-- Natural-number division is used only in the stated range n ≥ 2. -/
def AlternatingOrder : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (n : ℕ), Nat.card X = n → 2 ≤ n →
    Nat.card (alternatingGroup X) = n.factorial / 2

/-- Relate the library three-cycle predicate to the accepted cycle constructor. -/
def ThreeCycleListing : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (σ : Equiv.Perm X),
    σ.IsThreeCycle ↔ ∃ (l : List X) (h : l.Nodup), l.length = 3 ∧
      PermutationConvention.cycleConstructorValue X l h = σ

def ThreeCyclesEven : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (l : List X) (h : l.Nodup), l.length = 3 →
    PermutationConvention.cycleConstructorValue X l h ∈ alternatingGroup X

/-- Subgroup closure expresses generation, including the identity/empty word. -/
def ThreeCycleGeneration : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (n : ℕ), Nat.card X = n → 3 ≤ n →
    Subgroup.closure {σ : Equiv.Perm X | ∃ (l : List X) (h : l.Nodup),
      l.length = 3 ∧ PermutationConvention.cycleConstructorValue X l h = σ} =
        alternatingGroup X

/-- This is exactly the two finite cases n = 0 and n = 1. -/
def SmallAlternatingGroup : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X], Nat.card X ≤ 1 →
    alternatingGroup X = ⊥ ∧ Nat.card (alternatingGroup X) = 1

end Specs.D07.Ch02.AlternatingGroups
