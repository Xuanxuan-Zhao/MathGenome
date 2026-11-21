import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Foundation
import Mathlib.Combinatorics.Matroid.Circuit

/-! Independent statements for the forward directions of W64 and W65–W66.
All ranks are the canonical integer-valued finite ranks. Every recovery statement
includes the ground condition, so it also handles ambient sets outside the ground.
No nonempty ground or positive rank is assumed. -/
namespace FiniteCombinatorics.Matroid.Expected
open Set
universe u

def basisExtension : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (I A : Set α),
    M.Indep I → I ⊆ A → A ⊆ M.E → ∃ B, M.IsBasis B A ∧ I ⊆ B

def basisCardinality : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (B A : Set α),
    M.IsBasis B A → (B.ncard : ℤ) = rank M A

def basesPresentation : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite],
    BasisPresentation M.E {B | M.IsBase B}

def rankEmpty : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite], rank M ∅ = 0

def rankBounds : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (A : Set α),
    A ⊆ M.E → 0 ≤ rank M A ∧ rank M A ≤ (A.ncard : ℤ)

def rankMonotone : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (A B : Set α),
    A ⊆ B → B ⊆ M.E → rank M A ≤ rank M B

def rankIncrements : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (A : Set α),
    A ⊆ M.E → ∀ e ∈ M.E,
      0 ≤ rank M (insert e A) - rank M A ∧ rank M (insert e A) - rank M A ≤ 1

def rankSubmodular : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (A B : Set α),
    A ⊆ M.E → B ⊆ M.E →
      rank M (A ∪ B) + rank M (A ∩ B) ≤ rank M A + rank M B

def rankDiminishing : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (A B : Set α),
    A ⊆ B → B ⊆ M.E → ∀ e ∈ M.E,
      rank M (insert e B) - rank M B ≤ rank M (insert e A) - rank M A

def rankNoIncrement : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (A B : Set α),
    A ⊆ B → B ⊆ M.E → ∀ e ∈ M.E,
      rank M (insert e A) = rank M A → rank M (insert e B) = rank M B

def rankPresentation : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite], RankPresentation M.E (rank M)

def circuitMinimal : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (C : Set α),
    M.IsCircuit C ↔ C ⊆ M.E ∧ ¬ M.Indep C ∧
      ∀ D, D ⊂ C → M.Indep D

def circuitsPresentation : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite],
    CircuitPresentation M.E {C | M.IsCircuit C}

def closurePresentation : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite],
    ClosurePresentation M.E M.closure

def closureRank : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (A : Set α),
    A ⊆ M.E → ∀ e ∈ M.E,
      e ∈ M.closure A ↔ rank M (insert e A) = rank M A

def basisRecovery : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (I : Set α),
    BasisIndependent M.E {B | M.IsBase B} I ↔ M.Indep I

def rankRecovery : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (I : Set α),
    RankIndependent M.E (rank M) I ↔ M.Indep I

def circuitRecovery : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (I : Set α),
    CircuitIndependent M.E {C | M.IsCircuit C} I ↔ M.Indep I

def closureRecovery : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (I : Set α),
    ClosureIndependent M.E M.closure I ↔ M.Indep I

end FiniteCombinatorics.Matroid.Expected
