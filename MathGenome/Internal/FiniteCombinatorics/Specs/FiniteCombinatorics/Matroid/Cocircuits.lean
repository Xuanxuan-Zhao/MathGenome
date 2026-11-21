import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Duality
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ForwardPresentations
import Mathlib.Combinatorics.Matroid.Loop

/-! Independent statements for the cocircuit paragraph of W68 (paper.tex).
Complements are relative to the canonical ground. Minimality and maximality
are by inclusion. No ground, basis, or rank is assumed nonempty or positive. -/

namespace FiniteCombinatorics.Matroid.Expected
open Set
open scoped _root_.Matroid
universe u
variable {α : Type u}

def Loop (M : _root_.Matroid α) (e : α) : Prop := M.IsCircuit {e}

def Coloop (M : _root_.Matroid α) (e : α) : Prop :=
  ∀ B, M.IsBase B → e ∈ B

def Cocircuit (M : _root_.Matroid α) (C : Set α) : Prop := M✶.IsCircuit C

def MeetsEveryBasis (M : _root_.Matroid α) (C : Set α) : Prop :=
  ∀ B, M.IsBase B → (C ∩ B).Nonempty

def MinimalBasisHitting (M : _root_.Matroid α) (C : Set α) : Prop :=
  C ⊆ M.E ∧ MeetsEveryBasis M C ∧
    ∀ D, D ⊂ C → ¬ MeetsEveryBasis M D

def MaximalNonspanning (M : _root_.Matroid α) (H : Set α) : Prop :=
  H ⊆ M.E ∧ ¬ M.Spanning H ∧
    ∀ A, H ⊂ A → A ⊆ M.E → M.Spanning A

def LoopType := ∀ {α : Type u}, _root_.Matroid α → α → Prop
def ColoopType := ∀ {α : Type u}, _root_.Matroid α → α → Prop
def CocircuitType := ∀ {α : Type u}, _root_.Matroid α → Set α → Prop
def MeetsEveryBasisType := ∀ {α : Type u}, _root_.Matroid α → Set α → Prop
def MinimalBasisHittingType := ∀ {α : Type u}, _root_.Matroid α → Set α → Prop
def MaximalNonspanningType := ∀ {α : Type u}, _root_.Matroid α → Set α → Prop

def loopIffIsLoop : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (e : α),
    Loop M e ↔ M.IsLoop e

def coloopIffIsColoop : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (e : α),
    Coloop M e ↔ M.IsColoop e

def cocircuitMinimalHitting : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C : Set α),
    Cocircuit M C ↔ MinimalBasisHitting M C

/-- Nonspanning means precisely that the subset contains no primal basis. -/
def spanningContainsBasis : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (A : Set α),
    A ⊆ M.E → (M.Spanning A ↔ ∃ B, M.IsBase B ∧ B ⊆ A)

def hittingComplementNonspanning : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C : Set α),
    C ⊆ M.E →
      (MeetsEveryBasis M C ↔ ¬ M.Spanning (relativeCompl M.E C))

/-- The explicit support condition prevents off-ground sets from acquiring
the same characterization merely because their relative complements agree. -/
def cocircuitComplementMaximal : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C : Set α),
    Cocircuit M C ↔ C ⊆ M.E ∧ MaximalNonspanning M (relativeCompl M.E C)

def cocircuitComplementExists : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C : Set α),
    Cocircuit M C ↔
      ∃ H, MaximalNonspanning M H ∧ C = relativeCompl M.E H

def coloopDualLoop : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (e : α),
    Coloop M e ↔ Loop M✶ e

def emptyBaseNoHitting : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite],
    M.IsBase ∅ → ∀ C, ¬ MeetsEveryBasis M C

def emptyBaseNoCocircuit : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite],
    M.IsBase ∅ → ∀ C, ¬ Cocircuit M C

def emptyGroundNoCocircuit : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite],
    M.E = ∅ → ∀ C, ¬ Cocircuit M C

end FiniteCombinatorics.Matroid.Expected
