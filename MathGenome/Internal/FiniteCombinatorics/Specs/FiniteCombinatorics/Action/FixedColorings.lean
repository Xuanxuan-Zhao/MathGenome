import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.CycleIndex
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Data.Fintype.Pi

/-! Independent specification of the fixed-coloring assertion in paper.tex W32.
The orbit enumeration itself is allocated to the subsequent Pólya goal. -/
namespace FiniteCombinatorics.FixedColoringsSpec
open scoped BigOperators
universe u v w
variable (G : Type u) (X : Type v) (C : Type w) [Group G] [MulAction G X]

/-- Precomposition by the inverse action on positions. -/
@[instance_reducible] def coloringAction : MulAction G (X → C) := arrowAction
attribute [local instance] coloringAction

def fixedColorings (g : G) := {f : X → C // g • f = f}

variable [Fintype X]
/-- Constancy on each complete cycle, including cycles of length one. -/
def constantOnCycles (g : G) (f : X → C) : Prop :=
  ∀ D ∈ CycleIndexSpec.cycles G X g, ∀ x ∈ D, ∀ y ∈ D, f x = f y

def coloringActionType := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X], MulAction G (X → C)
def fixedColoringsType := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X], G → Type (max v w)
def constantOnCyclesType := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] [Fintype X], G → (X → C) → Prop

def ActionApply : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] (g : G) (f : X → C) (x : X),
  letI := coloringAction G X C
  (g • f) x = f (g⁻¹ • x)

def FixedIffConstant : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] [Fintype X] (g : G) (f : X → C),
  letI := coloringAction G X C
  g • f = f ↔ constantOnCycles G X C g f

/-- The equivalence assigns a fixed coloring its common color on each cycle. -/
def CycleBijection : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] [Fintype X] (g : G),
  ∃ e : fixedColorings G X C g ≃ (↥(CycleIndexSpec.cycles G X g) → C),
    ∀ (f : fixedColorings G X C g) (D : ↥(CycleIndexSpec.cycles G X g))
      (x : X), x ∈ D.val → e f D = f.val x

def FixedCount : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] [Fintype X] [Fintype C] (g : G),
  Nat.card (fixedColorings G X C g) =
    Fintype.card C ^ (∑ k ∈ Finset.Icc 1 (Fintype.card X), CycleIndexSpec.countCycles G X g k)

def EmptyPositions : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] [Fintype X] [IsEmpty X] (g : G),
  Nat.card (fixedColorings G X C g) = 1

def EmptyColors : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] [Fintype X] [Nonempty X] [IsEmpty C] (g : G),
  IsEmpty (fixedColorings G X C g)

end FiniteCombinatorics.FixedColoringsSpec
