import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.MurnaghanNakayama
import Mathlib.LinearAlgebra.Matrix.Notation

/-! The unnumbered S₄ example, source lines 1204–1226.
Rows and columns below are actual partitions and actual inherited Specht traces. -/
noncomputable section
open scoped BigOperators
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Specht labels, in the printed order. -/
def s4Shapes : Fin 5 → Partition 4 := ![
  ⟨{4}, by simp, by simp⟩,
  ⟨{3, 1}, by simp, by simp⟩,
  ⟨{2, 2}, by simp, by simp⟩,
  ⟨{2, 1, 1}, by simp, by simp⟩,
  ⟨{1, 1, 1, 1}, by simp, by simp⟩]

/-- Cycle types include every singleton cycle. -/
def s4Cycles : Fin 5 → Partition 4 := ![
  s4Shapes 4, s4Shapes 3, s4Shapes 2, s4Shapes 1, s4Shapes 0]

def s4ClassSizes : Fin 5 → ℕ := ![1, 6, 3, 8, 6]
def s4Centralizers : Fin 5 → ℕ := ![24, 4, 8, 3, 4]

def s4Table : Matrix (Fin 5) (Fin 5) ℤ := !![
  1, 1, 1, 1, 1;
  3, 1, -1, 0, -1;
  2, 0, 2, -1, 0;
  3, -1, -1, 0, 1;
  1, -1, 1, 1, -1]

def s4Character (i j : Fin 5) : ℂ := spechtCharacterAtCycle (s4Shapes i) (s4Cycles j)

def s4ShapesType := Fin 5 → Partition 4
def s4CyclesType := Fin 5 → Partition 4
def s4ClassSizesType := Fin 5 → ℕ
def s4CentralizersType := Fin 5 → ℕ
def s4TableType := Matrix (Fin 5) (Fin 5) ℤ
def s4CharacterType := Fin 5 → Fin 5 → ℂ

def s4_shapes_bijectiveType : Prop := Function.Bijective s4Shapes
def s4_cycles_bijectiveType : Prop := Function.Bijective s4Cycles

def s4_labelsType : Prop :=
  (∀ i, parts (s4Shapes i) = ![[4], [3, 1], [2, 2], [2, 1, 1], [1, 1, 1, 1]] i) ∧
  (∀ j, parts (s4Cycles j) = ![[1, 1, 1, 1], [2, 1, 1], [2, 2], [3, 1], [4]] j)

def s4_character_tableType : Prop := ∀ i j, s4Character i j = (s4Table i j : ℂ)

def s4_class_cardinalitiesType : Prop :=
  ∀ j (g : SymmetricGroup 4), cyclePartition g = s4Cycles j →
    Nat.card {h : SymmetricGroup 4 // IsConj g h} = s4ClassSizes j ∧
    Nat.card (Subgroup.centralizer ({g} : Set (SymmetricGroup 4))) = s4Centralizers j

/-- The Hermitian convention is linear in the first variable, as in the source. -/
def s4_row_gramType : Prop := ∀ i k : Fin 5,
  (∑ j, (s4ClassSizes j : ℂ) * s4Character i j * star (s4Character k j)) =
    if i = k then 24 else 0

/-- This includes both the squared norms and orthogonality of distinct columns. -/
def s4_column_gramType : Prop := ∀ j k : Fin 5,
  (∑ i, s4Character i j * star (s4Character i k)) =
    if j = k then (s4Centralizers j : ℂ) else 0

end Specs.AdvancedFiniteGroupRepresentations
