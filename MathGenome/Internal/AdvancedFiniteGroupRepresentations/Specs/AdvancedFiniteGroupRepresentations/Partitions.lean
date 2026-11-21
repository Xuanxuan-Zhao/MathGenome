import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.GroupTheory.Perm.Basic

/-! Canonical interfaces for FR, Scope and conventions and Chapter 1.
Rows/columns and labels use `Fin n` and zero-based coordinates internally.
`cellOneBased` translates exactly to the printed positive coordinates.
The ordered list model is identified with the library partition and diagram models.
-/
open scoped BigOperators
universe u

namespace Specs.AdvancedFiniteGroupRepresentations

abbrev SymmetricGroup : ℕ → Type :=
  fun n => Equiv.Perm (Fin n)

def SymmetricGroupType := ℕ → Type

abbrev GroupAlgebra : ℕ → Type :=
  fun n => MonoidAlgebra ℂ (SymmetricGroup n)

def GroupAlgebraType := ℕ → Type

abbrev Partition : ℕ → Type :=
  Nat.Partition

def PartitionType := ℕ → Type

def diagram : {n : ℕ} → Partition n → YoungDiagram :=
  fun p => YoungDiagram.ofPartition p

def diagramType := {n : ℕ} → Partition n → YoungDiagram

def diagramEquiv : (n : ℕ) → Partition n ≃ {d : YoungDiagram // d.card = n} :=
  fun _ => YoungDiagram.equivPartition.symm

def diagramEquivType := (n : ℕ) → Partition n ≃ {d : YoungDiagram // d.card = n}

def parts : {n : ℕ} → Partition n → List ℕ :=
  fun p => (diagram p).rowLens

def partsType := {n : ℕ} → Partition n → List ℕ

abbrev OrderedParts : ℕ → Type :=
  fun n => {w : List ℕ // w.SortedGE ∧ (∀ x ∈ w, 0 < x) ∧ w.sum = n}

def OrderedPartsType := ℕ → Type

def cells : {n : ℕ} → Partition n → Finset (ℕ × ℕ) :=
  fun p => (diagram p).cells

def cellsType := {n : ℕ} → Partition n → Finset (ℕ × ℕ)

abbrev Cell : {n : ℕ} → Partition n → Type :=
  fun p => {c : ℕ × ℕ // c ∈ cells p}

def CellType := {n : ℕ} → Partition n → Type

def rowLength : {n : ℕ} → Partition n → ℕ → ℕ :=
  fun p => (diagram p).rowLen

def rowLengthType := {n : ℕ} → Partition n → ℕ → ℕ

def columnLength : {n : ℕ} → Partition n → ℕ → ℕ :=
  fun p => (diagram p).colLen

def columnLengthType := {n : ℕ} → Partition n → ℕ → ℕ

def length : {n : ℕ} → Partition n → ℕ :=
  fun p => (parts p).length

def lengthType := {n : ℕ} → Partition n → ℕ

def transpose : {n : ℕ} → Partition n → Partition n :=
  Nat.Partition.conjugate

def transposeType := {n : ℕ} → Partition n → Partition n

def dominates : {n : ℕ} → Partition n → Partition n → Prop :=
  fun p μ => ∀ k, (∑ i ∈ Finset.range k, rowLength μ i) ≤ ∑ i ∈ Finset.range k, rowLength p i

def dominatesType := {n : ℕ} → Partition n → Partition n → Prop

def emptyPartition : Partition 0 :=
  default

def emptyPartitionType := Partition 0

def cellOneBased : {n : ℕ} → Partition n → ℕ → ℕ → Prop :=
  fun p i j => 0 < i ∧ 0 < j ∧ (i - 1, j - 1) ∈ cells p

def cellOneBasedType := {n : ℕ} → Partition n → ℕ → ℕ → Prop

def relabel : {n : ℕ} → {α : Type u} → SymmetricGroup n → (α → Fin n) → α → Fin n :=
  fun σ t a => σ (t a)

def relabelType := {n : ℕ} → {α : Type u} → SymmetricGroup n → (α → Fin n) → α → Fin n

def relabelLabeling : {n : ℕ} → {α : Type u} → SymmetricGroup n → (α ≃ Fin n) → (α ≃ Fin n) :=
  fun σ t => t.trans σ

def relabelLabelingType := {n : ℕ} → {α : Type u} → SymmetricGroup n → (α ≃ Fin n) → (α ≃ Fin n)

def parts_sortedType : Prop :=
  ∀ {n} (p : Partition n), (parts p).SortedGE

def parts_positiveType : Prop :=
  ∀ {n} (p : Partition n) (x : ℕ), x ∈ parts p → 0 < x

def parts_sumType : Prop :=
  ∀ {n} (p : Partition n), (parts p).sum = n

def diagram_cardType : Prop :=
  ∀ {n} (p : Partition n), (diagram p).card = n

def diagramEquiv_applyType : Prop :=
  ∀ {n} (p : Partition n), (diagramEquiv n p).val = diagram p

def orderedParts_equivalenceType : Prop :=
  ∀ n, ∃ e : Partition n ≃ OrderedParts n, ∀ p, (e p).val = parts p

def parts_eq_sorted_multisetType : Prop :=
  ∀ {n} (p : Partition n), parts p = p.parts.sort (· ≥ ·)

def rowLength_eq_getDType : Prop :=
  ∀ {n} (p : Partition n) (i : ℕ), rowLength p i = (parts p)[i]?.getD 0

def rowLength_antitoneType : Prop :=
  ∀ {n} (p : Partition n), Antitone (rowLength p)

def rowLength_zero_of_length_leType : Prop :=
  ∀ {n} (p : Partition n) (i : ℕ), length p ≤ i → rowLength p i = 0

def length_eq_columnLength_zeroType : Prop :=
  ∀ {n} (p : Partition n), length p = columnLength p 0

def cell_iffType : Prop :=
  ∀ {n} (p : Partition n) (i j : ℕ), (i,j) ∈ cells p ↔ j < rowLength p i

def cell_iff_columnType : Prop :=
  ∀ {n} (p : Partition n) (i j : ℕ), (i,j) ∈ cells p ↔ i < columnLength p j

def cellOneBased_iffType : Prop :=
  ∀ {n} (p : Partition n) (i j : ℕ), cellOneBased p i j ↔ 0 < i ∧ 0 < j ∧ j ≤ rowLength p (i-1)

def transpose_diagramType : Prop :=
  ∀ {n} (p : Partition n), diagram (transpose p) = (diagram p).transpose

def transpose_columnLengthType : Prop :=
  ∀ {n} (p : Partition n) (i : ℕ), columnLength (transpose p) i = rowLength p i

def transpose_rowLengthType : Prop :=
  ∀ {n} (p : Partition n) (j : ℕ), rowLength (transpose p) j = columnLength p j

def transpose_involutiveType : Prop :=
  ∀ {n} (p : Partition n), transpose (transpose p) = p

def dominance_antisymmType : Prop :=
  ∀ {n} (p μ : Partition n), dominates p μ → dominates μ p → p = μ

def dominance_reflType : Prop :=
  ∀ {n} (p : Partition n), dominates p p

def dominance_transType : Prop :=
  ∀ {n} (p μ ν : Partition n), dominates p μ → dominates μ ν → dominates p ν

def zero_partition_uniqueType : Prop :=
  ∀ p : Partition 0, p = emptyPartition

def empty_partsType : Prop :=
  parts emptyPartition = []

def empty_cellsType : Prop :=
  cells emptyPartition = ∅

def empty_lengthType : Prop :=
  length emptyPartition = 0

def empty_transposeType : Prop :=
  transpose emptyPartition = emptyPartition

def zero_labels_trivialType : Prop :=
  ∀ σ : SymmetricGroup 0, σ = 1

def permutation_mul_applyType : Prop :=
  ∀ {n} (σ τ : SymmetricGroup n) (i : Fin n), (σ * τ) i = σ (τ i)

def relabel_oneType : Prop :=
  ∀ {n} {α : Type u} (t : α → Fin n), relabel (1 : SymmetricGroup n) t = t

def relabel_mulType : Prop :=
  ∀ {n} {α : Type u} (σ τ : SymmetricGroup n) (t : α → Fin n), relabel (σ * τ) t = relabel σ (relabel τ t)

def relabelLabeling_applyType : Prop :=
  ∀ {n} {α : Type u} (σ : SymmetricGroup n) (t : α ≃ Fin n) (a : α), relabelLabeling σ t a = σ (t a)

end Specs.AdvancedFiniteGroupRepresentations
