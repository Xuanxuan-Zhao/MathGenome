import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.Tabloids
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fin.SuccPred

/-! FR, Chapter 2, definitions at lines 464–469, 581–587 and 738–744.
Cells and labels are zero based, using the upstream canonical objects.
Deletion and insertion are required to leave a lower set, i.e. a Young diagram.
The formula with one-based coordinates is explicitly recorded below. -/
noncomputable section
namespace Specs.AdvancedFiniteGroupRepresentations

def RowIncreasing : {n : ℕ} → {p : Partition n} → Tableau p → Prop :=
  fun t => ∀ a b : Cell _, a.val.1 = b.val.1 → a.val.2 < b.val.2 → t a < t b

def RowIncreasingType := {n : ℕ} → {p : Partition n} → Tableau p → Prop

def ColumnIncreasing : {n : ℕ} → {p : Partition n} → Tableau p → Prop :=
  fun t => ∀ a b : Cell _, a.val.2 = b.val.2 → a.val.1 < b.val.1 → t a < t b

def ColumnIncreasingType := {n : ℕ} → {p : Partition n} → Tableau p → Prop

def IsStandard : {n : ℕ} → {p : Partition n} → Tableau p → Prop :=
  fun t => RowIncreasing t ∧ ColumnIncreasing t

def IsStandardType := {n : ℕ} → {p : Partition n} → Tableau p → Prop

def StandardTableau : {n : ℕ} → Partition n → Type :=
  fun p => {t : Tableau p // IsStandard t}

def StandardTableauType := {n : ℕ} → Partition n → Type

def standardTableauCount : {n : ℕ} → Partition n → ℕ :=
  fun p => Nat.card (StandardTableau p)

def standardTableauCountType := {n : ℕ} → Partition n → ℕ

def IsRemovable : {n : ℕ} → Partition n → (ℕ × ℕ) → Prop :=
  fun p c => c ∈ cells p ∧ IsLowerSet (↑((cells p).erase c) : Set (ℕ × ℕ))

def IsRemovableType := {n : ℕ} → Partition n → (ℕ × ℕ) → Prop

def RemovableCell : {n : ℕ} → Partition n → Type :=
  fun p => {c : ℕ × ℕ // IsRemovable p c}

def RemovableCellType := {n : ℕ} → Partition n → Type

def deletedDiagram : ∀ {n} (p : Partition n) (_c : RemovableCell p), YoungDiagram :=
  fun p c => ⟨(cells p).erase c.val, c.property.2⟩

def deletedDiagramType := ∀ {n} (p : Partition n) (_c : RemovableCell p), YoungDiagram

def deleteCell : ∀ {n} (p : Partition n), RemovableCell p → Partition (n - 1) :=
  fun {n} p c => (deletedDiagram p c).toPartition (by
    change ((cells p).erase c.val).card = n - 1
    rw [Finset.card_erase_of_mem c.property.1]
    exact congrArg (· - 1) (YoungDiagram.card_ofPartition p))

def deleteCellType := ∀ {n} (p : Partition n), RemovableCell p → Partition (n - 1)

def IsAddable : {n : ℕ} → Partition n → (ℕ × ℕ) → Prop :=
  fun p c => c ∉ cells p ∧ IsLowerSet (↑(insert c (cells p)) : Set (ℕ × ℕ))

def IsAddableType := {n : ℕ} → Partition n → (ℕ × ℕ) → Prop

def AddableCell : {n : ℕ} → Partition n → Type :=
  fun p => {c : ℕ × ℕ // IsAddable p c}

def AddableCellType := {n : ℕ} → Partition n → Type

def adjoinedDiagram : ∀ {n} (p : Partition n) (_c : AddableCell p), YoungDiagram :=
  fun p c => ⟨insert c.val (cells p), c.property.2⟩

def adjoinedDiagramType := ∀ {n} (p : Partition n) (_c : AddableCell p), YoungDiagram

def addCell : ∀ {n} (p : Partition n), AddableCell p → Partition (n + 1) :=
  fun {n} p c => (adjoinedDiagram p c).toPartition (by
    change (insert c.val (cells p)).card = n + 1
    rw [Finset.card_insert_of_notMem c.property.1]
    exact congrArg (· + 1) (YoungDiagram.card_ofPartition p))

def addCellType := ∀ {n} (p : Partition n), AddableCell p → Partition (n + 1)

def lastLabelSubgroup : (n : ℕ) → Subgroup (SymmetricGroup (n + 1)) :=
  fun n =>
  { carrier := {g | g (Fin.last n) = Fin.last n}
    one_mem' := rfl
    mul_mem' := fun hg hh => by change _ = _; rw [Equiv.Perm.mul_apply, hh, hg]
    inv_mem' := fun {g} hg => by
      change g.symm (Fin.last n) = Fin.last n
      rw [Equiv.symm_apply_eq]; exact hg.symm }

def lastLabelSubgroupType := (n : ℕ) → Subgroup (SymmetricGroup (n + 1))

def extendPermutation : ∀ {n}, SymmetricGroup n → SymmetricGroup (n + 1) :=
  fun {n} g =>
  { toFun := Fin.lastCases (Fin.last n) (fun i => (g i).castSucc)
    invFun := Fin.lastCases (Fin.last n) (fun i => (g.symm i).castSucc)
    left_inv := by intro i; cases i using Fin.lastCases <;> simp
    right_inv := by intro i; cases i using Fin.lastCases <;> simp }

def extendPermutationType := ∀ {n}, SymmetricGroup n → SymmetricGroup (n + 1)

def hook : ∀ {n} {p : Partition n}, Cell p → Finset (ℕ × ℕ) :=
  fun {_n} {p} c => (cells p).filter (fun d =>
    (d.1 = c.val.1 ∧ c.val.2 ≤ d.2) ∨ (d.2 = c.val.2 ∧ c.val.1 ≤ d.1))

def hookType := ∀ {n} {p : Partition n}, Cell p → Finset (ℕ × ℕ)

def hookLength : ∀ {n} {p : Partition n}, Cell p → ℕ :=
  fun c => (hook c).card

def hookLengthType := ∀ {n} {p : Partition n}, Cell p → ℕ

def standardTableau_finiteType : Prop :=
  ∀ {n} (p : Partition n), Finite (StandardTableau p)

def emptyTableau_standardType : Prop :=
  IsStandard emptyTableau

def empty_standardTableau_uniqueType : Prop :=
  ∃! t : StandardTableau emptyPartition, t.val = emptyTableau

def empty_standardTableauCountType : Prop :=
  standardTableauCount emptyPartition = 1

def removable_iff_exists_diagramType : Prop :=
  ∀ {n} (p : Partition n) (c : ℕ × ℕ), IsRemovable p c ↔ c ∈ cells p ∧ ∃ d : YoungDiagram, d.cells = (cells p).erase c

def removable_iff_row_endType : Prop :=
  ∀ {n} (p : Partition n) (c : ℕ × ℕ), IsRemovable p c ↔ c.2 + 1 = rowLength p c.1 ∧ rowLength p (c.1 + 1) < rowLength p c.1

def deleteCell_cellsType : Prop :=
  ∀ {n} (p : Partition n) (c : RemovableCell p), cells (deleteCell p c) = (cells p).erase c.val

def addable_iff_exists_diagramType : Prop :=
  ∀ {n} (p : Partition n) (c : ℕ × ℕ), IsAddable p c ↔ c ∉ cells p ∧ ∃ d : YoungDiagram, d.cells = insert c (cells p)

def addable_iff_row_endType : Prop :=
  ∀ {n} (p : Partition n) (c : ℕ × ℕ), IsAddable p c ↔ c.2 = rowLength p c.1 ∧ (c.1 = 0 ∨ rowLength p c.1 < rowLength p (c.1 - 1))

def addCell_cellsType : Prop :=
  ∀ {n} (p : Partition n) (c : AddableCell p), cells (addCell p c) = insert c.val (cells p)

def deleted_cell_addableType : Prop :=
  ∀ {n} (p : Partition n) (c : RemovableCell p), IsAddable (deleteCell p c) c.val

def adjoined_cell_removableType : Prop :=
  ∀ {n} (p : Partition n) (c : AddableCell p), IsRemovable (addCell p c) c.val

def extendPermutation_castSuccType : Prop :=
  ∀ {n} (g : SymmetricGroup n) (i : Fin n), extendPermutation g i.castSucc = (g i).castSucc

def extendPermutation_lastType : Prop :=
  ∀ {n} (g : SymmetricGroup n), extendPermutation g (Fin.last n) = Fin.last n

def extendPermutation_oneType : Prop :=
  ∀ n, extendPermutation (1 : SymmetricGroup n) = 1

def extendPermutation_mulType : Prop :=
  ∀ {n} (g h : SymmetricGroup n), extendPermutation (g * h) = extendPermutation g * extendPermutation h

def extendPermutation_injectiveType : Prop :=
  ∀ n, Function.Injective (@extendPermutation n)

def lastLabelSubgroup_eq_rangeType : Prop :=
  ∀ {n} (g : SymmetricGroup (n + 1)), g ∈ lastLabelSubgroup n ↔ ∃ h : SymmetricGroup n, extendPermutation h = g

def hook_mem_iffType : Prop :=
  ∀ {n} {p : Partition n} (c : Cell p) (d : ℕ × ℕ), d ∈ hook c ↔ d ∈ cells p ∧ ((d.1 = c.val.1 ∧ c.val.2 ≤ d.2) ∨ (d.2 = c.val.2 ∧ c.val.1 ≤ d.1))

def hookLength_formulaType : Prop :=
  ∀ {n} {p : Partition n} (c : Cell p), hookLength c = (rowLength p c.val.1 - (c.val.2 + 1)) + (columnLength p c.val.2 - (c.val.1 + 1)) + 1

def hookLength_oneBasedType : Prop :=
  ∀ {n} {p : Partition n} (c : Cell p) (i j : ℕ), i = c.val.1 + 1 → j = c.val.2 + 1 → hookLength c = (rowLength p (i - 1) - j) + (columnLength p (j - 1) - i) + 1

/-- With ambient size `n+1`, this is the source inclusion S_n ⊆ S_{n+1}.
Thus it covers every positive ambient size, including S_0 ⊆ S_1. -/
def symmetricGroupEmbedding (n : ℕ) : SymmetricGroup n →* SymmetricGroup (n+1) where
  toFun := extendPermutation
  map_one' := by
    apply Equiv.ext
    intro i
    cases i using Fin.lastCases <;> simp [extendPermutation]
  map_mul' g h := by
    apply Equiv.ext
    intro i
    cases i using Fin.lastCases <;> simp [extendPermutation, Equiv.Perm.mul_apply]

def symmetricGroupEmbeddingType := (n : ℕ) → SymmetricGroup n →* SymmetricGroup (n+1)

def symmetricGroupEmbedding_injectiveType : Prop :=
  ∀ n, Function.Injective (symmetricGroupEmbedding n)

def removableCell_finiteType : Prop :=
  ∀ {n} (p : Partition n), Finite (RemovableCell p)

def hookLength_positiveType : Prop :=
  ∀ {n} {p : Partition n} (c : Cell p), 0 < hookLength c

end Specs.AdvancedFiniteGroupRepresentations
