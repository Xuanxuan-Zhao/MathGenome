import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StandardBasisRationalModel

/-! FR-B08, source lines 738–806. Hooks are the actual sets of boxes defined
upstream, not numerical surrogates. Coordinates are zero based. All rational
quotients cast the natural factorial and the natural hook product explicitly.
The row and column specializations include the empty diagram. -/
noncomputable section
open scoped BigOperators
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Product of the cardinalities of the hooks of all cells of the diagram. -/
def hookProduct {n : ℕ} (p : Partition n) : ℕ :=
  ∏ c : Cell p, hookLength c

def hookProductType := {n : ℕ} → Partition n → ℕ

def allHookLengths_positiveType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (c : Cell p), 0 < hookLength c

def hookProduct_positiveType : Prop :=
  ∀ {n : ℕ} (p : Partition n), 0 < hookProduct p

def hookProduct_emptyType : Prop := hookProduct emptyPartition = 1

/-- The quantitative formula for all partitions, including `n = 0`. -/
def hookLength_formula_countType : Prop :=
  ∀ {n : ℕ} (p : Partition n),
    (standardTableauCount p : ℚ) = (n.factorial : ℚ) / (hookProduct p : ℚ)

/-- Both equalities in the source, in a common field with explicit casts. -/
def hookLength_formula_dimensionType : Prop :=
  ∀ {n : ℕ} (p : Partition n),
    Module.finrank ℂ (SpechtModule p) = standardTableauCount p ∧
    (Module.finrank ℂ (SpechtModule p) : ℚ) =
      (n.factorial : ℚ) / (hookProduct p : ℚ)

/-- At most one nonempty row; for positive size this is exactly a single row. -/
def specht_finrank_singleRowType : Prop :=
  ∀ {n : ℕ} (p : Partition n), length p ≤ 1 →
    Module.finrank ℂ (SpechtModule p) = 1

/-- At most one nonempty column; for positive size this is exactly a single column. -/
def specht_finrank_singleColumnType : Prop :=
  ∀ {n : ℕ} (p : Partition n), rowLength p 0 ≤ 1 →
    Module.finrank ℂ (SpechtModule p) = 1

end Specs.AdvancedFiniteGroupRepresentations
