import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StandardBasisRationalModel
import Mathlib.LinearAlgebra.Quotient.Basic

/-! FR-B04, source lines 581–640. All cells and labels are zero based.
Ambient size `n+1` includes deletion to the empty shape. Corner indices count
strictly earlier rows, so index zero is the first removable box. Filtration
terms live in the original permutation module; the final term is the original
Specht span. Quotients use the preceding term pulled back to the current term.
-/
noncomputable section
namespace Specs.AdvancedFiniteGroupRepresentations

open scoped Classical

/-- The row of a label is independent of the tableau representative. -/
def tabloidRow {n : ℕ} {p : Partition n} (q : Tabloid p) : Fin n → ℕ :=
  Quotient.lift labelRow (fun _ _ h => h) q

/-- Removable cells, with their original coordinates retained. -/
def removableCorners {n : ℕ} (p : Partition n) : Finset (ℕ × ℕ) :=
  (cells p).filter (IsRemovable p)

def cornerCount {n : ℕ} (p : Partition n) : ℕ := (removableCorners p).card

/-- Number of removable boxes in strictly earlier rows. -/
def cornerIndex {n : ℕ} (p : Partition n) (c : RemovableCell p) : ℕ :=
  ((removableCorners p).filter (fun d => d.1 < c.val.1)).card

/-- The source's `F_i`, as a subspace of the original tabloid module. -/
def restrictionFiltration {n : ℕ} (p : Partition (n + 1)) (i : ℕ) :
    Submodule ℂ (PermutationModule p) :=
  Submodule.span ℂ {v | ∃ t : StandardTableau p, ∃ c : RemovableCell p,
    cornerIndex p c < i ∧ (t.val.symm (Fin.last n)).val = c.val ∧ v = polytabloid t.val}

/-- The quotient at the box `c` (index `cornerIndex p c + 1` in one-based form). -/
abbrev RestrictionStepQuotient {n : ℕ} (p : Partition (n + 1))
    (c : RemovableCell p) :=
  (restrictionFiltration p (cornerIndex p c + 1)) ⧸
    ((restrictionFiltration p (cornerIndex p c)).comap
      (restrictionFiltration p (cornerIndex p c + 1)).subtype)

def tabloidRowType := {n : ℕ} → {p : Partition n} → Tabloid p → Fin n → ℕ

def removableCornersType := {n : ℕ} → Partition n → Finset (ℕ × ℕ)

def cornerCountType := {n : ℕ} → Partition n → ℕ

def cornerIndexType := ∀ {n : ℕ} (p : Partition n), RemovableCell p → ℕ

def restrictionFiltrationType := ∀ {n : ℕ} (p : Partition (n + 1)),
  ℕ → Submodule ℂ (PermutationModule p)

def RestrictionStepQuotientType := ∀ {n : ℕ} (p : Partition (n + 1)),
  RemovableCell p → Type

def standard_last_removableType : Prop := ∀ {n : ℕ} {p : Partition (n + 1)}
  (t : StandardTableau p), IsRemovable p (t.val.symm (Fin.last n)).val

def cornerIndex_lt_countType : Prop := ∀ {n : ℕ} (p : Partition n)
  (c : RemovableCell p), cornerIndex p c < cornerCount p

/-- Indices identify the increasing-row list with `Fin (cornerCount p)`. -/
def cornerIndex_orderType : Prop := ∀ {n : ℕ} (p : Partition n),
  (∀ c d : RemovableCell p, cornerIndex p c < cornerIndex p d ↔ c.val.1 < d.val.1) ∧
  (∀ i : Fin (cornerCount p), ∃! c : RemovableCell p, cornerIndex p c = i.val)

def restrictionFiltration_zeroType : Prop := ∀ {n : ℕ} (p : Partition (n + 1)),
  restrictionFiltration p 0 = ⊥

def restrictionFiltration_monoType : Prop := ∀ {n : ℕ} (p : Partition (n + 1)),
  Monotone (restrictionFiltration p)

def restrictionFiltration_le_spechtType : Prop := ∀ {n : ℕ} (p : Partition (n + 1)) (i : ℕ),
  restrictionFiltration p i ≤ spechtSpan p

def restrictionFiltration_topType : Prop := ∀ {n : ℕ} (p : Partition (n + 1)),
  restrictionFiltration p (cornerCount p) = spechtSpan p

/-- Full restriction-filtration conclusion, including the actual deletion on
all tabloids. At a matching row the target tabloid has precisely the rows of
the surviving labels; at any other row the map is zero. Keeping original row
indices automatically omits a final row when it becomes empty.

The equivalence is induced by these same deletion maps. Its equivariance is
stated on quotient representatives, with the actions inherited from the
ambient tabloid modules. Together with invariance, this is equivariance on
the quotient itself, without choosing new actions on either side. -/
def restriction_filtrationType : Prop := ∀ {n : ℕ} (p : Partition (n + 1)),
  ∃ D : ∀ c : RemovableCell p,
      PermutationModule p →ₗ[ℂ] PermutationModule (deleteCell p c),
    (∀ c q, tabloidRow q (Fin.last n) ≠ c.val.1 →
      D c (MonoidAlgebra.single q 1) = 0) ∧
    (∀ c q, tabloidRow q (Fin.last n) = c.val.1 →
      ∃! q' : Tabloid (deleteCell p c),
        (∀ a : Fin n, tabloidRow q' a = tabloidRow q a.castSucc) ∧
        D c (MonoidAlgebra.single q 1) = MonoidAlgebra.single q' 1) ∧
    (∀ c g v, D c (permutationRepresentation p (extendPermutation g) v) =
      permutationRepresentation (deleteCell p c) g (D c v)) ∧
    restrictionFiltration p 0 = ⊥ ∧
    Monotone (restrictionFiltration p) ∧
    restrictionFiltration p (cornerCount p) = spechtSpan p ∧
    (∀ i g v, v ∈ restrictionFiltration p i →
      permutationRepresentation p (extendPermutation g) v ∈ restrictionFiltration p i) ∧
    (∀ c : RemovableCell p,
      ∃ e : RestrictionStepQuotient p c ≃ₗ[ℂ] SpechtModule (deleteCell p c),
        (∀ v : restrictionFiltration p (cornerIndex p c + 1),
          (e (Submodule.Quotient.mk v)).val = D c v.val) ∧
        (∀ (g : SymmetricGroup n)
          (v w : restrictionFiltration p (cornerIndex p c + 1)),
          w.val = permutationRepresentation p (extendPermutation g) v.val →
          (e (Submodule.Quotient.mk w)).val =
            permutationRepresentation (deleteCell p c) g
              (e (Submodule.Quotient.mk v)).val))

end Specs.AdvancedFiniteGroupRepresentations
