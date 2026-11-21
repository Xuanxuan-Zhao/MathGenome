import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SpechtModules
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! FR B09 (lines 808–831): the point representation and the shape (n-1,1).
Labels and cells use the upstream zero-based convention. -/
noncomputable section
open scoped BigOperators
namespace Specs.AdvancedFiniteGroupRepresentations

private def standardDiagram (n : ℕ) (h : 2 ≤ n) : YoungDiagram :=
  YoungDiagram.ofRowLens [n - 1, 1] (by rw [List.sortedGE_iff_pairwise]; simp; omega)

private theorem standardDiagram_rows (n : ℕ) (h : 2 ≤ n) :
    (standardDiagram n h).rowLens = [n - 1, 1] := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  intro x hx
  rcases hx with rfl | rfl <;> omega

/-- The canonical partition with rows n-1 and 1, including n=2. -/
def standardPartition (n : ℕ) (h : 2 ≤ n) : Partition n :=
  (standardDiagram n h).toPartition (by
    rw [← YoungDiagram.sum_rowLens_eq_card, standardDiagram_rows]
    simp; omega)

abbrev PointModule (n : ℕ) := MonoidAlgebra ℂ (Fin n)

def pointCoordinates (n : ℕ) : PointModule n ≃ₗ[ℂ] (Fin n → ℂ) :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).trans (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin n))

def pointRepresentation (n : ℕ) : Representation ℂ (SymmetricGroup n) (PointModule n) :=
  Representation.ofMulAction ℂ (SymmetricGroup n) (Fin n)

def pointVector {n} (a : Fin n) : PointModule n := MonoidAlgebra.single a 1

def pointSum (n : ℕ) : PointModule n →ₗ[ℂ] ℂ where
  toFun x := ∑ a, x.coeff a
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' z x := by simp [Finset.mul_sum]

def sumZero (n : ℕ) : Submodule ℂ (PointModule n) := (pointSum n).ker

/-- The independent contract uses literal cell positions, so the normalization
is the actual bottom-row label and the actual column polytabloid. -/
def standard_representationType : Prop :=
  ∀ (n : ℕ) (h : 2 ≤ n),
    parts (standardPartition n h) = [n - 1, 1] ∧
    ∃ (bottom top : Cell (standardPartition n h))
      (e : PermutationModule (standardPartition n h) ≃ₗ[ℂ] PointModule n),
      bottom.val = (1, 0) ∧ top.val = (0, 0) ∧
      (∀ (t : Tableau (standardPartition n h)) (z : ℂ),
        e (MonoidAlgebra.single (tabloid t) z) = z • pointVector (t bottom)) ∧
      (∀ g v, e (permutationRepresentation (standardPartition n h) g v) =
        pointRepresentation n g (e v)) ∧
      (∀ t : Tableau (standardPartition n h),
        e (polytabloid t) = pointVector (t bottom) - pointVector (t top)) ∧
      Submodule.map e.toLinearMap (spechtSpan (standardPartition n h)) = sumZero n ∧
      (∀ g v, v ∈ sumZero n → pointRepresentation n g v ∈ sumZero n) ∧
      Module.finrank ℂ (SpechtModule (standardPartition n h)) = n - 1

/-- Coordinates identify the chosen finite basis model with the usual C^n
and the natural permutation of coordinates. -/
def point_coordinatesType : Prop :=
  (∀ n (x : PointModule n) a, pointCoordinates n x a = x.coeff a) ∧
  (∀ n (g : SymmetricGroup n) (x : PointModule n) a,
    pointCoordinates n (pointRepresentation n g x) a = pointCoordinates n x (g⁻¹ a)) ∧
  (∀ n (x : PointModule n), pointSum n x = ∑ a, pointCoordinates n x a)

def standard_S3Type : Prop :=
  parts (standardPartition 3 (by decide)) = [2, 1] ∧
  Module.finrank ℂ (SpechtModule (standardPartition 3 (by decide))) = 2

end Specs.AdvancedFiniteGroupRepresentations
