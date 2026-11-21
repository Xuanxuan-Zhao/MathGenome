import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Convex.Function

/-! The minor coordinates in paper.tex §§8.5–8.6. All indices are zero based;
thus the first-row cofactor of column l has sign (-1)^l. -/
noncomputable section
open scoped BigOperators InnerProductSpace

namespace VariationalNotes.Sobolev.Minors

/-- Increasing lists, so a row or column set occurs exactly once. -/
abbrev Selection (n j : ℕ) := {a : Fin j → Fin n // StrictMono a}
instance (n j : ℕ) : Fintype (Selection n j) := by
  classical
  exact Subtype.fintype _

abbrev Index (m d j : ℕ) := Selection m j × Selection d j
abbrev MinorVector (m d j : ℕ) := EuclideanSpace ℝ (Index m d j)

/-- This uses the very same (target,domain) entry order as `Gradient`. -/
def submatrix {m d j : ℕ} (a : Index m d j) (Z : Gradient m d) :
    Matrix (Fin j) (Fin j) ℝ := fun i k => Z (a.1.val i, a.2.val k)

def minor {m d j : ℕ} (a : Index m d j) (Z : Gradient m d) : ℝ :=
  Matrix.det (submatrix a Z)

def minors {m d : ℕ} (j : ℕ) (Z : Gradient m d) : MinorVector m d j :=
  WithLp.toLp 2 (fun a => minor a Z)

/-- The signed determinant obtained by deleting row zero and column l.
The order is written n+1 so that the empty complementary determinant at order
one is the ordinary determinant of a 0-by-0 matrix. -/
def cofactor {m d n : ℕ} (a : Index m d (n+1)) (l : Fin (n+1))
    (Z : Gradient m d) : ℝ :=
  (-1 : ℝ) ^ l.val * Matrix.det ((submatrix a Z).submatrix Fin.succ l.succAbove)

def singletonSelection {n : ℕ} (i : Fin n) : Selection n 1 :=
  ⟨fun _ => i, by intro a b h; exact False.elim (by have := Fin.eq_zero a; have := Fin.eq_zero b; omega)⟩

def entryIndex {m d : ℕ} (ik : Fin m × Fin d) : Index m d 1 :=
  (singletonSelection ik.1, singletonSelection ik.2)

/-- Independent coordinates of orders 1,...,min(m,d), with a Euclidean norm
on the flattened finite list. There are no equations imposed on these coordinates. -/
abbrev AllIndex (m d : ℕ) := Σ k : Fin (min m d), Index m d (k.val+1)
abbrev Coordinates (m d : ℕ) := EuclideanSpace ℝ (AllIndex m d)

def allMinors {m d : ℕ} (Z : Gradient m d) : Coordinates m d :=
  WithLp.toLp 2 (fun a => minor a.2 Z)

/-- Projection onto order one followed by its canonical entry identification. -/
def firstMatrix {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    Coordinates m d →ₗ[ℝ] Gradient m d where
  toFun z := WithLp.toLp 2 (fun ik => z ⟨⟨0, lt_min hm hd⟩, entryIndex ik⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Convexity is on the whole independent coordinate space, jointly. -/
def IsPolyconvexRepresentation {m d : ℕ}
    (F : Domain d → Vector m → Gradient m d → ℝ)
    (G : Domain d → Vector m → Coordinates m d → ℝ) : Prop :=
  (∀ x s Z, F x s Z = G x s (allMinors Z)) ∧
  ∀ x s, ConvexOn ℝ Set.univ (G x s)

/-- A matrix-convex density extends by ignoring every higher minor. -/
def convexLift {m d : ℕ} (hm : 0 < m) (hd : 0 < d)
    (F : Domain d → Vector m → Gradient m d → ℝ) :
    Domain d → Vector m → Coordinates m d → ℝ :=
  fun x s z => F x s (firstMatrix hm hd z)

namespace Expected

def IndexType := ℕ → ℕ → ℕ → Type
def IndexValue : IndexType := Index

def MinorType := {m d j : ℕ} → Index m d j → Gradient m d → ℝ
def MinorValue : MinorType := @minor

def MinorsType := {m d : ℕ} → (j : ℕ) → Gradient m d → MinorVector m d j
def MinorsValue : MinorsType := @minors

def CofactorType := {m d n : ℕ} → Index m d (n+1) → Fin (n+1) → Gradient m d → ℝ
def CofactorValue : CofactorType := @cofactor

def CoordinatesType := ℕ → ℕ → Type
def CoordinatesValue : CoordinatesType := Coordinates

def AllMinorsType := {m d : ℕ} → Gradient m d → Coordinates m d
def AllMinorsValue : AllMinorsType := @allMinors

def RepresentationType := {m d : ℕ} →
  (Domain d → Vector m → Gradient m d → ℝ) →
  (Domain d → Vector m → Coordinates m d → ℝ) → Prop
def RepresentationValue : RepresentationType := @IsPolyconvexRepresentation

def LiftType := {m d : ℕ} → (hm : 0 < m) → (hd : 0 < d) →
  (Domain d → Vector m → Gradient m d → ℝ) →
  Domain d → Vector m → Coordinates m d → ℝ
def LiftValue : LiftType := @convexLift

/-- No missing entries or duplicate entries in the first-order vector. -/
def FirstIdentification : Prop := ∀ m d : ℕ,
  ∃ e : Gradient m d ≃ₗᵢ[ℝ] MinorVector m d 1,
    (∀ Z, e Z = minors 1 Z) ∧
    (∀ Z W : Gradient m d, ⟪minors 1 Z, minors 1 W⟫_ℝ = frobenius Z W)

def FirstEntries : Prop := ∀ {m d : ℕ} (Z : Gradient m d) (ik : Fin m × Fin d),
  minors 1 Z (entryIndex ik) = Z ik

def FirstNorm : Prop := ∀ {m d : ℕ} (Z : Gradient m d),
  ‖minors 1 Z‖ = ‖Z‖ ∧
  ‖minors 1 Z‖ = Real.sqrt (∑ i : Fin m, ∑ k : Fin d, (Z (i,k))^2)

def CofactorOne : Prop := ∀ {m d : ℕ} (a : Index m d 1) (Z : Gradient m d),
  cofactor a 0 Z = 1

/-- The sign and row convention agree with expansion along the first row. -/
def FirstRowExpansion : Prop := ∀ {m d n : ℕ} (a : Index m d (n+1)) (Z : Gradient m d),
  minor a Z = ∑ l : Fin (n+1), Z (a.1.val 0, a.2.val l) * cofactor a l Z

def AllOrders : Prop := ∀ {m d : ℕ} (Z : Gradient m d)
  (k : Fin (min m d)) (a : Index m d (k.val+1)),
  allMinors Z ⟨k,a⟩ = minors (k.val+1) Z a

def MatrixRecovery : Prop := ∀ {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (Z : Gradient m d),
  firstMatrix hm hd (allMinors Z) = Z

def ConvexImpliesPolyconvex : Prop := ∀ {m d : ℕ} (hm : 0 < m) (hd : 0 < d)
  (F : Domain d → Vector m → Gradient m d → ℝ),
  (∀ x s, ConvexOn ℝ Set.univ (F x s)) →
  IsPolyconvexRepresentation F (convexLift hm hd F)

end Expected
end VariationalNotes.Sobolev.Minors
