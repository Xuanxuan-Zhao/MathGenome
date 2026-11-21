import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.HouseholderExactQR
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.HouseholderPivotStep
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.HouseholderTrailingStep
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.OrthogonalErrorAccumulation

/-! The actual W32 stored procedure. Rows and columns are zero based; at column
`j` the active dimension is `m-j`, corresponding to the paper's `m-j+1`.
Each dot may use either of the two sequential W07 evaluations. All copies,
signs, zero tests, and replacement by exact zeros are exact. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace NumAnalysis206.HouseholderColumnDefinitions
open MatrixDefinitions HouseholderDefinitions HouseholderQRDefinitions

/-- Independent choices of the two source-approved sequential dot evaluations.
`false` rounds separate products and left-to-right additions; `true` uses FMA. -/
structure DotModes where
  pivot : Bool
  numerator : Bool
  denominator : Bool

/-- Tail of an arbitrary column on the current active row block. -/
def columnTail {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j c : Fin n) :
    Vec ℝ (m-j.val) :=
  WithLp.toLp 2 (fun i => B (split m j.val (by omega) (Sum.inr i)) c)

/-- Retain the earlier rows and replace all active column tails. -/
def splice {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j : Fin n)
    (z : Fin n → Vec ℝ (m-j.val)) : Mat ℝ m n :=
  (fromRows (B.submatrix (fun i => split m j.val (by omega) (Sum.inl i)) id)
    (fun i c => z c i)).submatrix (split m j.val (by omega)).symm id

/-- The stored direction for the specified rounding map. -/
def roundedW {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (B : Mat ℝ m n) (h : n ≤ m)
    (j : Fin n) : Vec ℝ (m-j.val) := by
  letI : NeZero (m-j.val) := ⟨by have := j.isLt; omega⟩
  exact HouseholderPivotDefinitions.storedDirection modes.pivot round (columnTail B h j j)

def newTail {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (B : Mat ℝ m n) (h : n ≤ m)
    (j c : Fin n) : Vec ℝ (m-j.val) := by
  letI : NeZero (m-j.val) := ⟨by have := j.isLt; omega⟩
  exact if c.val < j.val then columnTail B h j c else
    if c = j then
      HouseholderPivotDefinitions.computedAlpha modes.pivot round (columnTail B h j j) •
        firstVector (m-j.val)
    else HouseholderTrailingDefinitions.update modes.numerator modes.denominator round (roundedW modes round B h j)
      (columnTail B h j c)

/-- A zero pivot tail skips the entire step, including trailing columns. -/
def storedStep {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (B : Mat ℝ m n) (h : n ≤ m)
    (j : Fin n) : Mat ℝ m n :=
  if columnTail B h j j = 0 then B else splice B h j (newTail modes round B h j)

/-- Exact orthogonal reflector of the actual stored direction. -/
def exactUpdate {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (B : Mat ℝ m n) (h : n ≤ m)
    (j : Fin n) : Mat ℝ m m :=
  if columnTail B h j j = 0 then 1 else
    blockLift (by omega) (reflector (roundedW modes round B h j))

def stepConstant {m n : ℕ} (u : ℝ) (B : Mat ℝ m n) (h : n ≤ m)
    (j : Fin n) : ℝ :=
  if columnTail B h j j = 0 then 0 else
    max (HouseholderPivotDefinitions.normError (m-j.val) u +
      8 * HouseholderPivotDefinitions.directionError (m-j.val) u)
      (HouseholderTrailingDefinitions.ctail
        (_root_.Specs.NumAnalysis206.Rounding.gammaValue (m-j.val) u) u)

/-- Exactly the nontrivial step's budget and per-primitive range hypotheses.
In particular, nonzero stored directions and positive computed denominators
are proved later, and are not hypotheses here. -/
def SafeStep {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (B : Mat ℝ m n) (h : n ≤ m) (j : Fin n) : Prop := by
  letI : NeZero (m-j.val) := ⟨by have := j.isLt; omega⟩
  exact columnTail B h j j ≠ 0 →
    ((m-j.val : ℕ) : ℝ) * u < 1 ∧
    _root_.Specs.NumAnalysis206.Rounding.gammaValue (m-j.val) u < 1 ∧
    HouseholderPivotDefinitions.safe modes.pivot round D (columnTail B h j j) ∧
    ∀ c : Fin n, j.val < c.val →
      HouseholderTrailingDefinitions.Safe modes.numerator modes.denominator round D
        (roundedW modes round B h j) (columnTail B h j c)

def run {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (A : Mat ℝ m n) (h : n ≤ m) :
    ℕ → Mat ℝ m n
  | 0 => A
  | k+1 => if hk : k < n then storedStep modes round (run modes round A h k) h ⟨k,hk⟩
    else run modes round A h k

def updates {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (A : Mat ℝ m n) (h : n ≤ m)
    (k : ℕ) : Mat ℝ m m :=
  if hk : k < n then exactUpdate modes round (run modes round A h k) h ⟨k,hk⟩ else 1

def constants {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (u : ℝ) (A : Mat ℝ m n)
    (h : n ≤ m) (k : ℕ) : ℝ :=
  if hk : k < n then stepConstant u (run modes round A h k) h ⟨k,hk⟩ else 0

def SafeRun {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (A : Mat ℝ m n) (h : n ≤ m) : Prop :=
  ∀ j : Fin n, SafeStep modes round u D (run modes round A h j.val) h j

def fullProduct {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (A : Mat ℝ m n) (h : n ≤ m) :
    Mat ℝ m m := OrthogonalErrorDefinitions.forwardProduct (updates modes round A h) n

/-- The implicit inverse factor, explicitly a product of the very same stored-w
reflectors in reverse application order. There are no rounded operations here. -/
def implicitProduct {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ)
    (A : Mat ℝ m n) (h : n ≤ m) : ℕ → Mat ℝ m m
  | 0 => 1
  | k+1 => implicitProduct modes round A h k * updates modes round A h k

def rFactor {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (A : Mat ℝ m n) (h : n ≤ m) : Mat ℝ n n :=
  (run modes round A h n).submatrix (Fin.castLE h) id

def qFactor {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (A : Mat ℝ m n) (h : n ≤ m) : Mat ℝ m n :=
  (implicitProduct modes round A h n).submatrix id (Fin.castLE h)

def backwardError {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (A : Mat ℝ m n) (h : n ≤ m) :
    Mat ℝ m n := (fullProduct modes round A h).conjTranspose * run modes round A h n - A

end NumAnalysis206.HouseholderColumnDefinitions

namespace Specs.NumAnalysis206.HouseholderColumnBackward
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.HouseholderColumnDefinitions

/-- Full stored W32 QR, with its exact implicit Q and columnwise backward bound.
No rank, nonempty-dimension, or nonzero-column hypothesis is imposed. -/
def column_backward : Prop :=
  ∀ {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (A : Mat ℝ m n) (h : n ≤ m),
    _root_.NumAnalysis206.Rounding.Specs.RelativeModelValue round u D →
    SafeRun modes round u D A h →
    (∀ k ≤ n, _root_.NumAnalysis206.HouseholderQRDefinitions.Cleared (run modes round A h k) k) ∧
    (∀ j : Fin n, ∀ c : Fin n, c.val < j.val → ∀ i,
      run modes round A h (j.val+1) i c = run modes round A h j.val i c) ∧
    implicitProduct modes round A h n = (fullProduct modes round A h).conjTranspose ∧
    (fullProduct modes round A h).conjTranspose * fullProduct modes round A h = 1 ∧
    A + backwardError modes round A h = qFactor modes round A h * rFactor modes round A h ∧
    (qFactor modes round A h).conjTranspose * qFactor modes round A h = 1 ∧
    _root_.NumAnalysis206.MatrixDefinitions.IsUpperTriangular (rFactor modes round A h) ∧
    (∀ i : Fin m, n ≤ i.val → ∀ c, run modes round A h n i c = 0) ∧
    (∀ c, ‖columns (backwardError modes round A h) c‖ ≤
      ((∏ k ∈ Finset.range n, (1 + constants modes round u A h k)) - 1) * ‖columns A c‖) ∧
    (n = 0 → backwardError modes round A h = 0)

end Specs.NumAnalysis206.HouseholderColumnBackward
