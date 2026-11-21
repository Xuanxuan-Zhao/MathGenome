import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.DotProduct
import Mathlib.Data.Matrix.Mul

/-! Independent specifications for the matrix assertion of paper.tex W08
(lines 293–298 and 313–315), under the stored-real and safe-primitive conventions
of W02 and the two sequential evaluation orders of W07. -/
noncomputable section

namespace NumAnalysis206.Rounding.MatrixSpecs

/-- Each entry is the specified sequential dot product of its row and column.
`false` separately rounds products; `true` uses fused multiply-adds. -/
abbrev ProductType := Bool → (ℝ → ℝ) → {m k n : ℕ} →
  Matrix (Fin m) (Fin k) ℝ → Matrix (Fin k) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ

def productValue : ProductType := fun fused round {_m _k _n} A B =>
  Matrix.of fun i j => DotSpecs.finiteTrace fused round (A i) (fun l => B l j)

/-- Every executed primitive in every output entry has its exact result in D.
For the separate evaluation this checks both products and additions. -/
abbrev SafeType := Bool → (ℝ → ℝ) → Set ℝ → {m k n : ℕ} →
  Matrix (Fin m) (Fin k) ℝ → Matrix (Fin k) (Fin n) ℝ → Prop

def safeValue : SafeType := fun fused round D {_m _k _n} A B =>
  ∀ i j, DotSpecs.finiteSafe fused round D (A i) (fun l => B l j)

/-- Absolute value is taken entrywise. The product of the two nonnegative
matrices is ordinary matrix multiplication, not an operator norm. -/
def entrywiseBound {m k n : ℕ} (A : Matrix (Fin m) (Fin k) ℝ)
    (B : Matrix (Fin k) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) (u : ℝ) : Prop :=
  ∀ i j, |C i j - (A * B) i j| ≤
    _root_.Specs.NumAnalysis206.Rounding.gammaValue k u *
      ((Matrix.of fun i l => |A i l|) * (Matrix.of fun l j => |B l j|)) i j

/-- No positivity assumptions on the dimensions: k=0 uses empty dot products,
and m=0 or n=0 makes the entrywise conclusion vacuous. -/
def matrixProductError : Prop := ∀ (m k n : ℕ) (fused : Bool) (round : ℝ → ℝ)
    (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin k) (Fin n) ℝ)
    (u : ℝ) (D : Set ℝ),
  Specs.RelativeModelValue round u D → (k : ℝ) * u < 1 →
  safeValue fused round D A B → entrywiseBound A B (productValue fused round A B) u

/-- Empty dot products return zero even without a safety or model assumption. -/
def zeroInnerDimension : Prop := ∀ (m n : ℕ) (fused : Bool) (round : ℝ → ℝ)
    (A : Matrix (Fin m) (Fin 0) ℝ) (B : Matrix (Fin 0) (Fin n) ℝ),
  productValue fused round A B = 0

end NumAnalysis206.Rounding.MatrixSpecs
