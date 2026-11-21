import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.Errors
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Mul

/-! W15, componentwise part. Nonnegative entry scales are represented by NNReal.
The finite budget set consists of actual perturbations of the original matrix
and right-hand side. Its infimum is taken in ENNReal, including infeasibility.
RCLike includes both real and complex scalars. No nonempty index hypothesis is used. -/
noncomputable section
set_option linter.checkUnivs false
open scoped BigOperators NNReal ENNReal
universe u v w
namespace Specs.NumAnalysis206.Conditioning.Componentwise

variable {I : Type u} {J : Type v} {K : Type w} [Fintype I] [Fintype J] [RCLike K]

def residual (A : Matrix I J K) (b : I → K) (x : J → K) : I → K :=
  b - A.mulVec x

def rowScale (E : Matrix I J ℝ≥0) (f : I → ℝ≥0) (x : J → K) : I → ℝ≥0 :=
  fun i => (∑ j, E i j * ‖x j‖₊) + f i

def feasible (A : Matrix I J K) (b : I → K) (x : J → K)
    (E : Matrix I J ℝ≥0) (f : I → ℝ≥0) (ε : ℝ≥0) : Prop :=
  ∃ (ΔA : Matrix I J K) (Δb : I → K),
    (A + ΔA).mulVec x = b + Δb ∧
    (∀ i j, ‖ΔA i j‖₊ ≤ ε * E i j) ∧ (∀ i, ‖Δb i‖₊ ≤ ε * f i)

def backwardError (A : Matrix I J K) (b : I → K) (x : J → K)
    (E : Matrix I J ℝ≥0) (f : I → ℝ≥0) : ℝ≥0∞ :=
  sInf {t | ∃ ε : ℝ≥0, feasible A b x E f ε ∧ (ε : ℝ≥0∞) = t}

def formula (A : Matrix I J K) (b : I → K) (x : J → K)
    (E : Matrix I J ℝ≥0) (f : I → ℝ≥0) : ℝ≥0∞ :=
  Errors.componentwiseSize (rowScale E f x) (residual A b x)

def residualType := ∀ {I : Type u} {J : Type v} {K : Type w} [Fintype J]
  [RCLike K], Matrix I J K → (I → K) → (J → K) → (I → K)
def rowScaleType := ∀ {I : Type u} {J : Type v} {K : Type w} [Fintype J]
  [RCLike K], Matrix I J ℝ≥0 → (I → ℝ≥0) → (J → K) → (I → ℝ≥0)
def feasibleType := ∀ {I : Type u} {J : Type v} {K : Type w} [Fintype J]
  [RCLike K], Matrix I J K → (I → K) → (J → K) → Matrix I J ℝ≥0 → (I → ℝ≥0) → ℝ≥0 → Prop
def backwardErrorType := ∀ {I : Type u} {J : Type v} {K : Type w} [Fintype J]
  [RCLike K], Matrix I J K → (I → K) → (J → K) → Matrix I J ℝ≥0 → (I → ℝ≥0) → ℝ≥0∞
def formulaType := ∀ {I : Type u} {J : Type v} {K : Type w} [Fintype J]
  [RCLike K], Matrix I J K → (I → K) → (J → K) → Matrix I J ℝ≥0 → (I → ℝ≥0) → ℝ≥0∞

def feasible_iffStatement : Prop :=
  ∀ {I : Type u} {J : Type v} {K : Type w} [Fintype I] [Fintype J] [RCLike K]
    (A : Matrix I J K) (b : I → K) (x : J → K) (E : Matrix I J ℝ≥0)
    (f : I → ℝ≥0) (ε : ℝ≥0),
    feasible A b x E f ε ↔ ∀ i, ‖residual A b x i‖₊ ≤ ε * rowScale E f x i

def backwardError_eq_formulaStatement : Prop :=
  ∀ {I : Type u} {J : Type v} {K : Type w} [Fintype I] [Fintype J] [RCLike K]
    (A : Matrix I J K) (b : I → K) (x : J → K) (E : Matrix I J ℝ≥0) (f : I → ℝ≥0),
    backwardError A b x E f = formula A b x E f

def finite_attainedStatement : Prop :=
  ∀ {I : Type u} {J : Type v} {K : Type w} [Fintype I] [Fintype J] [RCLike K]
    (A : Matrix I J K) (b : I → K) (x : J → K) (E : Matrix I J ℝ≥0) (f : I → ℝ≥0),
    backwardError A b x E f ≠ ⊤ → ∃ ε : ℝ≥0,
      (ε : ℝ≥0∞) = backwardError A b x E f ∧ feasible A b x E f ε

-- These state the conventions of the displayed maximum explicitly.
def zero_rowStatement : Prop :=
  ∀ {I : Type u} {J : Type v} {K : Type w} [Fintype I] [Fintype J] [RCLike K]
    (A : Matrix I J K) (b : I → K) (x : J → K) (E : Matrix I J ℝ≥0) (f : I → ℝ≥0) (i : I),
    rowScale E f x i = 0 → residual A b x i ≠ 0 → backwardError A b x E f = ⊤

def empty_rowsStatement : Prop :=
  ∀ {I : Type u} {J : Type v} {K : Type w} [Fintype I] [Fintype J] [RCLike K] [IsEmpty I]
    (A : Matrix I J K) (b : I → K) (x : J → K) (E : Matrix I J ℝ≥0) (f : I → ℝ≥0),
    backwardError A b x E f = 0
end Specs.NumAnalysis206.Conditioning.Componentwise
