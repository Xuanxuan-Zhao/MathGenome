import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Basic.ENNReal.Inv

/-! Independent specification of paper.tex, W12 (415–437).
The domain is a subtype, so f is only evaluated at valid inputs. Sizes may
be extended nonnegative numbers; finite nonnegative sizes embed canonically.
All selected norm scales are nonnegative, with relative scales nonzero.
A component with zero scale allows only a zero perturbation at finite budget.
No infimum is asserted to be attained. -/

open scoped NNReal ENNReal

noncomputable section

set_option linter.unusedVariables false
set_option linter.checkUnivs false

universe u v w

namespace Specs.NumAnalysis206.Conditioning.Errors

def absoluteForwardError {X : Type u} {Y : Type v} [NormedAddCommGroup Y] {U : Set X} (f : U → Y) (x : U) (yhat : Y) : ℝ :=
  ‖yhat - f x‖

def absoluteForwardErrorType :=
  ∀ {X : Type u} {Y : Type v} [NormedAddCommGroup Y] {U : Set X} (f : U → Y) (x : U) (yhat : Y), ℝ

def relativeForwardError {X : Type u} {Y : Type v} [NormedAddCommGroup Y] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (outputScale : ℝ≥0) (_hscale : outputScale ≠ 0) : ℝ :=
  absoluteForwardError f x yhat / (outputScale : ℝ)

def relativeForwardErrorType :=
  ∀ {X : Type u} {Y : Type v} [NormedAddCommGroup Y] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (outputScale : ℝ≥0) (_hscale : outputScale ≠ 0), ℝ

def feasiblePerturbation {X : Type u} {Y : Type v} [Add X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) (v : X) : Prop :=
  v ∈ D ∧ ∃ h : (x : X) + v ∈ U, f ⟨(x : X) + v, h⟩ = yhat

def feasiblePerturbationType :=
  ∀ {X : Type u} {Y : Type v} [Add X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) (v : X), Prop

def backwardError {X : Type u} {Y : Type v} [Add X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) (size : X → ℝ≥0∞) : ℝ≥0∞ :=
  sInf {r | ∃ v, feasiblePerturbation f x yhat D v ∧ size v = r}

def backwardErrorType :=
  ∀ {X : Type u} {Y : Type v} [Add X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) (size : X → ℝ≥0∞), ℝ≥0∞

def isBackwardCertificate {X : Type u} {Y : Type v} [Add X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) (size : X → ℝ≥0∞) (v : X) (bound : ℝ≥0) : Prop :=
  feasiblePerturbation f x yhat D v ∧ size v ≤ (bound : ℝ≥0∞)

def isBackwardCertificateType :=
  ∀ {X : Type u} {Y : Type v} [Add X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) (size : X → ℝ≥0∞) (v : X) (bound : ℝ≥0), Prop

def normwiseSize {X : Type u} [NormedAddCommGroup X] (v : X) : ℝ≥0∞ :=
  (‖v‖₊ : ℝ≥0∞)

def normwiseSizeType :=
  ∀ {X : Type u} [NormedAddCommGroup X] (v : X), ℝ≥0∞

def relativeNormwiseSize {X : Type u} [NormedAddCommGroup X] (inputScale : ℝ≥0) (_hscale : inputScale ≠ 0) (v : X) : ℝ≥0∞ :=
  ((‖v‖₊ / inputScale : ℝ≥0) : ℝ≥0∞)

def relativeNormwiseSizeType :=
  ∀ {X : Type u} [NormedAddCommGroup X] (inputScale : ℝ≥0) (_hscale : inputScale ≠ 0) (v : X), ℝ≥0∞

def componentwiseSize {I : Type u} {K : Type v} [NormedAddCommGroup K] (scale : I → ℝ≥0) (v : I → K) : ℝ≥0∞ :=
  ⨆ i, (‖v i‖₊ : ℝ≥0∞) / (scale i : ℝ≥0∞)

def componentwiseSizeType :=
  ∀ {I : Type u} {K : Type v} [NormedAddCommGroup K] (scale : I → ℝ≥0) (v : I → K), ℝ≥0∞

def normwiseBackwardError {X : Type u} {Y : Type v} [NormedAddCommGroup X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) : ℝ≥0∞ :=
  backwardError f x yhat D normwiseSize

def normwiseBackwardErrorType :=
  ∀ {X : Type u} {Y : Type v} [NormedAddCommGroup X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X), ℝ≥0∞

def relativeNormwiseBackwardError {X : Type u} {Y : Type v} [NormedAddCommGroup X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) (inputScale : ℝ≥0) (hscale : inputScale ≠ 0) : ℝ≥0∞ :=
  backwardError f x yhat D (relativeNormwiseSize inputScale hscale)

def relativeNormwiseBackwardErrorType :=
  ∀ {X : Type u} {Y : Type v} [NormedAddCommGroup X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) (inputScale : ℝ≥0) (hscale : inputScale ≠ 0), ℝ≥0∞

def componentwiseBackwardError {I : Type u} {K : Type v} {Y : Type w} [NormedAddCommGroup K] {U : Set (I → K)} (f : U → Y) (x : U) (yhat : Y) (D : Set (I → K)) (scale : I → ℝ≥0) : ℝ≥0∞ :=
  backwardError f x yhat D (componentwiseSize scale)

def componentwiseBackwardErrorType :=
  ∀ {I : Type u} {K : Type v} {Y : Type w} [NormedAddCommGroup K] {U : Set (I → K)} (f : U → Y) (x : U) (yhat : Y) (D : Set (I → K)) (scale : I → ℝ≥0), ℝ≥0∞

def backwardError_le_of_feasibleStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [Add X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) (size : X → ℝ≥0∞) (v : X),
    feasiblePerturbation f x yhat D v → backwardError f x yhat D size ≤ size v

def backwardError_eq_top_of_infeasibleStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [Add X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) (size : X → ℝ≥0∞),
    (¬ ∃ v, feasiblePerturbation f x yhat D v) → backwardError f x yhat D size = ⊤

def certificate_bounds_backwardErrorStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [Add X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) (size : X → ℝ≥0∞) (v : X) (bound : ℝ≥0),
    isBackwardCertificate f x yhat D size v bound →
      backwardError f x yhat D size ≤ (bound : ℝ≥0∞)

def exists_feasible_size_ltStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [Add X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) (size : X → ℝ≥0∞) (b : ℝ≥0∞),
    backwardError f x yhat D size < b →
      ∃ v, feasiblePerturbation f x yhat D v ∧ size v < b

def exists_near_feasible_sizeStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [Add X] {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X) (size : X → ℝ≥0∞),
    backwardError f x yhat D size ≠ ⊤ →
      ∀ ε : ℝ≥0, 0 < ε → ∃ v, feasiblePerturbation f x yhat D v ∧
        size v < backwardError f x yhat D size + (ε : ℝ≥0∞)

def componentwiseSize_le_iffStatement : Prop :=
  ∀ {I : Type u} {K : Type v} [NormedAddCommGroup K]
    (scale : I → ℝ≥0) (v : I → K) (bound : ℝ≥0),
    componentwiseSize scale v ≤ (bound : ℝ≥0∞) ↔
      ∀ i, ‖v i‖₊ ≤ bound * scale i

def componentwiseSize_zero_scaleStatement : Prop :=
  ∀ {I : Type u} {K : Type v} [NormedAddCommGroup K]
    (scale : I → ℝ≥0) (v : I → K) (i : I),
    scale i = 0 → v i ≠ 0 → componentwiseSize scale v = ⊤

end Specs.NumAnalysis206.Conditioning.Errors
