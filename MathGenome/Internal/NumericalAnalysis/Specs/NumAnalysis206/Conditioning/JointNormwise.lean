import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Basic.ENNReal.Inv

/-! Independent specification for the normwise assertion of W15, paper.tex 499–534.
Continuous linear maps carry the subordinate operator norm. The statement holds
on arbitrary normed real/complex spaces, hence includes every finite dimensional
system, zero dimensional spaces, and arbitrary vector norms. No invertibility
or rank hypothesis is imposed. Budgets and scales are finite nonnegative reals;
the infimum is taken in the extended nonnegative reals, including the empty set.
ENNReal division gives 0/0 = 0 and positive/0 = infinity. -/

open scoped NNReal ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false
universe u v w
namespace Specs.NumAnalysis206.Conditioning.JointNormwise

def jointNormwiseFeasible {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (A : X →L[𝕜] Y) (b : Y) (xhat : X) (α β : ℝ≥0) (ε : ℝ≥0) : Prop :=
  ∃ (ΔA : X →L[𝕜] Y) (Δb : Y),
    (A + ΔA) xhat = b + Δb ∧ ‖ΔA‖₊ ≤ ε * α ∧ ‖Δb‖₊ ≤ ε * β

def jointNormwiseFeasibleType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (A : X →L[𝕜] Y) (b : Y) (xhat : X) (α β : ℝ≥0) (ε : ℝ≥0), Prop

def jointNormwiseBackwardError {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (A : X →L[𝕜] Y) (b : Y) (xhat : X) (α β : ℝ≥0) : ℝ≥0∞ :=
  sInf {t | ∃ ε : ℝ≥0, jointNormwiseFeasible A b xhat α β ε ∧ (ε : ℝ≥0∞) = t}

def jointNormwiseBackwardErrorType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (A : X →L[𝕜] Y) (b : Y) (xhat : X) (α β : ℝ≥0), ℝ≥0∞

def jointNormwiseFeasible_iffStatement : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (A : X →L[𝕜] Y) (b : Y) (xhat : X) (α β : ℝ≥0) (ε : ℝ≥0),
    jointNormwiseFeasible A b xhat α β ε ↔
      ‖b - A xhat‖₊ ≤ ε * (α * ‖xhat‖₊ + β)

def jointNormwiseBackwardError_formulaStatement : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (A : X →L[𝕜] Y) (b : Y) (xhat : X) (α β : ℝ≥0),
    jointNormwiseBackwardError A b xhat α β =
      (‖b - A xhat‖₊ : ℝ≥0∞) / ((α * ‖xhat‖₊ + β : ℝ≥0) : ℝ≥0∞)

def jointNormwiseBackwardError_attainedStatement : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (A : X →L[𝕜] Y) (b : Y) (xhat : X) (α β : ℝ≥0),
    jointNormwiseBackwardError A b xhat α β ≠ ⊤ →
      ∃ ε : ℝ≥0, (ε : ℝ≥0∞) = jointNormwiseBackwardError A b xhat α β ∧
        jointNormwiseFeasible A b xhat α β ε

end Specs.NumAnalysis206.Conditioning.JointNormwise
