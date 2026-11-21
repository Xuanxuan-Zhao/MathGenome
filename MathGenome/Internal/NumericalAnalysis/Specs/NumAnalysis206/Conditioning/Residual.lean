import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.Errors
import Mathlib.Analysis.Normed.Operator.Basic

/-! Independent specification of paper.tex W14, including the chapter's subordinate
operator-norm convention. A continuous linear equivalence is precisely a linear
bijection with continuous forward and inverse maps. No completeness or finite
dimensionality is needed. The scalar field includes both ℝ and ℂ.
The b-only model is the solution map b ↦ A⁻¹b on the whole right-hand-side space,
with all additive perturbations admissible, using the W12 normwise size. -/

open scoped NNReal ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false
universe u v w

namespace Specs.NumAnalysis206.Conditioning.Residual

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]

def linearResidual (A : X ≃L[𝕜] Y) (b : Y) (xhat : X) : Y := b - A xhat

def linearConditionNumber (A : X ≃L[𝕜] Y) : ℝ :=
  ‖A.toContinuousLinearMap‖ * ‖A.symm.toContinuousLinearMap‖

def rightHandSideSolution (A : X ≃L[𝕜] Y) : ↥(Set.univ : Set Y) → X :=
  fun b => A.symm b.val

def linearResidualType :=
  ∀ {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (A : X ≃L[𝕜] Y) (b : Y) (xhat : X), Y

def linearConditionNumberType :=
  ∀ {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (A : X ≃L[𝕜] Y), ℝ

def rightHandSideSolutionType :=
  ∀ {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (A : X ≃L[𝕜] Y), ↥(Set.univ : Set Y) → X

def residual_absolute_boundStatement : Prop :=
  ∀ {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (A : X ≃L[𝕜] Y) (x xhat : X) (b : Y), A x = b →
    ‖xhat - x‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖linearResidual A b xhat‖

def residual_relative_boundStatement : Prop :=
  ∀ {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (A : X ≃L[𝕜] Y) (x xhat : X) (b : Y), A x = b → b ≠ 0 →
    ‖xhat - x‖ / ‖x‖ ≤ linearConditionNumber A * ‖linearResidual A b xhat‖ / ‖b‖

def rightHandSide_feasible_iffStatement : Prop :=
  ∀ {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (A : X ≃L[𝕜] Y) (b : Y) (xhat : X) (δb : Y),
    Errors.feasiblePerturbation (rightHandSideSolution A) ⟨b, Set.mem_univ b⟩ xhat
      Set.univ δb ↔ δb = -linearResidual A b xhat

def rightHandSide_backwardError_eqStatement : Prop :=
  ∀ {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (A : X ≃L[𝕜] Y) (b : Y) (xhat : X),
    Errors.normwiseBackwardError (rightHandSideSolution A) ⟨b, Set.mem_univ b⟩
      xhat Set.univ = (‖linearResidual A b xhat‖₊ : ℝ≥0∞)

def rightHandSide_backwardError_attainedStatement : Prop :=
  ∀ {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (A : X ≃L[𝕜] Y) (b : Y) (xhat : X),
    Errors.isBackwardCertificate (rightHandSideSolution A) ⟨b, Set.mem_univ b⟩
      xhat Set.univ Errors.normwiseSize (-linearResidual A b xhat)
      ‖linearResidual A b xhat‖₊ ∧
    Errors.normwiseSize (-linearResidual A b xhat) =
      Errors.normwiseBackwardError (rightHandSideSolution A) ⟨b, Set.mem_univ b⟩
        xhat Set.univ

end Specs.NumAnalysis206.Conditioning.Residual
