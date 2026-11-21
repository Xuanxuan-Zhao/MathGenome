import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.ClassicalProduct
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.ContinuousTraceDiagonal
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.TraceClassDefinitions
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Remaining statements of `fa2:p2:classical-fredholm-product`.
The index n below represents the positive power j = n + 1. The measure is
finite positive Borel on a compact metric space, hence covers the source's
finite Radon measures. No full support, symmetry, or positivity of k is assumed.
The logarithm is the principal logarithm, which is the branch equal to zero
at D(0)=1 on a sufficiently small disk. -/
noncomputable section
open MeasureTheory
universe u
namespace ExpandedFA.FredholmDeterminant.ClassicalLogDerivative.Spec
open ClassicalDefinitions.Spec
open ClassicalProduct.Spec.Data
open IntegralOperators.ContinuousTraceDiagonal.Spec
open TraceIdeals.TraceClassDefinitions.Spec

namespace Data
/-- The continuous kernel of K^(n+1); no continuous kernel for the identity
operator is asserted. -/
def iteratedKernel {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] (μ : Measure Q) (k : C(Q × Q, ℂ)) : ℕ → C(Q × Q, ℂ)
  | 0 => k
  | n + 1 => compositionKernel μ k (iteratedKernel μ k n)

/-- The source's c_(n+1), using its actual continuous iterated kernel. -/
def diagonalCoefficient {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] (μ : Measure Q) (k : C(Q × Q, ℂ)) (n : ℕ) : ℂ :=
  ∫ t, iteratedKernel μ k n (t, t) ∂μ
end Data
open Data

/-- The logarithmic formula includes convergence, not just equality of tsums. -/
def LogarithmicSeries : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)),
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      HasSum (fun n : ℕ => -(z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) *
        diagonalCoefficient μ k n)) (Complex.log (FredholmDeterminantValue μ k z))

/-- Every positive iterate is the power of the canonical L² operator. -/
def IteratedOperator : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (n : ℕ),
    continuousKernelOperator μ (iteratedKernel μ k n) =
      continuousKernelOperator μ k ^ (n + 1)

/-- The full positive-power trace conclusion. -/
def TracePowerCoefficients : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)),
    IsTraceClassValue (continuousKernelOperator μ k) → ∀ n : ℕ,
      IsTraceClassValue (continuousKernelOperator μ k ^ (n + 1)) ∧
      diagonalCoefficient μ k n = TraceValue (continuousKernelOperator μ k ^ (n + 1))

/-- The upstream trace determinant uses I+wK, so w=-z gives I-zK. -/
def TraceDeterminantComparison : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)),
    IsTraceClassValue (continuousKernelOperator μ k) → ∀ z : ℂ,
      FredholmDeterminantValue μ k z =
        TraceClassDefinitions.Spec.FredholmDeterminantValue (continuousKernelOperator μ k) (-z)

/-- All clauses of the source theorem, including the multiplication stage
already allocated to ClassicalProduct. -/
def MultiplicationAndLogarithmicDerivative : Prop :=
  ClassicalProduct.Spec.UniformKernelContinuity.{u} ∧
  ClassicalProduct.Spec.LocallyUniformKernelLimit.{u} ∧
  ClassicalProduct.Spec.Multiplication.{u} ∧
  ClassicalProduct.Spec.ScalarMultiplication.{u} ∧
  LogarithmicSeries.{u} ∧ TracePowerCoefficients.{u} ∧ TraceDeterminantComparison.{u}

end ExpandedFA.FredholmDeterminant.ClassicalLogDerivative.Spec
