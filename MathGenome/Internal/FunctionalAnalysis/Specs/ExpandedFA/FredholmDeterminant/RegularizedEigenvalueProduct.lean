import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.ClassicalLogDerivative
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.KernelSpectralBridge
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.Lidskii
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! The adopted source, fa2:p2:classical-fredholm-eigenvalues.
The index type is the full nonzero algebraic eigenvalue multiset, with no
ordering, trace-class, full-support, nonempty-space, or nonzero-mass premise.
Products are nets over all finite submultisets; this is stronger than convergence
along any exhaustive enumeration. The shared operator is the actual L² kernel
operator, not an operator selected to satisfy a spectral certificate. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
universe u
namespace ExpandedFA.FredholmDeterminant.RegularizedEigenvalueProduct.Spec
open TraceIdeals.Lidskii.Spec
open IntegralOperators.ContinuousTraceDiagonal.Spec
open ClassicalDefinitions.Spec

namespace Data
/-- The genus-one elementary factor with the sign convention I-zK. -/
def factor (w : ℂ) : ℂ := (1 - w) * Complex.exp w

/-- The product indexed by every algebraic occurrence of the nonzero spectrum. -/
def product {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (z : ℂ) : ℂ :=
  ∏' i : EigenvalueIndex T, factor (z * eigenvalue T i)
end Data
open Data

def SquareSummability : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)),
    Summable (fun i : EigenvalueIndex (continuousKernelOperator μ k) =>
      ‖eigenvalue (continuousKernelOperator μ k) i‖ ^ 2)

def UniformProduct : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (R : ℝ), 0 ≤ R →
    TendstoUniformlyOn
      (fun s : Finset (EigenvalueIndex (continuousKernelOperator μ k)) => fun z : ℂ =>
        ∏ i ∈ s, factor (z * eigenvalue (continuousKernelOperator μ k) i))
      (product (continuousKernelOperator μ k)) atTop (Metric.closedBall 0 R)

def EntireProduct : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)),
    Differentiable ℂ (product (continuousKernelOperator μ k))

/-- Convergence to the prescribed determinant, rather than only equality of
possibly totalized infinite products. -/
def ProductFormula : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ),
    HasProd (fun i : EigenvalueIndex (continuousKernelOperator μ k) =>
      factor (z * eigenvalue (continuousKernelOperator μ k) i))
      (Complex.exp (z * ∫ t, k (t,t) ∂μ) * FredholmDeterminantValue μ k z)

def DeterminantFormula : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ),
    FredholmDeterminantValue μ k z =
      Complex.exp (-z * ∫ t, k (t,t) ∂μ) * product (continuousKernelOperator μ k) z

def ZerosExactly : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ),
    FredholmDeterminantValue μ k z = 0 ↔
      ∃ a : ℂ, a ≠ 0 ∧
        Module.End.HasEigenvalue (continuousKernelOperator μ k).toLinearMap a ∧ z * a = 1

/-- Actual analytic order, not just coincidence of zero sets. -/
def ZeroMultiplicities : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (a : ℂ), a ≠ 0 →
    Module.End.HasEigenvalue (continuousKernelOperator μ k).toLinearMap a →
    analyticOrderAt (FredholmDeterminantValue μ k) a⁻¹ =
      (TraceIdeals.WeylProducts.Spec.algebraicMultiplicity (continuousKernelOperator μ k) a : ℕ∞)

/-- Supporting result about the canonical product itself, independent of its
identification with the classical determinant. -/
def ProductZeroMultiplicities : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (a : ℂ), a ≠ 0 →
    Module.End.HasEigenvalue (continuousKernelOperator μ k).toLinearMap a →
    analyticOrderAt (product (continuousKernelOperator μ k)) a⁻¹ =
      (TraceIdeals.WeylProducts.Spec.algebraicMultiplicity (continuousKernelOperator μ k) a : ℕ∞)

/-- Assembly implications, separate from the unconditional main assertions. -/
def DeterminantFormulaOfProductFormula : Prop := ProductFormula.{u} → DeterminantFormula.{u}
def ZeroMultiplicitiesOfDeterminantFormula : Prop :=
  DeterminantFormula.{u} → ZeroMultiplicities.{u}

/-- Includes full generalized-eigenspace dimensions and their natural J map. -/
def SpectralComparison : Prop := KernelSpectralBridge.Spec.SpectralComparison.{u}

def FullConclusion : Prop :=
  ProductFormula.{u} ∧ DeterminantFormula.{u} ∧ UniformProduct.{u} ∧
    EntireProduct.{u} ∧ ZerosExactly.{u} ∧ ZeroMultiplicities.{u} ∧ SpectralComparison.{u}
end ExpandedFA.FredholmDeterminant.RegularizedEigenvalueProduct.Spec
