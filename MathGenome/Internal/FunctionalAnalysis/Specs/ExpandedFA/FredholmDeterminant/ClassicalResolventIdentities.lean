import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.ClassicalEntireSeries
import Mathlib.MeasureTheory.Integral.Prod

/-! The identities and the inverse formula in `fa2:p2:classical-fredholm`,
paper.tex:11009–11075. We use the original determinant series and the upstream
continuous-kernel realization of its first minor. The finite Borel measure
formulation includes the finite positive Radon measures of the manuscript,
including zero measures and empty compact spaces. -/

open MeasureTheory
universe u
namespace ExpandedFA.FredholmDeterminant.ClassicalResolventIdentities.Spec

open ClassicalDefinitions.Spec ClassicalEntireSeries.Spec.Data

def KernelIdentities : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ) (x y : Q),
    FredholmMinorValue μ k x y z = FredholmDeterminantValue μ k z * k (x, y) +
      z * ∫ t, k (x, t) * FredholmMinorValue μ k t y z ∂μ ∧
    FredholmMinorValue μ k x y z = FredholmDeterminantValue μ k z * k (x, y) +
      z * ∫ t, FredholmMinorValue μ k x t z * k (t, y) ∂μ

def DiagonalDerivative : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ),
    deriv (FredholmDeterminantValue μ k) z =
      -(∫ t, FredholmMinorValue μ k t t z ∂μ)

def ResolventOperatorType :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ],
    C(Q × Q, ℂ) → ℂ → C(Q, ℂ) →L[ℂ] C(Q, ℂ)

noncomputable def ResolventOperatorValue : ResolventOperatorType.{u} :=
  fun μ _ k z => 1 + (z / FredholmDeterminantValue μ k z) •
    KernelOperatorValue μ (minorKernel μ k z)

def ResolventFormula : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ)
    (f : C(Q, ℂ)) (x : Q),
    ResolventOperatorValue μ k z f x = f x +
      (z / FredholmDeterminantValue μ k z) *
        ∫ y, FredholmMinorValue μ k x y z * f y ∂μ

/-- Both compositions equal the identity on all of C(Q), so the formula is
an actual bounded two-sided inverse. No invertibility certificate is assumed. -/
def TwoSidedInverse : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ),
    FredholmDeterminantValue μ k z ≠ 0 →
    (1 - z • KernelOperatorValue μ k).comp (ResolventOperatorValue μ k z) = 1 ∧
    (ResolventOperatorValue μ k z).comp (1 - z • KernelOperatorValue μ k) = 1

end ExpandedFA.FredholmDeterminant.ClassicalResolventIdentities.Spec
