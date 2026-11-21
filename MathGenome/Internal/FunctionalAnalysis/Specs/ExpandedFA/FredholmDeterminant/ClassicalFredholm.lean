import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.ClassicalResolventIdentities

/-! The complete classical Fredholm theorem for the original continuous-kernel
series on C(Q). Finite positive Borel measures include the manuscript's Radon
measures. No full support, positive mass, or nonempty-space hypothesis is used. -/
open MeasureTheory Filter
open scoped Topology
universe u
namespace ExpandedFA.FredholmDeterminant.ClassicalFredholm.Spec
open ClassicalDefinitions.Spec ClassicalEntireSeries.Spec.Data

def Invertibility : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ),
    IsUnit (1 - z • KernelOperatorValue μ k) ↔ FredholmDeterminantValue μ k z ≠ 0

def InverseFormula : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ),
    FredholmDeterminantValue μ k z ≠ 0 → ∀ (f : C(Q, ℂ)) (x : Q),
    (Ring.inverse (1 - z • KernelOperatorValue μ k) f) x =
      f x + (z / FredholmDeterminantValue μ k z) *
        ∫ y, FredholmMinorValue μ k x y z * f y ∂μ

/-- No finite accumulation of exceptional parameters, including at ordinary parameters. -/
def ExceptionalDiscrete : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ),
    ∀ᶠ w in 𝓝[≠] z, FredholmDeterminantValue μ k w ≠ 0

def ExceptionalEigenvalues : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ),
    FredholmDeterminantValue μ k z = 0 ↔
      z ≠ 0 ∧ ∃ f : C(Q, ℂ), f ≠ 0 ∧ KernelOperatorValue μ k f = z⁻¹ • f

def FullTheorem : Prop :=
  ClassicalEntireSeries.Spec.EntireFunctions.{u} ∧
  ClassicalEntireSeries.Spec.ValuesAtZero.{u} ∧
  ClassicalEntireSeries.Spec.MinorKernelIdentification.{u} ∧
  ClassicalResolventIdentities.Spec.KernelIdentities.{u} ∧
  ClassicalResolventIdentities.Spec.DiagonalDerivative.{u} ∧
  Invertibility.{u} ∧ InverseFormula.{u} ∧ ExceptionalDiscrete.{u} ∧ ExceptionalEigenvalues.{u}

end ExpandedFA.FredholmDeterminant.ClassicalFredholm.Spec
