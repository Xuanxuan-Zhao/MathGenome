import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.RealExteriorDefinitions
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! Analytic and continuity properties of the genuine real Fredholm determinant.
All operators and trace norms are on the original real Hilbert space. -/
noncomputable section
universe v w
namespace ExpandedFA.FredholmDeterminant.RealTraceDeterminantContinuity.Spec
open RealExteriorDefinitions.Spec TraceIdeals.TraceClassDefinitions.Spec
open Filter
open scoped Topology

/-- Absolute convergence of the real exterior series and its entire extension. -/
def EntireExteriorSeries : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), IsTraceClassValue T →
    (∀ z : ℂ, Summable (fun n : ℕ => ‖z ^ n * (RealExteriorTraceValue T n : ℂ)‖)) ∧
    Differentiable ℂ (ComplexParameterDeterminantValue T)

/-- Uniform convergence of exterior partial sums on every closed complex disk. -/
def UniformExteriorSeries : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), IsTraceClassValue T → ∀ R : ℝ, 0 ≤ R →
    TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ => ∑ n ∈ Finset.range N,
        z ^ n * (RealExteriorTraceValue T n : ℂ))
      (ComplexParameterDeterminantValue T) atTop (Metric.closedBall 0 R)

/-- Sharp perturbation estimate, with the original real trace norm. -/
def ParameterPerturbationBound : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S T : H →L[ℝ] H), IsTraceClassValue S → IsTraceClassValue T → ∀ z : ℂ,
    ‖ComplexParameterDeterminantValue T z - ComplexParameterDeterminantValue S z‖ ≤
      ‖z‖ * TraceNormValue (T - S) *
        Real.exp (‖z‖ * max (TraceNormValue T) (TraceNormValue S))

/-- The original real determinant estimate at one. -/
def DeterminantPerturbationBound : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S T : H →L[ℝ] H), IsTraceClassValue S → IsTraceClassValue T →
    ‖RealDeterminantValue T 1 - RealDeterminantValue S 1‖ ≤
      TraceNormValue (T - S) * Real.exp (max (TraceNormValue T) (TraceNormValue S))

/-- Arbitrary filters, including the bottom filter, are allowed. -/
def TraceNormLocallyUniform : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {I : Type w} (l : Filter I) (T : I → H →L[ℝ] H) (L : H →L[ℝ] H),
    (∀ i, IsTraceClassValue (T i)) → IsTraceClassValue L →
    Tendsto (fun i => TraceNormValue (T i - L)) l (𝓝 0) →
    (∀ R : ℝ, 0 ≤ R → TendstoUniformlyOn
      (fun i => ComplexParameterDeterminantValue (T i)) (ComplexParameterDeterminantValue L)
      l (Metric.closedBall 0 R)) ∧
    TendstoLocallyUniformly (fun i => ComplexParameterDeterminantValue (T i))
      (ComplexParameterDeterminantValue L) l

/-- The corresponding actual real determinants converge locally uniformly. -/
def RealTraceNormLocallyUniform : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {I : Type w} (l : Filter I) (T : I → H →L[ℝ] H) (L : H →L[ℝ] H),
    (∀ i, IsTraceClassValue (T i)) → IsTraceClassValue L →
    Tendsto (fun i => TraceNormValue (T i - L)) l (𝓝 0) →
    (∀ R : ℝ, 0 ≤ R → TendstoUniformlyOn
      (fun i => RealDeterminantValue (T i)) (RealDeterminantValue L)
      l (Metric.closedBall 0 R)) ∧
    TendstoLocallyUniformly (fun i => RealDeterminantValue (T i))
      (RealDeterminantValue L) l

/-- Composition order is fixed by the displayed identity. -/
def DeterminantMultiplicative : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S T : H →L[ℝ] H), IsTraceClassValue S → IsTraceClassValue T →
    IsTraceClassValue (S + T + S.comp T) ∧
    (ContinuousLinearMap.id ℝ H + S).comp (ContinuousLinearMap.id ℝ H + T) =
      ContinuousLinearMap.id ℝ H + (S + T + S.comp T) ∧
    RealDeterminantValue (S + T + S.comp T) 1 =
      RealDeterminantValue S 1 * RealDeterminantValue T 1

end ExpandedFA.FredholmDeterminant.RealTraceDeterminantContinuity.Spec
