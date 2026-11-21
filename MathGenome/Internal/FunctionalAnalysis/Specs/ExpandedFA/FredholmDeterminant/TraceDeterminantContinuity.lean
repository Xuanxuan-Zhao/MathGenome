import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.TraceClassDefinitions
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! The analytic and continuity stage of the Fredholm determinant theorem.
All objects are the shared exterior-series objects, on arbitrary complete
complex Hilbert spaces, without a dimension or separability assumption. -/
noncomputable section
universe v w
namespace ExpandedFA.FredholmDeterminant.TraceDeterminantContinuity.Spec
open TraceClassDefinitions.Spec TraceIdeals.TraceClassDefinitions.Spec
open Filter
open scoped Topology

/-- Absolute convergence and holomorphy on the whole complex plane. -/
def EntireExteriorSeries : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), IsTraceClassValue T →
    (∀ z : ℂ, Summable (fun n : ℕ => ‖z ^ n * ExteriorTraceValue T n‖)) ∧
    Differentiable ℂ (FredholmDeterminantValue T)

/-- The exterior series converges uniformly on every bounded parameter disk. -/
def UniformExteriorSeries : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), IsTraceClassValue T → ∀ R : ℝ, 0 ≤ R →
    TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ => ∑ n ∈ Finset.range N, z ^ n * ExteriorTraceValue T n)
      (FredholmDeterminantValue T) atTop (Metric.closedBall 0 R)

/-- The bound concerns the canonical trace norm of the actual completed
exterior operator, rather than only the modulus of its trace. -/
def ExteriorTraceNormBound : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), IsTraceClassValue T → ∀ n : ℕ,
    IsTraceClassValue (ExteriorOperatorValue T n) ∧
    TraceNormValue (ExteriorOperatorValue T n) ≤ TraceNormValue T ^ n / (n.factorial : ℝ)

/-- The sharp quantitative continuity estimate at parameter one. -/
def DeterminantPerturbationBound : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S T : H →L[ℂ] H), IsTraceClassValue S → IsTraceClassValue T →
    ‖FredholmDeterminantValue T 1 - FredholmDeterminantValue S 1‖ ≤
      TraceNormValue (T - S) * Real.exp (max (TraceNormValue T) (TraceNormValue S))

/-- Parameter-dependent version used for uniform convergence on disks. -/
def ParameterPerturbationBound : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S T : H →L[ℂ] H), IsTraceClassValue S → IsTraceClassValue T → ∀ z : ℂ,
    ‖FredholmDeterminantValue T z - FredholmDeterminantValue S z‖ ≤
      ‖z‖ * TraceNormValue (T - S) *
        Real.exp (‖z‖ * max (TraceNormValue T) (TraceNormValue S))

/-- Trace-norm convergence gives uniform determinant convergence on each
closed disk, hence locally uniform convergence in the complex parameter. -/
def TraceNormLocallyUniform : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {I : Type w} (l : Filter I) (T : I → H →L[ℂ] H) (L : H →L[ℂ] H),
    (∀ n, IsTraceClassValue (T n)) → IsTraceClassValue L →
    Tendsto (fun n => TraceNormValue (T n - L)) l (𝓝 0) →
    ∀ R : ℝ, 0 ≤ R → TendstoUniformlyOn
      (fun n => FredholmDeterminantValue (T n)) (FredholmDeterminantValue L)
      l (Metric.closedBall 0 R)

/-- `(I+S)(I+T)=I+(S+T+ST)`; composition order is explicit. -/
def DeterminantMultiplicative : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S T : H →L[ℂ] H), IsTraceClassValue S → IsTraceClassValue T →
    IsTraceClassValue (S + T + S.comp T) ∧
    FredholmDeterminantValue (S + T + S.comp T) 1 =
      FredholmDeterminantValue S 1 * FredholmDeterminantValue T 1

end ExpandedFA.FredholmDeterminant.TraceDeterminantContinuity.Spec
