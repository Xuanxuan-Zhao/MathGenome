import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.RealTraceDeterminantContinuity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.TraceFredholmDeterminant

/-! Real Fredholm determinants, using the genuine Hilbert complexification.
The spectral index includes every nonzero complex eigenvalue with the dimension
of its full generalized eigenspace. No separability or normality is assumed. -/
noncomputable section
universe u w
namespace ExpandedFA.FredholmDeterminant.RealTraceFredholmDeterminant.Spec
open RealExteriorDefinitions.Spec TraceIdeals.TraceClassDefinitions.Spec
open TraceIdeals.Lidskii.Spec Filter

/-- Both the shared real coefficients and the traces of the actual real
completed exterior operators give convergent series for the determinant. -/
def ExteriorSeriesFormula : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), IsTraceClassValue T → ∀ z : ℂ,
    HasSum (fun n : ℕ => z ^ n * (RealExteriorTraceValue T n : ℂ))
      (ComplexParameterDeterminantValue T z) ∧
    HasSum (fun n : ℕ => z ^ n * (TraceValue (𝕜 := ℝ) (RealExteriorOperatorValue T n) : ℂ))
      (ComplexParameterDeterminantValue T z)

def RealExteriorSeriesFormula : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), IsTraceClassValue T → ∀ r : ℝ,
    HasSum (fun n : ℕ => r ^ n * TraceValue (𝕜 := ℝ) (RealExteriorOperatorValue T n))
      (RealDeterminantValue T r)

/-- The factors range over the complex spectrum of T_C, including nonreal
eigenvalues, and retain their algebraic multiplicities. -/
def ProductFormula : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), IsTraceClassValue T → ∀ z : ℂ,
    HasProd (fun i : EigenvalueIndex (TraceIdeals.RealComplexification.Spec.operator T) =>
      1 + z * eigenvalue (TraceIdeals.RealComplexification.Spec.operator T) i)
      (ComplexParameterDeterminantValue T z)

def ProductIdentity : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), IsTraceClassValue T → ∀ z : ℂ,
    ComplexParameterDeterminantValue T z =
      ∏' i : EigenvalueIndex (TraceIdeals.RealComplexification.Spec.operator T),
        (1 + z * eigenvalue (TraceIdeals.RealComplexification.Spec.operator T) i)

/-- The unordered net of all finite products converges uniformly on every
closed complex disk, including a disk of radius zero. -/
def UniformEigenvalueProduct : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), IsTraceClassValue T → ∀ R : ℝ, 0 ≤ R →
    TendstoUniformlyOn
      (fun s : Finset (EigenvalueIndex (TraceIdeals.RealComplexification.Spec.operator T)) =>
        fun z : ℂ => ∏ i ∈ s,
          (1 + z * eigenvalue (TraceIdeals.RealComplexification.Spec.operator T) i))
      (ComplexParameterDeterminantValue T) atTop (Metric.closedBall 0 R)

/-- Bounded invertibility is expressed as being a unit in the algebra of
continuous linear endomorphisms, which also covers the zero Hilbert space. -/
def ComplexNonvanishingIffInvertible : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), IsTraceClassValue T → ∀ z : ℂ,
    ComplexParameterDeterminantValue T z ≠ 0 ↔
      IsUnit (ContinuousLinearMap.id ℂ (TraceIdeals.RealComplexification.Space H) +
        z • TraceIdeals.RealComplexification.Spec.operator T)

/-- At real parameters this is invertibility on the original real space,
rather than on all complex-valued vectors viewed as a real space. -/
def RealNonvanishingIffInvertible : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), IsTraceClassValue T → ∀ r : ℝ,
    RealDeterminantValue T r ≠ 0 ↔ IsUnit (ContinuousLinearMap.id ℝ H + r • T)

def ZerosExactly : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), IsTraceClassValue T → ∀ z : ℂ,
    ComplexParameterDeterminantValue T z = 0 ↔
      ∃ μ : ℂ, μ ≠ 0 ∧
        Module.End.HasEigenvalue (TraceIdeals.RealComplexification.Spec.operator T).toLinearMap μ ∧
        1 + z * μ = 0

/-- The full real-source theorem retains the earlier analytic, continuity,
and genuine real multiplicativity conclusions with the same objects. -/
def RealFredholmDeterminantTheorem : Prop :=
  RealExteriorDefinitions.Spec.RealExteriorConstruction.{u} ∧
  RealTraceDeterminantContinuity.Spec.EntireExteriorSeries.{u} ∧
  RealTraceDeterminantContinuity.Spec.UniformExteriorSeries.{u} ∧
  RealTraceDeterminantContinuity.Spec.TraceNormLocallyUniform.{u,w} ∧
  RealTraceDeterminantContinuity.Spec.RealTraceNormLocallyUniform.{u,w} ∧
  RealTraceDeterminantContinuity.Spec.DeterminantMultiplicative.{u} ∧
  ExteriorSeriesFormula.{u} ∧ RealExteriorSeriesFormula.{u} ∧
  ProductFormula.{u} ∧ ProductIdentity.{u} ∧ UniformEigenvalueProduct.{u} ∧
  ComplexNonvanishingIffInvertible.{u} ∧ RealNonvanishingIffInvertible.{u} ∧ ZerosExactly.{u}

/-- Together the unchanged complex theorem and its real companion cover the
manuscript's full real-or-complex scalar convention. -/
def FullScalarFredholmDeterminantTheorem : Prop :=
  TraceFredholmDeterminant.Spec.FredholmDeterminantTheorem.{u,w} ∧
    RealFredholmDeterminantTheorem.{u,w}

end ExpandedFA.FredholmDeterminant.RealTraceFredholmDeterminant.Spec
