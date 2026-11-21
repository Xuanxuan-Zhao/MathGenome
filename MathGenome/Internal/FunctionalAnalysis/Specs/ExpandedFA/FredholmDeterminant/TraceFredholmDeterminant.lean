import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.TraceDeterminantContinuity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.Lidskii
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-! The remaining Fredholm determinant theorem, paper.tex:11582–11645.
The determinant remains the upstream exterior series. The product is over
all actual nonzero eigenvalues, repeated by the dimension of their full
generalized eigenspace. Neither normality nor separability is assumed. -/
noncomputable section
universe u w
namespace ExpandedFA.FredholmDeterminant.TraceFredholmDeterminant.Spec
open TraceClassDefinitions.Spec TraceIdeals.TraceClassDefinitions.Spec
open TraceIdeals.Lidskii.Spec Filter
open scoped Topology

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- An unordered product retains each algebraic occurrence, including finite
and empty spectra. It is independent of any ordering of the eigenvalues. -/
def EigenvalueProductValue (T : H →L[ℂ] H) (z : ℂ) : ℂ :=
  ∏' i : EigenvalueIndex T, (1 + z * eigenvalue T i)

/-- The coefficient is the canonical trace of the actual completed exterior
operator, as in the manuscript, rather than merely a principal-minor sum. -/
def ExteriorSeriesFormula : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), IsTraceClassValue T → ∀ z : ℂ,
    HasSum (fun n : ℕ => z ^ n * TraceValue (ExteriorOperatorValue T n))
      (FredholmDeterminantValue T z)

/-- Equality with the exterior-series determinant, with convergence rather
than just an equality of the totalized `tprod` and `tsum`. -/
def ProductFormula : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), IsTraceClassValue T → ∀ z : ℂ,
    HasProd (fun i : EigenvalueIndex T => 1 + z * eigenvalue T i)
      (FredholmDeterminantValue T z)

/-- Uniform convergence of the net of finite products on every bounded
parameter disk. In particular every exhaustive enumeration converges
locally uniformly and keeps all algebraic multiplicities. -/
def UniformEigenvalueProduct : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), IsTraceClassValue T → ∀ R : ℝ, 0 ≤ R →
    TendstoUniformlyOn
      (fun s : Finset (EigenvalueIndex T) => fun z : ℂ =>
        ∏ i ∈ s, (1 + z * eigenvalue T i))
      (EigenvalueProductValue T) atTop (Metric.closedBall 0 R)

def EntireEigenvalueProduct : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), IsTraceClassValue T →
      Differentiable ℂ (EigenvalueProductValue T)

/-- Nonvanishing of the determinant is precisely bounded invertibility in
the unital algebra of continuous linear endomorphisms, including H = 0. -/
def NonvanishingIffInvertible : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), IsTraceClassValue T → ∀ z : ℂ,
    FredholmDeterminantValue T z ≠ 0 ↔
      IsUnit (ContinuousLinearMap.id ℂ H + z • T)

/-- The root condition is stated using actual eigenvectors, so zero does
not appear as a spurious root when the nonzero spectrum is empty. -/
def ZerosExactly : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), IsTraceClassValue T → ∀ z : ℂ,
    FredholmDeterminantValue T z = 0 ↔
      ∃ μ : ℂ, μ ≠ 0 ∧ Module.End.HasEigenvalue T.toLinearMap μ ∧ 1 + z * μ = 0

/-- The complete source conclusion. Entirety, the exterior expansion,
trace-norm continuity, and multiplicativity use the unchanged upstream
objects; the remaining conjuncts identify the convergent spectral product
and its zeros. -/
def FredholmDeterminantTheorem : Prop :=
  TraceDeterminantContinuity.Spec.EntireExteriorSeries.{u} ∧
  TraceDeterminantContinuity.Spec.UniformExteriorSeries.{u} ∧
  TraceDeterminantContinuity.Spec.TraceNormLocallyUniform.{u,w} ∧
  TraceDeterminantContinuity.Spec.DeterminantMultiplicative.{u} ∧
  ExteriorSeriesFormula.{u} ∧ ProductFormula.{u} ∧ UniformEigenvalueProduct.{u} ∧
  EntireEigenvalueProduct.{u} ∧
  NonvanishingIffInvertible.{u} ∧ ZerosExactly.{u}

end ExpandedFA.FredholmDeterminant.TraceFredholmDeterminant.Spec
