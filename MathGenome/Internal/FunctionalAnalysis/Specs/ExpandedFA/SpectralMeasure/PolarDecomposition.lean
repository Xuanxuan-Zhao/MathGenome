import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Polar decomposition, paper.tex 12490–12511. All spaces are complete,
but no separability, injectivity, or closed-range assumption is imposed.
The explicit real-coefficient square-root series works over either scalar field.
Partial isometries preserve norms on the orthogonal complement of their kernel.
Their final space is their (closed) range. -/
noncomputable section
namespace ExpandedFA.SpectralMeasure.PolarDecomposition.Spec
universe u v w

def rootCoeff (n : ℕ) : ℝ := (catalan n : ℝ) / (2 * 4 ^ n)

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} {K : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- The binomial series, including the closed norm boundary and zero operator. -/
def positiveSqrtValue (A : H →L[𝕜] H) : H →L[𝕜] H :=
  (Real.sqrt ‖A‖ : 𝕜) •
    (1 - ∑' n, (rootCoeff n : 𝕜) •
      (1 - ((‖A‖⁻¹ : ℝ) : 𝕜) • A) ^ (n + 1))

def modulusValue (T : H →L[𝕜] K) : H →L[𝕜] H :=
  positiveSqrtValue (T.adjoint.comp T)

def IsPartialIsometryValue (U : H →L[𝕜] K) : Prop :=
  ∀ x ∈ U.ker.orthogonal, ‖U x‖ = ‖x‖

def IsPolarFactorValue (T U : H →L[𝕜] K) : Prop :=
  U.ker = T.ker ∧ IsPartialIsometryValue U ∧
    U.range = T.range.topologicalClosure ∧ U.comp (modulusValue T) = T

/-- The source's |T| really is the unique positive square root of T* T. -/
def ModulusProperties : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (T : H →L[𝕜] K),
    (modulusValue T).IsPositive ∧
    (modulusValue T).comp (modulusValue T) = T.adjoint.comp T ∧
    ∀ S : H →L[𝕜] H, S.IsPositive → S.comp S = T.adjoint.comp T →
      S = modulusValue T

def PolarDecomposition : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (T : H →L[𝕜] K), ∃! U : H →L[𝕜] K, IsPolarFactorValue T U

def NormalCommutation : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H), IsStarNormal T →
    ∀ U : H →L[𝕜] H, IsPolarFactorValue T U →
      Commute T (modulusValue T) ∧ Commute T U

/-- For different spaces, unitarity is a surjective linear isometry. -/
def InvertibleUnitary : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (T : H ≃L[𝕜] K) (U : H →L[𝕜] K),
    IsPolarFactorValue T.toContinuousLinearMap U →
      ∃ e : H ≃ₗᵢ[𝕜] K, e.toLinearIsometry.toContinuousLinearMap = U

def NonunitaryExample : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ T U : 𝕜 →L[𝕜] 𝕜, IsPolarFactorValue T U ∧
      ¬ ∃ e : 𝕜 ≃ₗᵢ[𝕜] 𝕜, e.toLinearIsometry.toContinuousLinearMap = U

end ExpandedFA.SpectralMeasure.PolarDecomposition.Spec
