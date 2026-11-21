import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03Neumann
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
Independent specification of the full quantitative perturbation theorem
`fa2:p1:c03:perturbation`, paper.tex 716–729, including openness and
continuity of inversion.

The initial inverse is supplied as a continuous linear map with both inverse
identities. This expresses a bounded bijection with an explicitly bounded
inverse, without using the bounded inverse theorem. Norms, infinite sums,
and convergence are those of the native operator spaces. No space is assumed
nonzero; in particular their identities can have norm zero.
-/

open Filter
open scoped Topology

namespace ExpandedFA.P1.C03Perturbation.Spec

universe u v w

/-- The two-sided bounded inverse of A + H, its operator-norm series, and
both sharp geometric majorants. `HasSum` gives the series in operator norm;
the explicit limit records the ordered partial sums through exponent N. -/
def QuantitativePerturbation : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F]
    (A : E →L[𝕜] F) (Ainv : F →L[𝕜] E),
    A.comp Ainv = ContinuousLinearMap.id 𝕜 F →
    Ainv.comp A = ContinuousLinearMap.id 𝕜 E →
    ∀ H : E →L[𝕜] F, ‖Ainv.comp H‖ < 1 →
    ∃ R : F →L[𝕜] E,
      (A + H).comp R = ContinuousLinearMap.id 𝕜 F ∧
      R.comp (A + H) = ContinuousLinearMap.id 𝕜 E ∧
      HasSum (fun n : ℕ => ((-Ainv.comp H) ^ n).comp Ainv) R ∧
      R = ∑' n : ℕ, ((-Ainv.comp H) ^ n).comp Ainv ∧
      Tendsto (fun N : ℕ =>
        ∑ n ∈ Finset.range (N + 1), ((-Ainv.comp H) ^ n).comp Ainv)
        atTop (𝓝 R) ∧
      ‖R‖ ≤ ‖Ainv‖ / (1 - ‖Ainv.comp H‖) ∧
      ‖R - Ainv‖ ≤ ‖Ainv.comp H‖ * ‖Ainv‖ / (1 - ‖Ainv.comp H‖)

/-- Native bounded invertibility is exactly the existence of a bounded
two-sided inverse; this also includes zero spaces. -/
def InvertibilityIdentification : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (A : E →L[𝕜] F),
    A.IsInvertible ↔ ∃ R : F →L[𝕜] E,
      A.comp R = ContinuousLinearMap.id 𝕜 F ∧
      R.comp A = ContinuousLinearMap.id 𝕜 E

/-- The quantitative conclusion, now stated for the actual inverse function. -/
def InversePerturbation : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F]
    (A : E →L[𝕜] F), A.IsInvertible →
    ∀ H : E →L[𝕜] F, ‖A.inverse.comp H‖ < 1 →
      (A + H).IsInvertible ∧
      HasSum (fun n : ℕ => ((-A.inverse.comp H) ^ n).comp A.inverse)
        (A + H).inverse ∧
      (A + H).inverse = ∑' n : ℕ, ((-A.inverse.comp H) ^ n).comp A.inverse ∧
      Tendsto (fun N : ℕ =>
        ∑ n ∈ Finset.range (N + 1), ((-A.inverse.comp H) ^ n).comp A.inverse)
        atTop (𝓝 (A + H).inverse) ∧
      ‖(A + H).inverse‖ ≤ ‖A.inverse‖ / (1 - ‖A.inverse.comp H‖) ∧
      ‖(A + H).inverse - A.inverse‖ ≤
        ‖A.inverse.comp H‖ * ‖A.inverse‖ / (1 - ‖A.inverse.comp H‖)

def InvertibleOpen : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F],
    IsOpen {A : E →L[𝕜] F | A.IsInvertible}

def InverseContinuous : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F],
    ContinuousOn (ContinuousLinearMap.inverse : (E →L[𝕜] F) → (F →L[𝕜] E))
      {A | A.IsInvertible}

/-- The full manuscript theorem is retained in this final module. -/
def PerturbationTheorem : Prop :=
  InversePerturbation.{u, v, w} ∧ InvertibleOpen.{u, v, w} ∧
    InverseContinuous.{u, v, w}

end ExpandedFA.P1.C03Perturbation.Spec
