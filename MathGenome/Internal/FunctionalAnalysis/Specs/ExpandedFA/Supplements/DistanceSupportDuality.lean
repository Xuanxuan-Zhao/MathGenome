import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Data.EReal.Operations

/-! Independent statements for paper.tex:6082–6121.
The support function and dual supremum take values in `EReal`, so unbounded
sets are included. Convexity is real convexity in both scalar cases.
No completeness, nearest point, or norm attainment is assumed.
-/
namespace ExpandedFA.Supplements.DistanceSupportDuality.Spec
universe u v

def SupportFunctionType :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Set E → (E →L[𝕜] 𝕜) → EReal

noncomputable def SupportFunctionValue : SupportFunctionType :=
  fun K f => ⨆ k ∈ K, (RCLike.re (f k) : EReal)

def SupportNotBot : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : Set E), K.Nonempty → ∀ f : E →L[𝕜] 𝕜,
    SupportFunctionValue K f ≠ ⊥

def InfiniteSupportTerm : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : Set E) (f : E →L[𝕜] 𝕜), SupportFunctionValue K f = ⊤ →
    ∀ x, (RCLike.re (f x) : EReal) - SupportFunctionValue K f = ⊥

def RealDistanceSupport : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E), K.Nonempty → IsClosed K → Convex ℝ K → ∀ x : E,
    (Metric.infDist x K : EReal) =
      ⨆ (f : E →L[ℝ] ℝ) (_ : ‖f‖ ≤ 1),
        (f x : EReal) - SupportFunctionValue K f

def ComplexDistanceSupport : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : Set E), K.Nonempty → IsClosed K → Convex ℝ K → ∀ x : E,
    (Metric.infDist x K : EReal) =
      ⨆ (f : E →L[ℂ] ℂ) (_ : ‖f‖ ≤ 1),
        ((f x).re : EReal) - SupportFunctionValue K f

/-- Every continuous real functional is the real part of exactly one
continuous complex-linear functional, with the displayed formula and norm. -/
def ComplexRealification : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : E →L[ℝ] ℝ), ∃ f : E →L[ℂ] ℂ,
    (∀ x, f x = (h x : ℂ) - Complex.I * (h (Complex.I • x) : ℂ)) ∧
    (∀ x, (f x).re = h x) ∧ ‖f‖ = ‖h‖ ∧
    (∀ g : E →L[ℂ] ℂ, (∀ x, (g x).re = h x) → g = f)

end ExpandedFA.Supplements.DistanceSupportDuality.Spec
