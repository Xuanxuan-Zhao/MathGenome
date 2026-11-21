import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! Independent specification of `fa2:p3:weak-semigroup-continuity`.
Time is the nonnegative real half-line, with its usual subspace topology.
The real-time orbit below extends to negative times by the value at zero;
only nonnegative compact intervals are used in integrability claims. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology NNReal
universe u v

namespace ExpandedFA.Semigroups.WeakContinuitySpec

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Algebraic semigroup laws, including the identity at zero. -/
def SemigroupLaws (T : ℝ≥0 → E →L[𝕜] E) : Prop :=
  T 0 = ContinuousLinearMap.id 𝕜 E ∧
    ∀ t s, T (t + s) = (T t).comp (T s)

/-- Weak convergence at the origin, testing with the scalar-linear dual. -/
def WeakAtZero (T : ℝ≥0 → E →L[𝕜] E) : Prop :=
  ∀ x (ℓ : E →L[𝕜] 𝕜), Tendsto (fun t => ℓ (T t x)) (𝓝 0) (𝓝 (ℓ x))

/-- The source hypothesis, with the time parameter tending strictly down to zero. -/
def WeakRightAtZero (T : ℝ≥0 → E →L[𝕜] E) : Prop :=
  ∀ x (ℓ : E →L[𝕜] 𝕜), Tendsto (fun t => ℓ (T t x)) (𝓝[>] 0) (𝓝 (ℓ x))

/-- Strong convergence at the origin. -/
def StrongAtZero (T : ℝ≥0 → E →L[𝕜] E) : Prop :=
  ∀ x, Tendsto (fun t => T t x) (𝓝 0) (𝓝 x)

/-- Uniform bounds on every finite time interval, including the interval {0}. -/
def LocallyBounded (T : ℝ≥0 → E →L[𝕜] E) : Prop :=
  ∀ a : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ≤ a, ‖T t‖ ≤ C

/-- Full conclusion, on arbitrary real or complex Banach spaces. -/
def WeakContinuityImpliesStrong : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (E : Type v)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (T : ℝ≥0 → E →L[𝕜] E), SemigroupLaws T → WeakRightAtZero T →
    (∀ x, Continuous (fun t => T t x)) ∧ LocallyBounded T ∧
    (∀ x, StronglyMeasurable (fun t : ℝ => T (Real.toNNReal t) x)) ∧
    (∀ x (a : ℝ), IntegrableOn (fun t : ℝ => T (Real.toNNReal t) x) (Icc 0 a))

end ExpandedFA.Semigroups.WeakContinuitySpec
