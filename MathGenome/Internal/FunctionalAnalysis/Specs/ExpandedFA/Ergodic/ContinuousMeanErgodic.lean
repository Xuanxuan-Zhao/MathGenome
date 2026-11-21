import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Ergodic.DiscreteMeanErgodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-! Independent formulation of paper.tex:12556–12574.
Time is the additive monoid ℝ≥0; strong continuity is continuity of each orbit.
The integral is the vectorwise Bochner integral, with canonical real scalars.
There are no generator, separability, or nonzero-space assumptions. -/
noncomputable section
open scoped NNReal Topology
namespace ExpandedFA.Ergodic.ContinuousMeanErgodic.Spec
universe u v

structure ContractionSemigroup (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] where
  op : ℝ≥0 → H →L[𝕜] H
  zero : op 0 = 1
  add : ∀ s t, op (s + t) = (op s).comp (op t)
  continuous : ∀ x, Continuous (fun s => op s x)
  norm_le : ∀ s, ‖op s‖ ≤ 1

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The common fixed-vector space, as a closed linear subspace. -/
def fixedSpace (S : ContractionSemigroup 𝕜 H) : ClosedSubmodule 𝕜 H :=
  ⨅ s : ℝ≥0, ⟨(1 - S.op s).ker, (1 - S.op s).isClosed_ker⟩

/-- Extension of an orbit to real arguments for integration. On [0,∞) it is
exactly the original orbit; its values at negative arguments are immaterial. -/
def orbit (S : ContractionSemigroup 𝕜 H) (x : H) (s : ℝ) : H :=
  S.op (Real.toNNReal s) x

def average [CompleteSpace H] (S : ContractionSemigroup 𝕜 H) (t : ℝ≥0) (x : H) : H :=
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
  (t : ℝ)⁻¹ • ∫ s in (0 : ℝ)..(t : ℝ), orbit S x s

def DiscreteStrongConvergence : Prop :=
  DiscreteMeanErgodic.Spec.StrongConvergence.{u,v}

def OrbitIntegrable : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (S : ContractionSemigroup 𝕜 H) (x : H) (a b : ℝ),
    letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
    IntervalIntegrable (orbit S x) MeasureTheory.volume a b

def AverageContraction : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (S : ContractionSemigroup 𝕜 H) (t : ℝ≥0) (x : H),
    ‖average S t x‖ ≤ ‖x‖

/-- The vectorwise average is represented by a bounded scalar-linear operator. -/
def AverageOperator : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (S : ContractionSemigroup 𝕜 H) (t : ℝ≥0),
    ∃ A : H →L[𝕜] H, ‖A‖ ≤ 1 ∧ ∀ x, A x = average S t x

def FixedSpaceIdentification : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (S : ContractionSemigroup 𝕜 H) (x : H),
    x ∈ fixedSpace S ↔ ∀ s, S.op s x = x

/-- Strong convergence to the orthogonal projector onto the common fixed space.
The nonnegative real time parameter tends to infinity. -/
def StrongConvergence : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (S : ContractionSemigroup 𝕜 H) (x : H),
    Filter.Tendsto (fun t : ℝ≥0 => average S t x) Filter.atTop
      (𝓝 ((fixedSpace S).toSubmodule.starProjection x))

end ExpandedFA.Ergodic.ContinuousMeanErgodic.Spec
