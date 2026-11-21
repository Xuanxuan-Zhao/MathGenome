import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Independent statements for the fixed-set, demiclosedness and averaged-map
energy parts of `paper.tex`, fa2:p5:nonlinear-ergodic, lines 22474–22515.
The map is arbitrary, possibly nonlinear, on the entire Hilbert space.
Weak convergence is convergence against every continuous scalar-linear
functional. Complex convexity and averaging use the shared realification,
which preserves the original norm and topology. No separability or
nontriviality assumption is imposed.
-/
noncomputable section
open Filter
open scoped Topology

namespace ExpandedFA.PartV.NonexpansiveDemiclosure.Spec
universe u v

/-- Nonexpansiveness in the original norm, with no linearity assumption. -/
def Nonexpansive {H : Type v} [NormedAddCommGroup H] (T : H → H) : Prop :=
  ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖

def fixedSet {H : Type v} (T : H → H) : Set H := {x | T x = x}

/-- The arithmetic average of the identity and T. -/
def averaged (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (T : H → H) : H → H :=
  letI := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  fun x => (1 / 2 : ℝ) • (x + T x)

/-- Scalar-linear continuous dual tests, not antidual tests. -/
def WeaklyConverges (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H] (zj : ℕ → H) (z : H) : Prop :=
  ∀ φ : H →L[𝕜] 𝕜, Tendsto (fun j => φ (zj j)) atTop (𝓝 (φ z))

def FixedSetClosedConvex : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H → H), Nonexpansive T →
    IsClosed (fixedSet T) ∧
      ExpandedFA.Hilbert.Conventions.Spec.RealConvexValue 𝕜 H (fixedSet T)

/-- Distances to every fixed point decrease, giving explicit orbit bounds. -/
def OrbitBounds : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H → H), Nonexpansive T → ∀ (p : H), T p = p → ∀ f : H,
    Antitone (fun n : ℕ => ‖T^[n] f - p‖) ∧
      (∀ n : ℕ, ‖T^[n] f - p‖ ≤ ‖f - p‖) ∧
      Antitone (fun n : ℕ => ‖(averaged 𝕜 T)^[n] f - p‖) ∧
      (∀ n : ℕ, ‖(averaged 𝕜 T)^[n] f - p‖ ≤ ‖f - p‖)

/-- The classical demiclosedness principle, at zero residual.
This stronger formulation does not need a pre-existing fixed point. -/
def Demiclosedness : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H → H), Nonexpansive T → ∀ (zj : ℕ → H) (z : H),
    WeaklyConverges 𝕜 zj z →
    Tendsto (fun j => zj j - T (zj j)) atTop (𝓝 0) → T z = z

def AveragedFixedSet : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (T : H → H),
    fixedSet (averaged 𝕜 T) = fixedSet T

def AveragedFirm : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (T : H → H), Nonexpansive T → ∀ u v : H,
    let S := averaged 𝕜 T
    ‖S u - S v‖ ^ 2 + ‖(u - S u) - (v - S v)‖ ^ 2 ≤ ‖u - v‖ ^ 2

def AveragedNonexpansive : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (T : H → H), Nonexpansive T → Nonexpansive (averaged 𝕜 T)

/-- Finite telescoping with the final distance retained. -/
def AveragedIterateEnergy : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H → H), Nonexpansive T → ∀ (p : H), T p = p → ∀ (f : H) (N : ℕ),
    let μ := fun n => (averaged 𝕜 T)^[n] f
    (∑ n ∈ Finset.range N, ‖μ (n + 1) - μ n‖ ^ 2) + ‖μ N - p‖ ^ 2 ≤ ‖f - p‖ ^ 2

/-- Square summability, together with its fixed-point-dependent norm bound. -/
def AveragedSquareSummable : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H → H), Nonexpansive T → ∀ (p : H), T p = p → ∀ f : H,
    let μ := fun n => (averaged 𝕜 T)^[n] f
    Summable (fun n => ‖μ (n + 1) - μ n‖ ^ 2) ∧
      (∑' n, ‖μ (n + 1) - μ n‖ ^ 2) ≤ ‖f - p‖ ^ 2

end ExpandedFA.PartV.NonexpansiveDemiclosure.Spec
