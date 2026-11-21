import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.HaarBasis
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15UnconditionalCriteria

/-!
Independent statements for the interior-exponent clause of
`fa2:p1:schauder-haar` and its estimates, paper.tex:4422–4459.
All Haar objects below are the accepted canonical unnormalised functions on
the closed Lebesgue unit interval, including the constant at index zero.
Finite subsets include the empty set. Unit-disk multipliers include signs,
complex phases, and coordinate deletions; no bound may depend on their choice
or on the finite subset. The full interior conclusion is not an assumption.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators unitInterval
universe u
namespace ExpandedFA.P1.HaarUnconditional.Spec
open HaarBasis.Spec

/-- A finite Fourier-Haar multiplier on the actual Lp quotient. -/
def finiteTransform {𝕜 : Type u} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (S : Finset ℕ) (m : ℕ → 𝕜) (f : Lp 𝕜 p (volume : Measure I)) :
    Lp 𝕜 p (volume : Measure I) :=
  ∑ n ∈ S, (m n * haarCoefficient f n) • haarLp 𝕜 p n

/-- The bound is for every L1 input and every positive threshold, with no
L2 assumption on the input. Measure is ENNReal-valued, including null sets. -/
def UniformWeakOne : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (𝕜 : Type u) [RCLike 𝕜]
    (S : Finset ℕ) (m : ℕ → 𝕜), (∀ n ∈ S, ‖m n‖ ≤ 1) →
    ∀ (f : Lp 𝕜 1 (volume : Measure I)) (t : ℝ), 0 < t →
      volume {x : I | t < ‖finiteTransform S m f x‖} ≤
        ENNReal.ofReal (C * ‖f‖ / t)

def L2Contraction : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (S : Finset ℕ) (m : ℕ → 𝕜),
    (∀ n ∈ S, ‖m n‖ ≤ 1) → ∀ f : Lp 𝕜 2 (volume : Measure I),
      ‖finiteTransform S m f‖ ≤ ‖f‖

/-- This is the analytic estimate for every real or complex scalar field.
It has no extra boundedness, regularity, or finite-support hypothesis on f. -/
def UniformLpBounds : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p → p ≠ ∞ → ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset ℕ) (m : ℕ → 𝕜), (∀ n ∈ S, ‖m n‖ ≤ 1) →
      ∀ f : Lp 𝕜 p (volume : Measure I), ‖finiteTransform S m f‖ ≤ C * ‖f‖

/-- The finite-subset net converges to the original function, not just to
an unspecified sum. -/
def HaarUnconditionalExpansion : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p → p ≠ ∞ → ∀ f : Lp 𝕜 p (volume : Measure I),
      HasSum (fun n => haarCoefficient f n • haarLp 𝕜 p n) f

def HaarUnconditionalBasis : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p → p ≠ ∞ →
      C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜
        (Lp 𝕜 p (volume : Measure I)) (haarLp 𝕜 p)

/-- A proof of this implication alone does not discharge UniformLpBounds. -/
def BoundsImplyUnconditional : Prop :=
  UniformLpBounds.{u} → HaarUnconditionalExpansion.{u} ∧ HaarUnconditionalBasis.{u}

/-- The already closed exponent-two specialization. -/
def L2UnconditionalBasis : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜
      (Lp 𝕜 2 (volume : Measure I)) (haarLp 𝕜 2)

namespace Expected

def finiteTransformType : Type _ := ∀ {𝕜 : Type u} [RCLike 𝕜]
  {p : ℝ≥0∞} [Fact (1 ≤ p)], Finset ℕ → (ℕ → 𝕜) →
    Lp 𝕜 p (volume : Measure I) → Lp 𝕜 p (volume : Measure I)
def finiteTransformValue : finiteTransformType := @finiteTransform

end Expected
end ExpandedFA.P1.HaarUnconditional.Spec
