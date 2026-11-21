import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionCalculus
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! The two limit assertions in `fa2:p4:distribution-calculus`.
All dimensions and open domains, and both scalar fields, are included.
The uniform compactwise order estimate is a conclusion. -/
open Set TopologicalSpace Filter
open scoped Topology Distributions ContDiff

namespace ExpandedFA.Distributions

/-- Weak convergence in the scalar-linear distribution dual. -/
def DistributionConverges {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (u : ℕ → ScalarDistribution 𝕜 Ω) (v : ScalarDistribution 𝕜 Ω) : Prop :=
  ∀ φ : Tests 𝕜 Ω, Tendsto (fun j => u j φ) atTop (𝓝 (v φ))

/-- Convergence in C∞ locally: every derivative converges uniformly on every
compact subset of the open domain. Fréchet derivatives are real multilinear,
including for complex-valued coefficients; order zero includes the values. -/
def SmoothLocallyConverges {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (a : ℕ → SmoothCoefficient 𝕜 Ω) (b : SmoothCoefficient 𝕜 Ω) : Prop :=
  ∀ (K : Compacts (Domain d)), (K : Set (Domain d)) ⊆ Ω → ∀ k : ℕ,
    TendstoUniformlyOn (fun j => iteratedFDeriv ℝ k (a j).val)
      (iteratedFDeriv ℝ k b.val) atTop K

/-- The exact scalar-linear pairing defining multiplication, independent of
any particular construction of the multiplication operator. -/
def DistributionProductPairing {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (a : SmoothCoefficient 𝕜 Ω) (u v : ScalarDistribution 𝕜 Ω) : Prop :=
  ∀ φ : Tests 𝕜 Ω, ∃ ψ : Tests 𝕜 Ω, (∀ x, ψ x = a.val x * φ x) ∧ v φ = u ψ

end ExpandedFA.Distributions

namespace Specs.ExpandedFA.Distributions.DistributionLimits
open _root_.ExpandedFA.Distributions

/-- The C∞ local convergence definition agrees with uniform convergence of
all coordinate partial derivatives, the usual Euclidean presentation. -/
def smoothConvergenceMeaningType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (a : ℕ → SmoothCoefficient 𝕜 Ω) (b : SmoothCoefficient 𝕜 Ω),
  SmoothLocallyConverges a b ↔
    ∀ (K : Compacts (Domain d)), (K : Set (Domain d)) ⊆ Ω →
      ∀ k (c : Fin k → Fin d) (ε : ℝ), 0 < ε →
        ∀ᶠ j in atTop, ∀ x ∈ (K : Set (Domain d)),
          ‖iteratedFDeriv ℝ k (a j).val x (fun i => coordinateVector (c i)) -
            iteratedFDeriv ℝ k b.val x (fun i => coordinateVector (c i))‖ < ε

/-- Pointwise bounded distributions have one order and one constant on each
compact step, uniform over the whole sequence. -/
def uniformOrderType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ℕ → ScalarDistribution 𝕜 Ω),
  (∀ φ : Tests 𝕜 Ω, BddAbove (range fun j => ‖u j φ‖)) →
  ∀ (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω),
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ j (φ : Step 𝕜 K),
      ‖u j (TestFunction.ofSupportedIn hK φ)‖ ≤ C * stepSeminorm 𝕜 K m φ

/-- An arbitrary scalar-valued pointwise limit is represented by a distribution;
linearity and continuity of that function are conclusions. -/
def pointwiseLimitType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ℕ → ScalarDistribution 𝕜 Ω) (f : Tests 𝕜 Ω → 𝕜),
  (∀ φ, Tendsto (fun j => u j φ) atTop (𝓝 (f φ))) →
  ∃ v : ScalarDistribution 𝕜 Ω, ∀ φ, v φ = f φ

/-- Products are supplied with their actual pairings, and converge weakly.
No uniform equicontinuity or common order is assumed. -/
def multiplicationLimitType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ℕ → ScalarDistribution 𝕜 Ω) (v : ScalarDistribution 𝕜 Ω)
    (a : ℕ → SmoothCoefficient 𝕜 Ω) (b : SmoothCoefficient 𝕜 Ω),
  DistributionConverges u v → SmoothLocallyConverges a b →
    ∃ (w : ℕ → ScalarDistribution 𝕜 Ω) (z : ScalarDistribution 𝕜 Ω),
      (∀ j, DistributionProductPairing (a j) (u j) (w j)) ∧
      DistributionProductPairing b v z ∧ DistributionConverges w z

end Specs.ExpandedFA.Distributions.DistributionLimits
