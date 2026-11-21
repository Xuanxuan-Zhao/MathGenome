import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Subcritical
import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Morrey
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Independent full scope of paper.tex, Theorem U5-05, lines 2322–2435.
The canonical spaces carry exactly the full Gagliardo norm. No connectedness,
nonemptiness, smooth-boundary, or endpoint exclusion at p = 1 is added.
Positive dimensions use n + 1 on domains and d ≥ 1 on the whole space.
-/
noncomputable section
open MeasureTheory Filter BoundedContinuousFunction
open scoped ENNReal NNReal Topology

namespace P102.Fractional.Embedding
open P102.Fractional

/-- Convergence in C^{0,β}. At β = 0 this is exactly uniform convergence.
For positive β the increment of the error has arbitrarily small Hölder constant.
This avoids discarding infinite seminorms by converting them to real numbers. -/
def HolderConverges {X 𝕜 : Type*} [MetricSpace X] [RCLike 𝕜]
    (β : ℝ≥0) (f : ℕ → X →ᵇ 𝕜) (g : X →ᵇ 𝕜) : Prop :=
  Tendsto f atTop (𝓝 g) ∧
    (β = 0 ∨ ∀ ε : ℝ≥0, 0 < ε →
      ∀ᶠ j in atTop, HolderWith ε β (fun x => f j x - g x))

/-- The usual class inclusion as a bounded linear map, compact on every bounded set. -/
def CompactLpInclusion {d : ℕ} (𝕜 : Type*) [RCLike 𝕜]
    (G : Set (Domain d)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] : Prop :=
  ∃ J : Space 𝕜 G s p →L[𝕜] Lp 𝕜 q (domainMeasure G),
    (∀ u, (J u : Domain d → 𝕜) =ᵐ[domainMeasure G] firstProjection u) ∧
    ∀ A : Set (Space 𝕜 G s p), Bornology.IsBounded A → IsCompact (closure (J '' A))

/-- The standard scaled real convolution kernel, acting on either scalar field. -/
def smoothValue {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (ρ : Domain d → ℝ) (ε : ℝ) (f : Domain d → 𝕜) (x : Domain d) : 𝕜 :=
  ∫ y, (ε⁻¹ ^ d * ρ (ε⁻¹ • y)) • f (x - y)

end P102.Fractional.Embedding

namespace Specs.P102.Fractional.EmbeddingsCompactness
open _root_.P102.Fractional _root_.P102.Fractional.Morrey
open _root_.P102.Fractional.Embedding
universe u

/-- Fixed-support bounded linear extension, with the exact upstream scope. -/
def extensionClause : Prop := Specs.P102.Fractional.Extension.extension.{u}

/-- Whole-space homogeneous and domain full-norm endpoint estimates. -/
def subcriticalEstimates : Prop :=
  Specs.P102.Fractional.Subcritical.wholeSpace.{u} ∧
  Specs.P102.Fractional.Subcritical.boundedDomain.{u}

/-- Full endpoint Hölder bound, with existence and uniqueness of representatives. -/
def supercriticalEmbedding : Prop := Specs.P102.Fractional.Morrey.onClosure.{u}

/-- All strictly subcritical Lq exponents, including q = 1. -/
def subcriticalCompactness : Prop :=
  ∀ (n : ℕ) (G : Set (Domain (n + 1))), IsBoundedLipschitzOpen G →
  ∀ s : ℝ, 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → s * p.toReal < (n + 1 : ℕ) →
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], q ≠ ∞ → q < sobolevExponent (n + 1) s p →
  ∀ (𝕜 : Type u) [RCLike 𝕜], CompactLpInclusion 𝕜 G s p q

/-- At sp = d, bounded linear and compact inclusion for each finite q ≥ 1. -/
def criticalInclusions : Prop :=
  ∀ (n : ℕ) (G : Set (Domain (n + 1))), IsBoundedLipschitzOpen G →
  ∀ s : ℝ, 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → s * p.toReal = (n + 1 : ℕ) →
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], q ≠ ∞ →
  ∀ (𝕜 : Type u) [RCLike 𝕜], CompactLpInclusion 𝕜 G s p q

/-- The continuous part of the critical clause, as the actual bounded linear
inclusion of a.e. classes into every finite Lq. -/
def criticalEmbedding : Prop :=
  ∀ (n : ℕ) (G : Set (Domain (n + 1))), IsBoundedLipschitzOpen G →
  ∀ s : ℝ, 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → s * p.toReal = (n + 1 : ℕ) →
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], q ≠ ∞ →
  ∀ (𝕜 : Type u) [RCLike 𝕜],
  ∃ J : Space 𝕜 G s p →L[𝕜] Lp 𝕜 q (domainMeasure G),
    ∀ u, (J u : Domain (n + 1) → 𝕜) =ᵐ[domainMeasure G] firstProjection u

/-- A fixed representative map, compact into every strictly smaller Hölder
space, with β = 0 explicitly meaning the supremum norm. The limit is in the
claimed target space; it need not be the representative of a source element. -/
def supercriticalCompactness : Prop :=
  ∀ (n : ℕ) (G : Set (Domain (n + 1))), IsBoundedLipschitzOpen G →
  ∀ s : ℝ, 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → ((n + 1 : ℕ) : ℝ) < s * p.toReal →
  ∀ (𝕜 : Type u) [RCLike 𝕜],
  ∃ F : Space 𝕜 G s p → (closure G →ᵇ 𝕜),
    (∀ u, RepresentsOnClosure u (F u)) ∧
    ∀ β : ℝ≥0, (β : ℝ) < exponent (n + 1) s p →
    ∀ v : ℕ → Space 𝕜 G s p, (∃ M : ℝ, ∀ j, ‖v j‖ ≤ M) →
    ∃ f : closure G →ᵇ 𝕜, MemHolder β (f : closure G → 𝕜) ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ HolderConverges β (fun j => F (v (σ j))) f

/-- A bounded-domain comparison sufficient to reduce the critical case to
the subcritical case. It preserves the underlying Lp class and is bounded in
the full norm. A diameter bound gives this without a whole-space tail estimate. -/
def lowerSmoothness : Prop :=
  ∀ (d : ℕ) (G : Set (Domain d)), Bornology.IsBounded G →
  ∀ (t s : ℝ), 0 < t → t < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∀ (𝕜 : Type u) [RCLike 𝕜],
  ∃ (C : ℝ≥0) (J : Space 𝕜 G s p →L[𝕜] Space 𝕜 G t p),
    (∀ u, firstProjection (J u) = firstProjection u) ∧
    ∀ u, ‖J u‖ ≤ (C : ℝ) * ‖u‖

/-- A single smooth compactly supported probability kernel has uniform
approximation error O(ε^s [v]_{s,p}), for the entire whole-space unit ball.
This is a quantitative uniform assertion, stronger than pointwise density. -/
def uniformSmoothing : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ s : ℝ, 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∀ (𝕜 : Type u) [RCLike 𝕜],
  ∃ (ρ : Domain d → ℝ) (C : ℝ≥0),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ HasCompactSupport ρ ∧
    (∀ x, 0 ≤ ρ x) ∧ (∫ x, ρ x) = 1 ∧ Function.support ρ ⊆ Metric.closedBall 0 1 ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ v : Space 𝕜 (Set.univ : Set (Domain d)) s p,
      MemLp (smoothValue ρ ε (firstProjection v)) p volume ∧
      eLpNorm (fun x => smoothValue ρ ε (firstProjection v) x - firstProjection v x) p volume ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (ε ^ s) * seminorm Set.univ s p (firstProjection v)

/-- The complete assigned theorem and the two explicitly requested analytic
support statements. This definition contains no conditional proof premises. -/
def fullTheorem : Prop :=
  extensionClause.{u} ∧ subcriticalEstimates.{u} ∧ supercriticalEmbedding.{u} ∧
  subcriticalCompactness.{u} ∧ criticalEmbedding.{u} ∧ criticalInclusions.{u} ∧ supercriticalCompactness.{u} ∧
  lowerSmoothness.{u} ∧ uniformSmoothing.{u}

end Specs.P102.Fractional.EmbeddingsCompactness
