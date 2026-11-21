import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Space
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
The localization operations on the canonical Gagliardo graph space.
Constants are quantified before domains, charts, multipliers and functions.
The zero-extension separation condition concerns only the artificial edge H \ G,
so it permits a piece to meet the genuine boundary of H.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Topology

namespace P102.Fractional

/-- The p-th power of the Lp norm, retained as an extended integral. -/
def lpMass {d : ℕ} {𝕜 : Type*} [RCLike 𝕜] (G : Set (Domain d))
    (p : ℝ≥0∞) (u : Domain d → 𝕜) : ℝ≥0∞ :=
  ∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂domainMeasure G

/-- Zero extension of a representative. Values outside G are discarded. -/
def zeroExtend {d : ℕ} {𝕜 : Type*} [RCLike 𝕜] (G : Set (Domain d))
    (u : Domain d → 𝕜) : Domain d → 𝕜 := G.indicator u

/-- Chart pullback, set to zero outside the source chart. -/
def chartPullback {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G H : Set (Domain d)} (F : G ≃ₜ H) (u : Domain d → 𝕜)
    (x : Domain d) : 𝕜 := by
  classical
  exact if hx : x ∈ G then u (F ⟨x, hx⟩) else 0

/-- Vanishing in a δ-neighborhood of the artificial edge, in the a.e. sense. -/
def SupportedAway {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (G H : Set (Domain d)) (δ : ℝ) (u : Domain d → 𝕜) : Prop :=
  ∀ᵐ x ∂domainMeasure G, u x ≠ 0 → ∀ y ∈ H \ G, δ ≤ dist x y

/-- The first coordinate is normal to the flat face. Dimension n+1 includes
both higher-dimensional half-spaces and the one-dimensional half-line. -/
def upperHalfSpace (n : ℕ) : Set (Domain (n + 1)) := {x | 0 < x 0}

def flatReflection {n : ℕ} (x : Domain (n + 1)) : Domain (n + 1) :=
  WithLp.toLp 2 (fun i : Fin (n + 1) => if i = 0 then -x i else x i)

/-- Even reflection, with an irrelevant but explicit value zero on the face. -/
def evenExtend {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Domain (n + 1) → 𝕜) (x : Domain (n + 1)) : 𝕜 :=
  if x 0 = 0 then 0 else if 0 < x 0 then u x else u (flatReflection x)

end P102.Fractional

namespace Specs.P102.Fractional.Localization
open _root_.P102.Fractional
universe u

/-- Bounded Lipschitz scalar multiplication, for either real or complex scalars.
The same finite constant bounds the energy comparison and the sum-norm operator.
The hypotheses on φ concern only G. No smoothness of G or φ is required. -/
def boundedMultiplier : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (s : ℝ), 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → ∀ (M L : ℝ≥0),
  ∃ C : ℝ≥0, ∀ {𝕜 : Type u} [RCLike 𝕜]
    (G : Set (Domain d)), IsOpen G → ∀ (φ : Domain d → 𝕜),
    LipschitzOnWith L φ G → (∀ x ∈ G, ‖φ x‖ ≤ M) →
    (∀ u : Domain d → 𝕜, MemLp u p (domainMeasure G) →
      energy G s p (fun x => φ x * u x) ≤
        (C : ℝ≥0∞) * (energy G s p u + lpMass G p u)) ∧
    ∃ T : Space 𝕜 G s p →L[𝕜] Space 𝕜 G s p,
      ∀ u, (firstProjection (T u) : Domain d → 𝕜) =ᵐ[domainMeasure G]
        (fun x => φ x * firstProjection u x) ∧ ‖T u‖ ≤ (C : ℝ) * ‖u‖

/-- Bi-Lipschitz changes of open Euclidean coordinates. Constants depend only
on dimension, s, p and the forward/inverse Lipschitz bounds. The conclusion
includes both raw double-integral comparison and an operator on a.e. classes. -/
def bilipschitzPullback : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (s : ℝ), 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → ∀ (K K' : ℝ≥0),
  ∃ C : ℝ≥0, ∀ {𝕜 : Type u} [RCLike 𝕜]
    (G H : Set (Domain d)), IsOpen G → IsOpen H →
    ∀ (F : G ≃ₜ H), LipschitzWith K F → LipschitzWith K' F.symm →
    (∀ u v : Domain d → 𝕜, u =ᵐ[domainMeasure H] v →
      chartPullback F u =ᵐ[domainMeasure G] chartPullback F v) ∧
    (∀ u : Domain d → 𝕜, MemLp u p (domainMeasure H) →
      energy G s p (chartPullback F u) ≤ (C : ℝ≥0∞) * energy H s p u ∧
      lpMass G p (chartPullback F u) ≤ (C : ℝ≥0∞) * lpMass H p u) ∧
    ∃ T : Space 𝕜 H s p →L[𝕜] Space 𝕜 G s p,
      ∀ u, (firstProjection (T u) : Domain d → 𝕜) =ᵐ[domainMeasure G]
        chartPullback F (firstProjection u) ∧ ‖T u‖ ≤ (C : ℝ) * ‖u‖

/-- Zero extension across an artificial edge. The coefficient of the original
energy is exactly one. The additional energy is C δ^(-sp) times the Lp mass;
C is independent of δ, the open sets and u. The second conclusion realizes
the extended class in the canonical space with a quantitative sum-norm bound. -/
def zeroExtensionAway : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (s : ℝ), 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∃ C : ℝ≥0, ∀ {𝕜 : Type u} [RCLike 𝕜]
    (G H : Set (Domain d)), IsOpen G → IsOpen H → G ⊆ H →
    ∀ (δ : ℝ), 0 < δ →
    (∀ u : Domain d → 𝕜, MemLp u p (domainMeasure G) → SupportedAway G H δ u →
      energy H s p (zeroExtend G u) ≤ energy G s p u +
        (C : ℝ≥0∞) * ENNReal.ofReal (δ ^ (-s * p.toReal)) * lpMass G p u) ∧
    (∀ u : Space 𝕜 G s p, SupportedAway G H δ (firstProjection u) →
      ∃ v : Space 𝕜 H s p,
        (firstProjection v : Domain d → 𝕜) =ᵐ[domainMeasure H]
          zeroExtend G (firstProjection u) ∧
        ‖v‖ ≤ (2 + (C : ℝ) * δ ^ (-s * p.toReal)) * ‖u‖)

/-- Even reflection across the flat face. Four times the source energy and
twice the source Lp mass control the extended representative; the resulting
scalar-linear operator has sum-norm bound four, including n=0 (dimension one). -/
def evenReflection : Prop :=
  ∀ (n : ℕ) (s : ℝ), 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∀ {𝕜 : Type u} [RCLike 𝕜],
    (∀ u v : Domain (n + 1) → 𝕜,
      u =ᵐ[domainMeasure (upperHalfSpace n)] v →
      evenExtend u =ᵐ[domainMeasure Set.univ] evenExtend v) ∧
    (∀ u : Domain (n + 1) → 𝕜, MemLp u p (domainMeasure (upperHalfSpace n)) →
      energy Set.univ s p (evenExtend u) ≤ 4 * energy (upperHalfSpace n) s p u ∧
      lpMass Set.univ p (evenExtend u) = 2 * lpMass (upperHalfSpace n) p u) ∧
    ∃ T : Space 𝕜 (upperHalfSpace n) s p →L[𝕜] Space 𝕜 Set.univ s p,
      ∀ u, (firstProjection (T u) : Domain (n + 1) → 𝕜)
        =ᵐ[domainMeasure Set.univ] evenExtend (firstProjection u) ∧ ‖T u‖ ≤ 4 * ‖u‖

end Specs.P102.Fractional.Localization
