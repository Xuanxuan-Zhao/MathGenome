import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.C1DomainExtension

/-! Local coordinate transport used in the C² two-jet trace theorem
(`paper.tex`, fa2:p4:second-trace). All spaces below are the original
multi-index distributional derivative graphs, with restricted Euclidean volume
and the sum norm. No boundary regularity of the arbitrary open input is imposed. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal
namespace ExpandedFA.PartIV.SecondTraceTransport.Spec
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.C1Extension.Transport
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- A localized C² coordinate pullback, with compatibility for every
representative. Compact support supplies all finite constants; no Sobolev
transport or Jacobian-bound certificate is an input. -/
def LocalizedTransport : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Λ : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
      ContDiffOn ℝ 2 Φ Φ.source → ContDiffOn ℝ 2 Φ.symm Φ.target →
    ∀ (θ : Domain d → 𝕜), ContDiff ℝ (⊤ : ℕ∞) θ →
      HasCompactSupport θ → tsupport θ ⊆ Φ.source →
    ∃ P : SpaceValue 𝕜 d Λ 2 p →L[𝕜]
        SpaceValue 𝕜 d (chartPreimage Φ Λ) 2 p,
      ∀ (u : SpaceValue 𝕜 d Λ 2 p) (f : Domain d → 𝕜),
        f =ᵐ[volume.restrict (Λ : Set (Domain d))] u.val (zeroIndex d 2) →
        (P u).val (zeroIndex d 2) =ᵐ[
          volume.restrict (chartPreimage Φ Λ : Set (Domain d))]
          fun x => θ x * f (Φ x)

/-- The identity-chart case, also useful without a coordinate change.
The coefficient may meet the physical boundary of Ω. -/
def SmoothMultiplication : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∀ (θ : Domain d → 𝕜), ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ →
    ∃ M : SpaceValue 𝕜 d Ω 2 p →L[𝕜] SpaceValue 𝕜 d Ω 2 p,
      ∀ (u : SpaceValue 𝕜 d Ω 2 p) (f : Domain d → 𝕜),
        f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 2) →
        (M u).val (zeroIndex d 2) =ᵐ[volume.restrict (Ω : Set (Domain d))]
          fun x => θ x * f x

/-- Localized insertion into a larger target, including physical-boundary
patches. The support is closed relative to the target and stays inside the
source, so the artificial edge creates no distributional jump. -/
def LocalizedZeroExtension : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω Λ : Opens (Domain d)), Ω ≤ Λ →
    ∀ (K : Set (Domain d)), IsClosed (K ∪ (Λ : Set (Domain d))ᶜ) → K ⊆ Ω →
    ∀ (θ : Domain d → 𝕜), ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ →
      (Ω : Set (Domain d)) ∩ tsupport θ ⊆ K →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃ E : SpaceValue 𝕜 d Ω 2 p →L[𝕜] SpaceValue 𝕜 d Λ 2 p,
      ∀ (u : SpaceValue 𝕜 d Ω 2 p) (f : Domain d → 𝕜),
        f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 2) →
        (E u).val (zeroIndex d 2) =ᵐ[volume.restrict (Λ : Set (Domain d))]
          (Ω : Set (Domain d)).indicator (fun x => θ x * f x)

/-- Recovery on the source and exact preservation of the graph norm for a
supported order-two patch. The hypotheses refer to the actual derivative
components rather than an assumed extension operator. -/
def SupportedRecovery : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω Λ : Opens (Domain d)), Ω ≤ Λ →
    ∀ (K : Set (Domain d)), IsClosed (K ∪ (Λ : Set (Domain d))ᶜ) → K ⊆ Ω →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 2 p),
      (∀ α, ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)), x ∉ K → u.val α x = 0) →
    ∃ v : SpaceValue 𝕜 d Λ 2 p,
      (∀ α, v.val α =ᵐ[volume.restrict (Λ : Set (Domain d))]
        (Ω : Set (Domain d)).indicator (u.val α)) ∧
      (∀ α, v.val α =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val α) ∧ ‖v‖ = ‖u‖

end ExpandedFA.PartIV.SecondTraceTransport.Spec
