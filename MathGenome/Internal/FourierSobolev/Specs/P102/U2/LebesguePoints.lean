import MathGenome.Internal.FourierSobolev.Specs.P102.U2.MaximalWeak

/-! Theorem 2.9 (paper.tex:920–931). We use the canonical completed
Lebesgue space and its finite-valued real or complex representatives.
`LocalL1` includes measurability and integrability on every compact set.
`lebesguePoint_value` is the right-hand limit at zero of the normalized
integral of `‖f y - f x‖`; `average_value` is the normalized integral of `f`.
No global integrability or choice of a different representative is required. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
universe u
namespace Specs.P102.U2.LebesguePoints
open _root_.D11.Ch03
open Specs.P102.U2.MaximalWeak
open Specs.D11.Ch13.AveragesMaximalDefinition

local instance (d : ℕ) [NeZero d] : MeasurableSpace (Point d) :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value d

def ae_lebesguePoint : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point d → 𝕜) (hf : LocalL1 f),
    ∀ᵐ x ∂(μ d), lebesguePoint_value f hf x

def average_tendsto_of_lebesguePoint : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point d → 𝕜) (hf : LocalL1 f) {x : Point d},
    lebesguePoint_value f hf x →
    Tendsto (fun r => average_value f hf r x) (𝓝[>] (0 : ℝ)) (𝓝 (f x))

/-- Every Lebesgue point works for every filtered family of containing balls.
Both the oscillation and the scalar average converge along that family. -/
def containing_balls_tendsto : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point d → 𝕜) (hf : LocalL1 f) {x : Point d},
    lebesguePoint_value f hf x →
    ∀ {ι : Type u} {l : Filter ι} (z : ι → Point d) (r : ι → ℝ),
      Tendsto r l (𝓝[>] (0 : ℝ)) →
      (∀ᶠ i in l, x ∈ ball (z i) (r i)) →
      Tendsto (fun i => (μ d (ball (z i) (r i))).toReal⁻¹ *
        ∫ y in ball (z i) (r i), ‖f y - f x‖ ∂(μ d)) l (𝓝 0) ∧
      Tendsto (fun i => average_value f hf (r i) (z i)) l (𝓝 (f x))

/-- One measurable null set suffices simultaneously for all ball families. -/
def lebesgue_differentiation : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point d → 𝕜) (hf : LocalL1 f),
    ∃ N : Set (Point d), MeasurableSet N ∧ μ d N = 0 ∧
      ∀ x ∉ N, lebesguePoint_value f hf x ∧
        Tendsto (fun r => average_value f hf r x) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) ∧
        ∀ {ι : Type u} {l : Filter ι} (z : ι → Point d) (r : ι → ℝ),
          Tendsto r l (𝓝[>] (0 : ℝ)) →
          (∀ᶠ i in l, x ∈ ball (z i) (r i)) →
          Tendsto (fun i => (μ d (ball (z i) (r i))).toReal⁻¹ *
            ∫ y in ball (z i) (r i), ‖f y - f x‖ ∂(μ d)) l (𝓝 0) ∧
          Tendsto (fun i => average_value f hf (r i) (z i)) l (𝓝 (f x))

end Specs.P102.U2.LebesguePoints
