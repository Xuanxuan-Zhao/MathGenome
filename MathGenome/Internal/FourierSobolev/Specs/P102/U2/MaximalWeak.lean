import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.AveragesMaximalDefinition

/-! Theorem 2.7, paper.tex:891–922. Euclidean points and completed Lebesgue
measure are the library's canonical objects. Functions are real or complex
finite-valued measurable representatives, integrable on every compact set.
The maximal functions take values in the extended nonnegative reals. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace Specs.P102.U2.MaximalWeak
open _root_.D11.Ch03
abbrev μ (d : ℕ) [NeZero d] := Specs.D11.Ch03.LebesgueMeasures.lebesgue_value d
local instance (d : ℕ) [NeZero d] : MeasurableSpace (Point d) :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value d
abbrev LocalL1 := @Specs.D11.Ch13.AveragesMaximalDefinition.locallyIntegrable_value
variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

def ballAverage_type := ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜],
  (Point d → 𝕜) → ℝ → Point d → ℝ

def ballAverage_value (f : Point d → 𝕜) (r : ℝ) (x : Point d) : ℝ :=
  (μ d (ball x r)).toReal⁻¹ * ∫ y in ball x r, ‖f y‖ ∂(μ d)

def centered_type := ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜],
  (Point d → 𝕜) → Point d → ℝ≥0∞
def centered_value (f : Point d → 𝕜) (x : Point d) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), ENNReal.ofReal (ballAverage_value f r x)

def uncentered_type := ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜],
  (Point d → 𝕜) → Point d → ℝ≥0∞
def uncentered_value (f : Point d → 𝕜) (x : Point d) : ℝ≥0∞ :=
  ⨆ (z : Point d) (r : ℝ) (_ : 0 < r) (_ : x ∈ ball z r),
    ENNReal.ofReal (ballAverage_value f r z)

def measurable_maximal : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point d → 𝕜), LocalL1 f →
    Measurable (centered_value f) ∧ Measurable (uncentered_value f)

def ae_invariant : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f g : Point d → 𝕜), LocalL1 f → LocalL1 g → f =ᵐ[μ d] g →
    centered_value f = centered_value g ∧ uncentered_value f = uncentered_value g

def comparison : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point d → 𝕜), LocalL1 f → ∀ x,
    centered_value f x ≤ uncentered_value f x ∧
    uncentered_value f x ≤ (2 : ℝ≥0∞)^d * centered_value f x

def weak_bounds : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point d → 𝕜), Integrable f (μ d) → ∀ α : ℝ, 0 < α →
    μ d {x | ENNReal.ofReal α < centered_value f x} ≤
      (3 : ℝ≥0∞)^d * ENNReal.ofReal (∫ y, ‖f y‖ ∂(μ d)) / ENNReal.ofReal α ∧
    μ d {x | ENNReal.ofReal α < uncentered_value f x} ≤
      (6 : ℝ≥0∞)^d * ENNReal.ofReal (∫ y, ‖f y‖ ∂(μ d)) / ENNReal.ofReal α
end Specs.P102.U2.MaximalWeak
