import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.RectifiableStieltjes
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.NormalizedStieltjes
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.Analysis.Normed.Operator.Mul

/-! The measure part of paper.tex:749–779. The original continuous BV function
is clamped to its compact interval and normalized by its actual left value.
The complex scalar integral uses the continuous bilinear pairing (z,w) ↦ z*w.
No derivative, a.e. replacement, or assumed measure certificate occurs here. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace D12Complex.StieltjesMeasure

def normalizedExtension (γ : ℝ → ℂ) (a b x : ℝ) : ℂ :=
  γ (max a (min b x)) - γ a

def measure (γ : ℝ → ℂ) (a b : ℝ) : ComplexMeasure ℝ :=
  Specs.D11.Ch12.ScalarStieltjesCorrespondence.stieltjesMeasure_value
    (normalizedExtension γ a b)

/-- The ordinary complex measure integral, with no conjugation. -/
def measureIntegral (ν : ComplexMeasure ℝ) (a b : ℝ) (u : ℝ → ℂ) : ℂ :=
  ∫ᵛ x in Icc a b, u x ∂[ContinuousLinearMap.mul ℝ ℂ; ν]

end D12Complex.StieltjesMeasure

namespace Specs.D12Complex.Ch03.ContourStieltjesMeasure
open _root_.D12Complex.StieltjesMeasure _root_.D12Complex.Stieltjes

abbrev normalizedExtension_type := (ℝ → ℂ) → ℝ → ℝ → ℝ → ℂ
def normalizedExtension_value : normalizedExtension_type := normalizedExtension
abbrev measure_type := (ℝ → ℂ) → ℝ → ℝ → ComplexMeasure ℝ
def measure_value : measure_type := measure
abbrev measureIntegral_type := ComplexMeasure ℝ → ℝ → ℝ → (ℝ → ℂ) → ℂ
def measureIntegral_value : measureIntegral_type := measureIntegral

def normalizedExtension_values_type : Prop :=
  ∀ (γ : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    (∀ x, x ≤ a → normalizedExtension γ a b x = 0) ∧
    (∀ x ∈ Icc a b, normalizedExtension γ a b x = γ x - γ a) ∧
    (∀ x, b ≤ x → normalizedExtension γ a b x = γ b - γ a)

def normalizedExtension_regular_type : Prop :=
  ∀ (γ : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    ContinuousOn γ (Icc a b) → totalVariation γ a b < ⊤ →
    Continuous (normalizedExtension γ a b) ∧
      Specs.D11.Ch12.ScalarStieltjesCorrespondence.NBV_value (normalizedExtension γ a b)

def measure_finite_type : Prop :=
  ∀ (γ : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    ContinuousOn γ (Icc a b) → totalVariation γ a b < ⊤ →
    IsFiniteMeasure (measure γ a b).variation

def measure_cumulative_type : Prop :=
  ∀ (γ : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    ContinuousOn γ (Icc a b) → totalVariation γ a b < ⊤ →
    ∀ x, measure γ a b (Iic x) = normalizedExtension γ a b x

def measure_Ioc_type : Prop :=
  ∀ (γ : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    ContinuousOn γ (Icc a b) → totalVariation γ a b < ⊤ →
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      measure γ a b (Ioc s t) = γ t - γ s

/-- All atoms vanish; in particular the left endpoint atom is specified. -/
def measure_singleton_type : Prop :=
  ∀ (γ : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    ContinuousOn γ (Icc a b) → totalVariation γ a b < ⊤ →
    ∀ x, measure γ a b {x} = 0

def measure_variation_Icc_type : Prop :=
  ∀ (γ : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    ContinuousOn γ (Icc a b) → totalVariation γ a b < ⊤ →
    (measure γ a b).variation (Icc a b) = totalVariation γ a b

def continuous_integrable_type : Prop :=
  ∀ (γ : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    ContinuousOn γ (Icc a b) → totalVariation γ a b < ⊤ →
    ∀ u : ℝ → ℂ, ContinuousOn u (Icc a b) →
      (measure γ a b).IntegrableOn u (Icc a b)

def integral_eq_measureIntegral_type : Prop :=
  ∀ (γ : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    ContinuousOn γ (Icc a b) → totalVariation γ a b < ⊤ →
    ∀ u : ℝ → ℂ, ContinuousOn u (Icc a b) →
      integral a b u γ = measureIntegral (measure γ a b) a b u

end Specs.D12Complex.Ch03.ContourStieltjesMeasure
