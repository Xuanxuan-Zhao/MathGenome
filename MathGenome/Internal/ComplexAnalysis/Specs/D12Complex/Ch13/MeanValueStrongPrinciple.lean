import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarmonicFoundation
import Mathlib.MeasureTheory.Integral.CircleAverage

/-! Forward assertions of paper.tex:2550–2555 (d12:13-03).
Harmonicity is the shared differential predicate. The optional continuous
mean-value formulation uses radii depending on each individual center. -/
noncomputable section
open Set Metric

namespace D12Complex

/-- The pointwise local circle mean property, with no regularity assumed. -/
def LocalCircleMeanProperty (U : Set ℂ) (u : ℂ → ℝ) : Prop :=
  ∀ a ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ closedBall a ρ ⊆ U ∧
    ∀ r : ℝ, 0 < r → r < ρ → Real.circleAverage u a r = u a

end D12Complex

namespace Specs.D12Complex.Ch13.MeanValueStrongPrinciple
open _root_.D12Complex

def LocalCircleMeanProperty_type := Set ℂ → (ℂ → ℝ) → Prop
def LocalCircleMeanProperty_value : LocalCircleMeanProperty_type :=
  fun U u => ∀ a ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ closedBall a ρ ⊆ U ∧
    ∀ r : ℝ, 0 < r → r < ρ → Real.circleAverage u a r = u a

def circle_mean_value_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), HarmonicOn U u →
    ∀ (a : ℂ) (R : ℝ), 0 < R → closedBall a R ⊆ U →
      u a = (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi,
        u (a + (R : ℂ) * Complex.exp ((t : ℂ) * Complex.I))

def harmonic_local_circle_mean_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), HarmonicOn U u → LocalCircleMeanProperty U u

def continuous_mean_maximum_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), IsDomain U → ContinuousOn u U →
    LocalCircleMeanProperty U u → ∀ a ∈ U,
    (∀ z ∈ U, u z ≤ u a) → ∀ z ∈ U, u z = u a

def continuous_mean_minimum_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), IsDomain U → ContinuousOn u U →
    LocalCircleMeanProperty U u → ∀ a ∈ U,
    (∀ z ∈ U, u a ≤ u z) → ∀ z ∈ U, u z = u a

def harmonic_maximum_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), IsDomain U → HarmonicOn U u →
    ∀ a ∈ U, (∀ z ∈ U, u z ≤ u a) → ∀ z ∈ U, u z = u a

def harmonic_minimum_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), IsDomain U → HarmonicOn U u →
    ∀ a ∈ U, (∀ z ∈ U, u a ≤ u z) → ∀ z ∈ U, u z = u a

end Specs.D12Complex.Ch13.MeanValueStrongPrinciple
