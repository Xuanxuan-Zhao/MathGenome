import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.KoopmanGroups
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Ergodic.ContinuousMeanErgodic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Probability-space clause of `fa2:p3:kooper-wave`.
Invariant sets are invariant modulo null sets separately for every real time;
no common exceptional set in time, standardness, or separability is assumed. -/
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace ExpandedFA.Models.KoopmanErgodicMeans
open KoopmanGroups
universe u
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- Ergodicity of the whole flow, allowing null-measurable invariant sets. -/
def Ergodic (Φ : MeasurePreservingFlow X μ) : Prop :=
  ∀ s : Set X, NullMeasurableSet s μ →
    (∀ t : ℝ, Φ.maps t ⁻¹' s =ᵐ[μ] s) → μ s = 0 ∨ μ sᶜ = 0

/-- Equality and constancy are equality of actual L² equivalence classes. -/
def FixedVectorsAreConstants [IsProbabilityMeasure μ]
    (Φ : MeasurePreservingFlow X μ) : Prop :=
  ∀ f : Lp ℂ 2 μ, (∀ t : ℝ, pullback Φ t f = f) ↔
    ∃ c : ℂ, f = Lp.const 2 μ c

/-- Vectorwise continuous time average on [0,t], with t tending to infinity. -/
def timeAverage (Φ : MeasurePreservingFlow X μ) (t : ℝ≥0) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (t : ℝ)⁻¹ • ∫ s in (0 : ℝ)..(t : ℝ), pullback Φ s f

/-- The fixed-space assertion on the actual real-valued L² space. -/
def RealFixedVectorsAreConstants [IsProbabilityMeasure μ]
    (Φ : MeasurePreservingFlow X μ) : Prop :=
  ∀ f : Lp ℝ 2 μ, (∀ t : ℝ, realPullback Φ t f = f) ↔
    ∃ c : ℝ, f = Lp.const 2 μ c

/-- The real-valued vectorwise Bochner average of the actual real pullbacks. -/
def realTimeAverage (Φ : MeasurePreservingFlow X μ) (t : ℝ≥0)
    (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (t : ℝ)⁻¹ • ∫ s in (0 : ℝ)..(t : ℝ), realPullback Φ s f

namespace Spec

def FixedSpaceCharacterization : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (Φ : MeasurePreservingFlow X μ),
    FixedVectorsAreConstants Φ ↔ Ergodic Φ

def ErgodicTimeMeans : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (Φ : MeasurePreservingFlow X μ), StronglyContinuous Φ → Ergodic Φ →
    ∀ f : Lp ℂ 2 μ,
      Tendsto (fun t : ℝ≥0 => timeAverage Φ t f) atTop
        (𝓝 (Lp.const 2 μ (∫ x, f x ∂μ)))

def RealFixedSpaceCharacterization : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (Φ : MeasurePreservingFlow X μ),
    RealFixedVectorsAreConstants Φ ↔ Ergodic Φ

def RealErgodicTimeMeans : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (Φ : MeasurePreservingFlow X μ), RealStronglyContinuous Φ → Ergodic Φ →
    ∀ f : Lp ℝ 2 μ,
      Tendsto (fun t : ℝ≥0 => realTimeAverage Φ t f) atTop
        (𝓝 (Lp.const 2 μ (∫ x, f x ∂μ)))

end Spec
end ExpandedFA.Models.KoopmanErgodicMeans
