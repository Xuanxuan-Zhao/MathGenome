import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeasureDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeanErgodic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Independent specification of `d13:19:composition-isometry` and the L²
specialization of `d13:19:mean-ergodic`. Composition is into Lᵖ, with no
invertibility or surjectivity assumption. The exponent is an extended
nonnegative real, so `p = ∞` is included. -/
namespace Specs.D13Unified.Ch19.CompositionIsometry
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
universe u v

/-- The actual composition operator on equivalence classes. -/
def compositionType :=
  {X : Type u} → [MeasurableSpace X] → (𝕜 : Type v) → [RCLike 𝕜] →
  (p : ℝ≥0∞) → [Fact (1 ≤ p)] → (T : X → X) → (μ : Measure X) →
  MeasureDefinitions.PreservesMeasure T μ → Lp 𝕜 p μ →ₗᵢ[𝕜] Lp 𝕜 p μ

def composition : compositionType := by
  intro X _ 𝕜 _ p _ T μ hT
  exact Lp.compMeasurePreservingₗᵢ 𝕜 T hT

/-- Cesàro averages as bounded linear operators. At zero the average is zero. -/
def averageType :=
  {X : Type u} → [MeasurableSpace X] → (𝕜 : Type v) → [RCLike 𝕜] →
  (p : ℝ≥0∞) → [Fact (1 ≤ p)] → (T : X → X) → (μ : Measure X) →
  MeasureDefinitions.PreservesMeasure T μ → ℕ → Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ

def average : averageType := by
  intro X _ 𝕜 _ p _ T μ hT n
  exact (n : 𝕜)⁻¹ • ∑ j ∈ Finset.range n,
    (composition 𝕜 p T μ hT ^ j).toContinuousLinearMap

/-- Nonnegative measurable integrals may have value infinity. The integrable
clause covers real and complex observables and also asserts integrability
of the composition. -/
def integrationStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ], MeasureDefinitions.PreservesMeasure T μ →
    (∀ h : X → ℝ≥0∞, Measurable h → (∫⁻ x, h (T x) ∂μ) = ∫⁻ x, h x ∂μ) ∧
    (∀ (𝕜 : Type v) [RCLike 𝕜] (h : X → 𝕜), Integrable h μ →
      Integrable (h ∘ T) μ ∧ (∫ x, h (T x) ∂μ) = ∫ x, h x ∂μ)

/-- Well-definedness, preservation of the Lᵖ norm, and identification of
operator powers with iterated composition. `p = ∞` is allowed. -/
def compositionStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ] (hT : MeasureDefinitions.PreservesMeasure T μ),
    (∀ f g : X → 𝕜, f =ᵐ[μ] g → f ∘ T =ᵐ[μ] g ∘ T) ∧
    (∀ h : X → 𝕜, MemLp h p μ → MemLp (h ∘ T) p μ) ∧
    (∀ h : Lp 𝕜 p μ, composition 𝕜 p T μ hT h =ᵐ[μ] h ∘ T ∧
      ‖composition 𝕜 p T μ hT h‖ = ‖h‖) ∧
    (∀ (n : ℕ) (h : Lp 𝕜 p μ),
      (composition 𝕜 p T μ hT ^ n) h =ᵐ[μ] h ∘ T^[n])

/-- Explicit essential-supremum preservation for arbitrary a.e. strongly
measurable observables, with no finite essential-bound assumption. -/
def essentialSupremumStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (T : X → X) (μ : Measure X) [IsProbabilityMeasure μ],
    MeasureDefinitions.PreservesMeasure T μ → ∀ h : X → 𝕜,
      AEStronglyMeasurable h μ → eLpNormEssSup (h ∘ T) μ = eLpNormEssSup h μ

/-- The operator estimate and its bridge to the canonical pointwise averages. -/
def averageStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ] (hT : MeasureDefinitions.PreservesMeasure T μ)
    (n : ℕ), 0 < n →
      ‖average 𝕜 p T μ hT n‖ ≤ 1 ∧
      ∀ h : Lp 𝕜 p μ, average 𝕜 p T μ hT n h =ᵐ[μ]
        MeasureDefinitions.ergodicAverage T (h : X → 𝕜) n

/-- The independent Hilbert mean theorem applied to the actual L² composition
isometry, together with the identification of its fixed space. -/
def l2MeanErgodicStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (T : X → X) (μ : Measure X) [IsProbabilityMeasure μ]
    (hT : MeasureDefinitions.PreservesMeasure T μ),
    (∀ h : Lp 𝕜 2 μ, h ∈ MeanErgodic.fixedSpace (composition 𝕜 2 T μ hT) ↔
      (h : X → 𝕜) ∘ T =ᵐ[μ] h) ∧
    ∀ h : Lp 𝕜 2 μ, Tendsto (fun n => average 𝕜 2 T μ hT n h) atTop
      (𝓝 (MeanErgodic.fixedProjection (composition 𝕜 2 T μ hT) h))

end
end Specs.D13Unified.Ch19.CompositionIsometry
