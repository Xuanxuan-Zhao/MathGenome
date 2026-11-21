import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.DistributionFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.RCLike.Basic

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ExpandedFA.PartIV

/-- Extended weak-Lp quasi-norm. The supremum is over positive real levels. -/
noncomputable def weakLpQ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (p : ℝ) (f : Ω → E) : ℝ≥0∞ :=
  ⨆ t : ℝ, ⨆ (_ : 0 < t),
    ENNReal.ofReal t * (DistributionFunctionsSpec.DistributionValue μ f t) ^ (1 / p)

/-- The extended Banach norm, tested on measurable sets of positive measure.
The exponent is -1/p' = 1/p-1. Zero-measure sets are omitted. -/
noncomputable def weakLpN {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (p : ℝ) (f : Ω → E) : ℝ≥0∞ :=
  ⨆ A : Set Ω, ⨆ (_ : MeasurableSet A), ⨆ (_ : 0 < μ A),
    (μ A) ^ (1 / p - 1) * ∫⁻ x in A, ‖f x‖ₑ ∂μ

namespace WeakLpBanachSpec

def QuasiNormType :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
    Measure Ω → ℝ → (Ω → E) → ℝ≥0∞
noncomputable def QuasiNormValue : QuasiNormType := @weakLpQ
noncomputable def NormValue : QuasiNormType := @weakLpN

def ComparisonStatement : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ), 1 < p →
  ∀ (f : Ω → E), AEStronglyMeasurable f μ →
    weakLpQ μ p f ≤ weakLpN μ p f ∧
      weakLpN μ p f ≤ ENNReal.ofReal (p / (p - 1)) * weakLpQ μ p f

/-- All scalar a.e. classes of finite N, with the inherited vector operations,
carry exactly the N norm and are complete. The existential group structure
introduces the metric from that norm; it is not a completion adding new points. -/
def BanachStatement : Prop :=
  ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ), 1 < p →
    ∃ S : Submodule 𝕜 (Ω →ₘ[μ] 𝕜),
      (∀ f, f ∈ S ↔ weakLpN μ p f < ∞) ∧
      ∃ G : NormedAddCommGroup S,
        G.toAddCommGroup = (inferInstance : AddCommGroup S) ∧
        letI := G
        (∃ _ : NormedSpace 𝕜 S, True) ∧
        (∀ f : S, ‖f‖ = (weakLpN μ p (f : Ω →ₘ[μ] 𝕜)).toReal) ∧
        CompleteSpace S

/-- The explicit L1/Fatou completeness route, including the zero measure case. -/
def L1LimitStatement : Prop :=
  ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ), 1 < p →
  ∀ (fs : ℕ → Ω → 𝕜), (∀ n, AEStronglyMeasurable (fs n) μ) →
    (∀ n, weakLpN μ p (fs n) < ∞) →
    Tendsto (fun nm : ℕ × ℕ => weakLpN μ p (fs nm.1 - fs nm.2)) atTop (𝓝 0) →
    ∃ f : Ω → 𝕜, Integrable f μ ∧ weakLpN μ p f < ∞ ∧
      Tendsto (fun n => eLpNorm (fs n - f) 1 μ) atTop (𝓝 0) ∧
      Tendsto (fun n => weakLpN μ p (fs n - f)) atTop (𝓝 0)

def ZeroMeasureStatement : Prop :=
  ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜],
    Subsingleton (Ω →ₘ[(0 : Measure Ω)] 𝕜) ∧
      ∀ (p : ℝ), 1 < p → ∀ (f : Ω → 𝕜), weakLpN 0 p f = 0 ∧ weakLpQ 0 p f = 0

end WeakLpBanachSpec
end ExpandedFA.PartIV
