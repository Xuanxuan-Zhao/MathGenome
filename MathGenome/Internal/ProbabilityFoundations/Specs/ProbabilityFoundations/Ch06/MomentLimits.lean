import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.VaryingMapping
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Independent statements for paper.tex, Proposition `prop:p06-moments`
(lines 1699–1737). All statements concern laws, hence allow random variables
on unrelated probability spaces. UI means integrability and uniform vanishing
of the strict absolute tails under the respective laws. -/
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch06.MomentLimits
universe u
noncomputable section

/-- Uniform integrability under a sequence of possibly different laws.
The epsilon formulation is precisely uniform vanishing of the tail integrals. -/
def LawUniformIntegrable {S : Type u} [MeasurableSpace S]
    (μs : ℕ → ProbabilityMeasure S) (h : S → ℝ) : Prop :=
  (∀ n, Integrable h (μs n : Measure S)) ∧
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧ ∀ n,
    (∫ x in {x | R < |h x|}, |h x| ∂(μs n : Measure S)) < ε

/-- Extended absolute p-moment, allowing infinity. -/
def absoluteMoment (μ : ProbabilityMeasure ℝ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂(μ : Measure ℝ)

def momentLowerBoundType : Prop :=
  ∀ (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (p : ℝ), 0 < p → Tendsto μs atTop (𝓝 μ) →
    absoluteMoment μ p ≤ liminf (fun n => absoluteMoment (μs n) p) atTop

def momentConvergenceType : Prop :=
  ∀ (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (p : ℝ), 0 < p → Tendsto μs atTop (𝓝 μ) →
    LawUniformIntegrable μs (fun x => |x| ^ p) →
    Integrable (fun x : ℝ => |x| ^ p) (μ : Measure ℝ) ∧
    Tendsto (fun n => ∫ x, |x| ^ p ∂(μs n : Measure ℝ)) atTop
      (𝓝 (∫ x, |x| ^ p ∂(μ : Measure ℝ))) ∧
    absoluteMoment μ p < ∞ ∧
    Tendsto (fun n => absoluteMoment (μs n) p) atTop (𝓝 (absoluteMoment μ p))

def expectationConvergenceType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (h : S → ℝ), Measurable h → Tendsto μs atTop (𝓝 μ) →
    (∀ᵐ x ∂(μ : Measure S), ContinuousAt h x) →
    LawUniformIntegrable μs h →
    Integrable h (μ : Measure S) ∧
    Tendsto (fun n => ∫ x, h x ∂(μs n : Measure S)) atTop
      (𝓝 (∫ x, h x ∂(μ : Measure S)))

def polynomialGrowthType : Prop :=
  ∀ (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (p : ℝ), 0 < p → Tendsto μs atTop (𝓝 μ) →
    LawUniformIntegrable μs (fun x => |x| ^ p) →
    ∀ (h : ℝ → ℝ) (C : ℝ), Continuous h → 0 ≤ C →
    (∀ x, |h x| ≤ C * (1 + |x| ^ p)) →
    Integrable h (μ : Measure ℝ) ∧
    Tendsto (fun n => ∫ x, h x ∂(μs n : Measure ℝ)) atTop
      (𝓝 (∫ x, h x ∂(μ : Measure ℝ)))

/-- The explicit law: mass 1/(n+1) at n+1, remaining mass at zero. -/
def spikeMeasure (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 / ((n : ℝ) + 1)) • Measure.dirac ((n : ℝ) + 1) +
    ENNReal.ofReal (1 - 1 / ((n : ℝ) + 1)) • Measure.dirac 0

def spikeCounterexampleType : Prop :=
  (∀ n, IsProbabilityMeasure (spikeMeasure n)) ∧
  (∃ μs : ℕ → ProbabilityMeasure ℝ,
    (∀ n, (μs n : Measure ℝ) = spikeMeasure n) ∧
    Tendsto μs atTop (𝓝 (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ n, Integrable (fun x : ℝ => x) (μs n : Measure ℝ)) ∧
    (∀ n, (∫ x : ℝ, |x| ∂(μs n : Measure ℝ)) = 1) ∧
    (∀ n, (∫ x : ℝ, x ∂(μs n : Measure ℝ)) = 1) ∧
    ¬ Tendsto (fun n => ∫ x : ℝ, x ∂(μs n : Measure ℝ)) atTop (𝓝 0))

end
end Specs.ProbabilityFoundations.Ch06.MomentLimits
