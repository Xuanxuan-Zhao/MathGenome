import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.EssSup

/-! Independent specification for paper.tex, Definition p102:U2-01 (856–870).
The norm of a real or complex value is its absolute value. All sizes and integrals
are extended nonnegative values, so no integrability or finiteness is implicit. -/

open MeasureTheory Set
open scoped ENNReal

namespace P102.U2

/-- Strict distribution function, extended to all real levels for convenience. -/
noncomputable def distribution {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    (μ : Measure α) (h : α → F) (t : ℝ) : ℝ≥0∞ := μ {x | t < ‖h x‖}

/-- Finite-exponent weak size; the asserted range is `0 < q`. -/
noncomputable def weakSize {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    (μ : Measure α) (q : ℝ) (h : α → F) : ℝ≥0∞ :=
  ⨆ t : ℝ, ⨆ (_ : 0 < t), ENNReal.ofReal t * distribution μ h t ^ (1 / q)

/-- The weak size at exponent infinity is the essential supremum of the norm. -/
noncomputable def weakSizeInfinity {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] (μ : Measure α) (h : α → F) : ℝ≥0∞ :=
  essSup (fun x => ENNReal.ofReal ‖h x‖) μ

namespace WeakNormsSpec

def DistributionType := ∀ {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F],
  Measure α → (α → F) → ℝ → ℝ≥0∞
noncomputable def DistributionValue : DistributionType := @distribution

def WeakSizeType := ∀ {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F],
  Measure α → ℝ → (α → F) → ℝ≥0∞
noncomputable def WeakSizeValue : WeakSizeType := @weakSize

def WeakSizeInfinityType := ∀ {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F],
  Measure α → (α → F) → ℝ≥0∞
noncomputable def WeakSizeInfinityValue : WeakSizeInfinityType := @weakSizeInfinity

/-- Measurability of the norm suffices, in particular for measurable real or complex h.
No sigma-finiteness is required, and the identity includes infinite values. -/
def LayerCake : Prop :=
  ∀ {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    (μ : Measure α) (h : α → F), AEMeasurable (fun x => ‖h x‖) μ →
    ∀ q : ℝ, 0 < q →
      (∫⁻ x, ENNReal.ofReal (‖h x‖ ^ q) ∂μ) =
        ∫⁻ t in Ioi 0, ENNReal.ofReal (q * t ^ (q - 1)) * distribution μ h t

/-- The normalized local weak-L1 estimate with exactly the source constant.
Division and powers are taken in ENNReal, retaining zero and infinite weak sizes. -/
def LocalEstimate : Prop :=
  ∀ {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    (μ : Measure α) (h : α → F), AEMeasurable (fun x => ‖h x‖) μ →
    ∀ (δ : ℝ), 0 < δ → δ < 1 →
    ∀ (E : Set α), MeasurableSet E → 0 < μ E → μ E < ∞ →
      ((∫⁻ x in E, ENNReal.ofReal (‖h x‖ ^ δ) ∂μ) / μ E) ^ (1 / δ) ≤
        ENNReal.ofReal ((1 - δ) ^ (-1 / δ)) * (weakSize μ 1 h / μ E)

end WeakNormsSpec
end P102.U2
