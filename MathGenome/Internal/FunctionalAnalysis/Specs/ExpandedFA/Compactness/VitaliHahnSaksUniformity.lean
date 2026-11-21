import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Independent specification: uniform variation in Vitali--Hahn--Saks

The uniformity stage of `fa2:p2:vitali-hahn-saks`, paper.tex:9734--9794.
The measurable space is arbitrary and the positive control measure is finite.
`SignedMeasure` and `ComplexMeasure` are the canonical countably additive
scalar measures. Their evaluations are finite scalars; total variation for
signed measures is the Hahn--Jordan measure, and for complex measures is
`VectorMeasure.variation`, defined using finite measurable partitions.
Absolute continuity below means vanishing on every null measurable set.
Convergence is on every measurable set, with a possibly different scalar limit
for each set. No bound uniform in `n` and no convergence of variations is assumed.
The conclusion takes a genuine supremum in the extended nonnegative reals.
The zero control measure and empty underlying space are included.
-/

open Filter MeasureTheory
open scoped Topology ENNReal

universe u

namespace Specs.ExpandedFA.Compactness.VitaliHahnSaksUniformity

/-- Signed-measure uniform variation absolute continuity. -/
def uniformVariationSigned : Prop :=
  ∀ {α : Type u} [MeasurableSpace α]
    (ρ : Measure α) [IsFiniteMeasure ρ] (μ : ℕ → SignedMeasure α),
    (∀ n s, MeasurableSet s → ρ s = 0 → μ n s = 0) →
    (∀ s, MeasurableSet s → ∃ l : ℝ,
      Tendsto (fun n => μ n s) atTop (𝓝 l)) →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
      ρ s < ENNReal.ofReal δ → (⨆ n, (μ n).totalVariation s) < ENNReal.ofReal ε

/-- Complex-measure uniform variation absolute continuity. -/
def uniformVariationComplex : Prop :=
  ∀ {α : Type u} [MeasurableSpace α]
    (ρ : Measure α) [IsFiniteMeasure ρ] (μ : ℕ → ComplexMeasure α),
    (∀ n s, MeasurableSet s → ρ s = 0 → μ n s = 0) →
    (∀ s, MeasurableSet s → ∃ l : ℂ,
      Tendsto (fun n => μ n s) atTop (𝓝 l)) →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
      ρ s < ENNReal.ofReal δ → (⨆ n, (μ n).variation s) < ENNReal.ofReal ε

end Specs.ExpandedFA.Compactness.VitaliHahnSaksUniformity
