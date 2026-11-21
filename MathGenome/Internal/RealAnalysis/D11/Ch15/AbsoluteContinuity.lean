import MathGenome.Internal.RealAnalysis.D11.Ch14.TotalVariation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.AbsoluteContinuity

/-! Absolute continuity on the fixed sigma-algebra (`paper.tex:4806–4814`).
No finiteness, sigma-finiteness, or completeness is imposed on the reference
measure. The common scalar interface includes both real and complex measures.
-/

open Set MeasureTheory

universe u v

namespace D11.Ch15.AbsoluteContinuity

/-- Positive absolute continuity, with the dominated measure first. -/
def positiveAbsolutelyContinuous {α : Type u} [MeasurableSpace α]
    (ν μ : Measure α) : Prop := ν ≪ μ

/-- Scalar absolute continuity is positive absolute continuity of variation. -/
def scalarAbsolutelyContinuous {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K)
    (μ : Measure α) : Prop := Ch14.TotalVariation.totalVariation ν ≪ μ

/-- Native outer values do not add any tests beyond the source sigma-algebra. -/
theorem positive_iff {α : Type u} [MeasurableSpace α] (ν μ : Measure α) :
    positiveAbsolutelyContinuous ν μ ↔
      ∀ E, MeasurableSet E → μ E = 0 → ν E = 0 := by
  constructor
  · intro h E _ hE
    exact h hE
  · intro h
    exact Measure.AbsolutelyContinuous.mk fun E hE hzero => h E hE hzero

theorem scalar_iff_variation {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K) (μ : Measure α) :
    scalarAbsolutelyContinuous ν μ ↔
      positiveAbsolutelyContinuous (Ch14.TotalVariation.totalVariation ν) μ := Iff.rfl

/-- On a reference-null measurable set, every measurable subset is null too.
The shared partition criterion therefore turns vanishing values into vanishing
variation. No hypothesis about the total mass of the reference is used. -/
theorem scalar_iff {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K) (μ : Measure α) :
    scalarAbsolutelyContinuous ν μ ↔
      ∀ E, MeasurableSet E → μ E = 0 → ν E = 0 := by
  rw [scalar_iff_variation, positive_iff]
  constructor
  · intro h E hE hzero
    exact (Ch14.TotalVariation.totalVariation_null_iff ν E hE).mp (h E hE hzero)
      E hE (Subset.refl E)
  · intro h E hE hzero
    apply (Ch14.TotalVariation.totalVariation_null_iff ν E hE).mpr
    intro A hA hAE
    exact h A hA (measure_mono_null hAE hzero)

open Ch01.MeasureDefinitions Ch14.ScalarInterfaces

/-- The predicate agrees with the literal positive source maps Σ → [0,∞]. -/
theorem source_positive_iff {α : Type u} [MeasurableSpace α]
    (ν μ : SourceMeasure α) :
    positiveAbsolutelyContinuous (measureOfSource ν) (measureOfSource μ) ↔
      ∀ E, μ.value E = 0 → ν.value E = 0 := by
  rw [positive_iff]
  constructor
  · intro h E hzero
    have hz : measureOfSource μ E.1 = 0 := by
      rw [measureOfSource_apply μ E.1 E.2]
      exact hzero
    simpa only [measureOfSource_apply ν E.1 E.2] using h E.1 E.2 hz
  · intro h E hE hzero
    rw [measureOfSource_apply ν E hE]
    apply h ⟨E, hE⟩
    simpa only [measureOfSource_apply μ E hE] using hzero

/-- The scalar null-value characterization on exactly the original domain Σ. -/
theorem source_scalar_iff {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : SourceScalarMeasure α K)
    (μ : SourceMeasure α) :
    scalarAbsolutelyContinuous (scalarOfSource ν) (measureOfSource μ) ↔
      ∀ E, μ.value E = 0 → ν.value E = 0 := by
  rw [scalar_iff]
  constructor
  · intro h E hzero
    have hz : measureOfSource μ E.1 = 0 := by
      rw [measureOfSource_apply μ E.1 E.2]
      exact hzero
    simpa only [scalarOfSource_apply ν E.1 E.2] using h E.1 E.2 hz
  · intro h E hE hzero
    rw [scalarOfSource_apply ν E hE]
    apply h ⟨E, hE⟩
    simpa only [measureOfSource_apply μ E hE] using hzero

end D11.Ch15.AbsoluteContinuity
