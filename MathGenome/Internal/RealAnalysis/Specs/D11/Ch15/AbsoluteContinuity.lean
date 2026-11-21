import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.TotalVariation
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-! Independent statements for `paper.tex:4806–4814`.

Both measures use one and the same `MeasurableSpace`. The positive reference
measure is arbitrary. Native positive absolute continuity is compared explicitly
with testing just the original measurable sets. Scalar absolute continuity uses
the shared partition variation; the null-value equivalence also holds for general
normed-group-valued measures, so in particular for the finite real and complex
measures of the manuscript. The source-map statements retain domain exactly Σ.
-/

open Set MeasureTheory

universe u v

namespace Specs.D11.Ch15.AbsoluteContinuity

abbrev positiveAbsolutelyContinuous_type :=
  ∀ {α : Type u} [MeasurableSpace α], Measure α → Measure α → Prop

def positiveAbsolutelyContinuous_value : positiveAbsolutelyContinuous_type.{u} :=
  fun ν μ => ν ≪ μ

abbrev scalarAbsolutelyContinuous_type :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K],
    VectorMeasure α K → Measure α → Prop

def scalarAbsolutelyContinuous_value : scalarAbsolutelyContinuous_type.{u,v} :=
  fun ν μ => Ch14.TotalVariation.totalVariation_value ν ≪ μ

def positive_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν μ : Measure α),
    positiveAbsolutelyContinuous_value ν μ ↔
      ∀ E, MeasurableSet E → μ E = 0 → ν E = 0

def scalar_iff_variation : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K) (μ : Measure α),
    scalarAbsolutelyContinuous_value ν μ ↔
      positiveAbsolutelyContinuous_value (Ch14.TotalVariation.totalVariation_value ν) μ

def scalar_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K) (μ : Measure α),
    scalarAbsolutelyContinuous_value ν μ ↔
      ∀ E, MeasurableSet E → μ E = 0 → ν E = 0

def source_positive_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α]
    (ν μ : _root_.D11.Ch01.MeasureDefinitions.SourceMeasure α),
    positiveAbsolutelyContinuous_value
      (Ch01.MeasureDefinitions.measureOfSource_value ν)
      (Ch01.MeasureDefinitions.measureOfSource_value μ) ↔
        ∀ E, μ.value E = 0 → ν.value E = 0

def source_scalar_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : _root_.D11.Ch14.ScalarInterfaces.SourceScalarMeasure α K)
    (μ : _root_.D11.Ch01.MeasureDefinitions.SourceMeasure α),
    scalarAbsolutelyContinuous_value
      (Ch14.ScalarInterfaces.scalarOfSource_value ν)
      (Ch01.MeasureDefinitions.measureOfSource_value μ) ↔
        ∀ E, μ.value E = 0 → ν.value E = 0

end Specs.D11.Ch15.AbsoluteContinuity
