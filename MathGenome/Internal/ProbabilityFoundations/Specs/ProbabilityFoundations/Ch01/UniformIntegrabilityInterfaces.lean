import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.ProbabilityObjects

/-! Independent specification of paper.tex, section 1.5, definitions before
Theorem 1.10. These interfaces also apply to arbitrary normed additive groups.
The source uses them on finite measure spaces with real or complex values.
There is no completeness assumption on the measure space. -/

open MeasureTheory Filter
open scoped ENNReal Topology

universe u v

namespace Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces

def l1NormType := ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (f : S → E), ℝ

noncomputable def l1NormValue {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (f : S → E) : ℝ :=
  ∫ x, ‖f x‖ ∂μ

def tailIntegralType := ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (f : S → E) (R : ℝ), ℝ≥0∞

noncomputable def tailIntegralValue {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (f : S → E) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x | R < ‖f x‖}, ‖f x‖ₑ ∂μ

def uniformTailIntegralType := ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (H : Set (S → E)) (R : ℝ), ℝ≥0∞

noncomputable def uniformTailIntegralValue {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (H : Set (S → E)) (R : ℝ) : ℝ≥0∞ :=
  ⨆ f ∈ H, tailIntegralValue μ f R

def SourceUniformIntegrableType := ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (H : Set (S → E)), Prop

noncomputable def SourceUniformIntegrableValue {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (H : Set (S → E)) : Prop :=
  (∀ f ∈ H, Integrable f μ) ∧
    Tendsto (uniformTailIntegralValue μ H) atTop (𝓝 0)

def ConvergesInMeasureType := ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (f : ℕ → S → E) (g : S → E), Prop

noncomputable def ConvergesInMeasureValue {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (f : ℕ → S → E) (g : S → E) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ {x | ε < ‖f n x - g x‖}) atTop (𝓝 0)

def ConvergesInProbabilityType := ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (P : Measure S) [IsProbabilityMeasure P] (f : ℕ → S → E) (g : S → E), Prop

noncomputable def ConvergesInProbabilityValue {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (P : Measure S) [IsProbabilityMeasure P] (f : ℕ → S → E) (g : S → E) : Prop :=
  ConvergesInMeasureValue P f g

def l1Norm_eq_toReal_lintegralType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S) (f : S → E)
    (hf : Integrable f μ),
    l1NormValue μ f = (∫⁻ x, ‖f x‖ₑ ∂μ).toReal

def tailIntegral_eq_ofReal_integralType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S) (f : S → E)
    (hf : Integrable f μ) (R : ℝ),
    tailIntegralValue μ f R = ENNReal.ofReal (∫ x in {x | R < ‖f x‖}, ‖f x‖ ∂μ)

def tailIntegral_lt_topType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S) (f : S → E)
    (hf : Integrable f μ) (R : ℝ),
    tailIntegralValue μ f R < ∞

def uniformTailIntegral_emptyType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S) (R : ℝ),
    uniformTailIntegralValue μ (∅ : Set (S → E)) R = 0

def sourceUniformIntegrable_emptyType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S),
    SourceUniformIntegrableValue μ (∅ : Set (S → E))

def uniformTailIntegral_zero_measureType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (H : Set (S → E)) (R : ℝ),
    uniformTailIntegralValue (0 : Measure S) H R = 0

def sourceUniformIntegrable_zero_measureType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (H : Set (S → E)),
    SourceUniformIntegrableValue (0 : Measure S) H

def convergesInMeasure_iff_nonstrictType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S)
    (f : ℕ → S → E) (g : S → E),
    ConvergesInMeasureValue μ f g ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => μ {x | ε ≤ ‖f n x - g x‖}) atTop (𝓝 0)

def convergesInMeasure_iff_tendstoInMeasureType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S)
    (f : ℕ → S → E) (g : S → E),
    ConvergesInMeasureValue μ f g ↔ TendstoInMeasure μ f atTop g

def convergesInMeasure_iff_measureRealType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S) [IsFiniteMeasure μ]
    (f : ℕ → S → E) (g : S → E),
    ConvergesInMeasureValue μ f g ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => μ.real {x | ε < ‖f n x - g x‖}) atTop (𝓝 0)

def convergesInProbability_iffType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (P : Measure S) [IsProbabilityMeasure P]
    (f : ℕ → S → E) (g : S → E),
    ConvergesInProbabilityValue P f g ↔ ConvergesInMeasureValue P f g

def convergesInProbability_iff_tendstoInMeasureType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (P : Measure S) [IsProbabilityMeasure P]
    (f : ℕ → S → E) (g : S → E),
    ConvergesInProbabilityValue P f g ↔ TendstoInMeasure P f atTop g

end Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces
