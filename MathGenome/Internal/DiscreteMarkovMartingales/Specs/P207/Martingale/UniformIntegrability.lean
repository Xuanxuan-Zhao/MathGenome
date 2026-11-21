import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Independent specification of paper.tex §6.1 (W30), Definition and Proposition.
The parameter space is arbitrary; no measurable structure or separability is
required on the normed codomain. In particular all real and complex Banach
spaces are included. The results are stated for finite measures, hence apply
to every probability space. Extended nonnegative suprema include empty families.
The doubling example is allocated separately. -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

universe u v w

namespace Specs.P207.Martingale.UniformIntegrability

noncomputable def tailIntegralValue {Ω : Type u} {E : Type v}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (f : Ω → E) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x | R < ‖f x‖}, ‖f x‖ₑ ∂μ

def tailIntegralType := ∀ {Ω : Type u} {E : Type v}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (f : Ω → E) (R : ℝ), ℝ≥0∞

noncomputable def uniformTailIntegralValue {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : I → Ω → E) (R : ℝ) : ℝ≥0∞ :=
  ⨆ i, tailIntegralValue μ (X i) R

def uniformTailIntegralType := ∀ {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : I → Ω → E) (R : ℝ), ℝ≥0∞

noncomputable def nonstrictUniformTailIntegralValue
    {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : I → Ω → E) (R : ℝ) : ℝ≥0∞ :=
  ⨆ i, ∫⁻ x in {x | R ≤ ‖X i x‖}, ‖X i x‖ₑ ∂μ

def nonstrictUniformTailIntegralType := ∀ {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : I → Ω → E) (R : ℝ), ℝ≥0∞

/-- Specification value of the single canonical source predicate. The integral
clause makes explicit that the source family consists of Bochner L¹ variables. -/
noncomputable def SourceUniformIntegrableValue
    {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : I → Ω → E) : Prop :=
  (∀ i, Integrable (X i) μ) ∧
    Tendsto (uniformTailIntegralValue μ X) atTop (𝓝 0)

def SourceUniformIntegrableType := ∀ {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : I → Ω → E), Prop

def tailIntegral_eq_ofReal_integralType : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (f : Ω → E), Integrable f μ → ∀ R : ℝ,
    tailIntegralValue μ f R =
      ENNReal.ofReal (∫ x, {x | R < ‖f x‖}.indicator (fun x => ‖f x‖) x ∂μ)

def tailIntegral_lt_topType : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (f : Ω → E), Integrable f μ → ∀ R : ℝ,
    tailIntegralValue μ f R < ∞

def uniformTailIntegral_emptyType : Prop :=
  ∀ {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [IsEmpty I]
    (μ : Measure Ω) (X : I → Ω → E) (R : ℝ),
    uniformTailIntegralValue μ X R = 0 ∧
      nonstrictUniformTailIntegralValue μ X R = 0

def sourceUniformIntegrable_emptyType : Prop :=
  ∀ {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [IsEmpty I]
    (μ : Measure Ω) (X : I → Ω → E), SourceUniformIntegrableValue μ X

def sourceUniformIntegrable_iff_nonstrictType : Prop :=
  ∀ {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : I → Ω → E),
    SourceUniformIntegrableValue μ X ↔
      (∀ i, Integrable (X i) μ) ∧
        Tendsto (nonstrictUniformTailIntegralValue μ X) atTop (𝓝 0)

def sourceUniformIntegrable_iff_uniformIntegrableType : Prop :=
  ∀ {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : I → Ω → E),
    SourceUniformIntegrableValue μ X ↔ MeasureTheory.UniformIntegrable X 1 μ

def sourceUniformIntegrable_firstMomentSup_lt_topType : Prop :=
  ∀ {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : I → Ω → E),
    SourceUniformIntegrableValue μ X → (⨆ i, ∫⁻ x, ‖X i x‖ₑ ∂μ) < ∞

def sourceUniformIntegrable_boundedType : Prop :=
  ∀ {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : I → Ω → E),
    SourceUniformIntegrableValue μ X →
      ∃ C : ℝ≥0, ∀ i, (∫ x, ‖X i x‖ ∂μ) ≤ C

end Specs.P207.Martingale.UniformIntegrability
