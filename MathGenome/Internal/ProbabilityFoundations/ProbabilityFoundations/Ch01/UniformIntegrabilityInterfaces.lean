import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.ProbabilityObjects

/-! Definitions preceding Theorem 1.10 of the source. Extended nonnegative
suprema avoid totalized real suprema for unbounded or empty families. The
integrability clause records that the source family is a subset of L1.
No bridge to Mathlib UniformIntegrable is assumed here. -/

open MeasureTheory Filter
open scoped ENNReal Topology

universe u v

namespace ProbabilityFoundations.Ch01

/-- The source L1 norm, used on integrable functions. -/
noncomputable def l1Norm {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (f : S → E) : ℝ :=
  ∫ x, ‖f x‖ ∂μ

/-- Extended nonnegative integral of the strict tail. -/
noncomputable def tailIntegral {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (f : S → E) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x | R < ‖f x‖}, ‖f x‖ₑ ∂μ

/-- The supremum in a complete nonnegative lattice; the empty supremum is zero. -/
noncomputable def uniformTailIntegral {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (H : Set (S → E)) (R : ℝ) : ℝ≥0∞ :=
  ⨆ f ∈ H, tailIntegral μ f R

/-- Source tail definition for a family in L1. In particular, it applies to real and complex functions on finite measure spaces. -/
noncomputable def SourceUniformIntegrable {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (H : Set (S → E)) : Prop :=
  (∀ f ∈ H, Integrable f μ) ∧
    Tendsto (uniformTailIntegral μ H) atTop (𝓝 0)

/-- Source convergence in measure with strict real thresholds. Real and complex codomains are finite-valued; the property also makes sense without measurability hypotheses. -/
noncomputable def ConvergesInMeasure {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) (f : ℕ → S → E) (g : S → E) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ {x | ε < ‖f n x - g x‖}) atTop (𝓝 0)

/-- On a probability space convergence in probability is convergence in measure. -/
noncomputable def ConvergesInProbability {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (P : Measure S) [IsProbabilityMeasure P] (f : ℕ → S → E) (g : S → E) : Prop :=
  ConvergesInMeasure P f g

theorem l1Norm_eq_toReal_lintegral {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S) (f : S → E)
    (hf : Integrable f μ) :
    l1Norm μ f = (∫⁻ x, ‖f x‖ₑ ∂μ).toReal := by
  exact integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable

theorem tailIntegral_eq_ofReal_integral {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S) (f : S → E)
    (hf : Integrable f μ) (R : ℝ) :
    tailIntegral μ f R = ENNReal.ofReal (∫ x in {x | R < ‖f x‖}, ‖f x‖ ∂μ) := by
  exact (ofReal_integral_norm_eq_lintegral_enorm hf.restrict).symm

theorem tailIntegral_lt_top {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S) (f : S → E)
    (hf : Integrable f μ) (R : ℝ) :
    tailIntegral μ f R < ∞ := by
  exact hasFiniteIntegral_iff_enorm.mp hf.restrict.2

theorem uniformTailIntegral_empty {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S) (R : ℝ) :
    uniformTailIntegral μ (∅ : Set (S → E)) R = 0 := by
  simp [uniformTailIntegral]

theorem sourceUniformIntegrable_empty {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S) :
    SourceUniformIntegrable μ (∅ : Set (S → E)) := by
  constructor
  · simp
  · change Tendsto (fun R => uniformTailIntegral μ ∅ R) atTop (𝓝 0)
    simpa only [uniformTailIntegral_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) atTop (𝓝 0))

theorem uniformTailIntegral_zero_measure {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (H : Set (S → E)) (R : ℝ) :
    uniformTailIntegral (0 : Measure S) H R = 0 := by
  simp [uniformTailIntegral, tailIntegral]

theorem sourceUniformIntegrable_zero_measure {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (H : Set (S → E)) :
    SourceUniformIntegrable (0 : Measure S) H := by
  constructor
  · intro f hf
    exact integrable_zero_measure
  · change Tendsto (fun R => uniformTailIntegral (0 : Measure S) H R) atTop (𝓝 0)
    simpa only [uniformTailIntegral_zero_measure] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) atTop (𝓝 0))

theorem convergesInMeasure_iff_nonstrict {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S)
    (f : ℕ → S → E) (g : S → E) :
    ConvergesInMeasure μ f g ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => μ {x | ε ≤ ‖f n x - g x‖}) atTop (𝓝 0) := by
  constructor
  · intro h ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h (ε / 2) (half_pos hε)) (fun _ => zero_le) ?_
    intro n
    apply measure_mono
    intro x hx
    exact lt_of_lt_of_le (half_lt_self hε) hx
  · intro h ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h ε hε) (fun _ => zero_le) ?_
    intro n
    apply measure_mono
    intro x hx
    change ε < ‖f n x - g x‖ at hx
    change ε ≤ ‖f n x - g x‖
    exact hx.le

theorem convergesInMeasure_iff_tendstoInMeasure {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S)
    (f : ℕ → S → E) (g : S → E) :
    ConvergesInMeasure μ f g ↔ TendstoInMeasure μ f atTop g := by
  rw [convergesInMeasure_iff_nonstrict, tendstoInMeasure_iff_norm]

theorem convergesInMeasure_iff_measureReal {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (μ : Measure S) [IsFiniteMeasure μ]
    (f : ℕ → S → E) (g : S → E) :
    ConvergesInMeasure μ f g ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => μ.real {x | ε < ‖f n x - g x‖}) atTop (𝓝 0) := by
  unfold ConvergesInMeasure
  simp_rw [measureReal_def, ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)]

theorem convergesInProbability_iff {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (P : Measure S) [IsProbabilityMeasure P]
    (f : ℕ → S → E) (g : S → E) :
    ConvergesInProbability P f g ↔ ConvergesInMeasure P f g := Iff.rfl

theorem convergesInProbability_iff_tendstoInMeasure {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E] (P : Measure S) [IsProbabilityMeasure P]
    (f : ℕ → S → E) (g : S → E) :
    ConvergesInProbability P f g ↔ TendstoInMeasure P f atTop g := convergesInMeasure_iff_tendstoInMeasure P f g

end ProbabilityFoundations.Ch01
