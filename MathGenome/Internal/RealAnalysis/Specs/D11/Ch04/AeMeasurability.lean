import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.AeCommonException
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.ScalarOperationsLimits

/-!
Independent statements for paper.tex:1358–1377: a.e. changes and a.e. limits.
All measurability conclusions use the original source sigma-algebra. The
extended target is `EReal`, including both infinities, with its Borel structure.
The source's ordinary a.e. relation and measure completeness are reused from
Chapter 1 and the common-exception interface. No finiteness or sigma-finiteness
is assumed. The real and complex statements retain finite-valued versions.
-/

open Set Filter MeasureTheory MeasurableSpace
open scoped Topology
universe u

namespace Specs.D11.Ch04.AeMeasurability

open Specs.D11.Ch01.MeasureDefinitions
open Specs.D11.Ch04.AeCommonException

/-- Null modifications of a measurable ereal function on a complete space. -/
def ereal_ae_change : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f g : X → EReal),
    isComplete_value μ → @Measurable X EReal _ (borel EReal) f →
    aeEq_value μ f g → @Measurable X EReal _ (borel EReal) g

/-- A measurable version of a specified almost-everywhere limit. -/
def ereal_ae_limit_version : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → EReal) (g : X → EReal),
    (∀ n, @Measurable X EReal _ (borel EReal) (f n)) →
    almostEverywhere_value μ
      (fun x => Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
    ∃ h : X → EReal, @Measurable X EReal _ (borel EReal) h ∧ aeEq_value μ h g

/-- Completeness makes the specified almost-everywhere limit measurable. -/
def ereal_ae_limit_complete : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → EReal) (g : X → EReal),
    isComplete_value μ →
    (∀ n, @Measurable X EReal _ (borel EReal) (f n)) →
    almostEverywhere_value μ
      (fun x => Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
    @Measurable X EReal _ (borel EReal) g

/-- Null modifications of a measurable real function on a complete space. -/
def real_ae_change : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ),
    isComplete_value μ → @Measurable X ℝ _ (borel ℝ) f →
    aeEq_value μ f g → @Measurable X ℝ _ (borel ℝ) g

/-- A measurable version of a specified almost-everywhere limit. -/
def real_ae_limit_version : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ) (g : X → ℝ),
    (∀ n, @Measurable X ℝ _ (borel ℝ) (f n)) →
    almostEverywhere_value μ
      (fun x => Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
    ∃ h : X → ℝ, @Measurable X ℝ _ (borel ℝ) h ∧ aeEq_value μ h g

/-- Completeness makes the specified almost-everywhere limit measurable. -/
def real_ae_limit_complete : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ) (g : X → ℝ),
    isComplete_value μ →
    (∀ n, @Measurable X ℝ _ (borel ℝ) (f n)) →
    almostEverywhere_value μ
      (fun x => Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
    @Measurable X ℝ _ (borel ℝ) g

/-- Null modifications of a measurable complex function on a complete space. -/
def complex_ae_change : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f g : X → ℂ),
    isComplete_value μ → @Measurable X ℂ _ (borel ℂ) f →
    aeEq_value μ f g → @Measurable X ℂ _ (borel ℂ) g

/-- A measurable version of a specified almost-everywhere limit. -/
def complex_ae_limit_version : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℂ) (g : X → ℂ),
    (∀ n, @Measurable X ℂ _ (borel ℂ) (f n)) →
    almostEverywhere_value μ
      (fun x => Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
    ∃ h : X → ℂ, @Measurable X ℂ _ (borel ℂ) h ∧ aeEq_value μ h g

/-- Completeness makes the specified almost-everywhere limit measurable. -/
def complex_ae_limit_complete : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℂ) (g : X → ℂ),
    isComplete_value μ →
    (∀ n, @Measurable X ℂ _ (borel ℂ) (f n)) →
    almostEverywhere_value μ
      (fun x => Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
    @Measurable X ℂ _ (borel ℂ) g

end Specs.D11.Ch04.AeMeasurability
