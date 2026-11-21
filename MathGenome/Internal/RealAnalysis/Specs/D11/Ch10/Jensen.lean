import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent statements for paper.tex:3558–3575, including the explicitly
adopted continuity, measurability and nondegenerate interval specialization.
Convexity is on all of ℝ and the function is finite valued. There is no
completeness or sigma-finiteness assumption on the abstract measure space.
The extended inequalities use ENNReal.ofReal on nonnegative real quantities.
Interval integrability is relative to the restricted Lebesgue measure, so
no hypotheses are imposed on values outside the interval. -/

open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch10.Jensen
open Specs.D11.Ch06.ScalarIntegral
open Specs.D11.Ch05.NonnegativeIntegral

def convex_continuous : Prop :=
  ∀ (Φ : ℝ → ℝ), ConvexOn ℝ univ Φ → Continuous Φ

def convex_measurable : Prop :=
  ∀ (Φ : ℝ → ℝ), ConvexOn ℝ univ Φ → Measurable Φ

def composition_measurable : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (f : X → ℝ) (Φ : ℝ → ℝ),
    ConvexOn ℝ univ Φ → Measurable f → Measurable (Φ ∘ f)

def jensen_integrable : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (Φ : ℝ → ℝ),
    μ univ = 1 → ConvexOn ℝ univ Φ →
    ∀ (hf : scalarIntegrable_value μ f)
      (hΦf : scalarIntegrable_value μ (Φ ∘ f)),
      Φ (scalarIntegral_value μ f hf) ≤ scalarIntegral_value μ (Φ ∘ f) hΦf

def jensen_nonnegative : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (Φ : ℝ → ℝ),
    μ univ = 1 → ConvexOn ℝ univ Φ → (∀ t, 0 ≤ Φ t) →
    ∀ (hf : scalarIntegrable_value μ f),
      ENNReal.ofReal (Φ (scalarIntegral_value μ f hf)) ≤
        nonnegativeIntegral_value μ (fun x => ENNReal.ofReal (Φ (f x)))

local notation "LReal" => NullMeasurableSpace ℝ (volume : Measure ℝ)
local notation "lebesgue" => Measure.completion (volume : Measure ℝ)

def intervalProbability_type := ℝ → ℝ → Measure LReal

def intervalProbability_value : intervalProbability_type := fun a b =>
  (ENNReal.ofReal (b - a))⁻¹ • Measure.restrict lebesgue (Icc a b : Set ℝ)

def intervalProbability_mass : Prop :=
  ∀ a b : ℝ, a < b → intervalProbability_value a b univ = 1

def interval_integral_normalization : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (f : LReal → ℝ), IntegrableOn f (Icc a b : Set ℝ) lebesgue →
    Integrable f (intervalProbability_value a b) ∧
      (∫ x, f x ∂intervalProbability_value a b) =
        (b - a)⁻¹ * ∫ x in (Icc a b : Set ℝ), f x ∂lebesgue

def interval_nonnegative_normalization : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (g : LReal → ℝ≥0∞),
    nonnegativeIntegral_value (intervalProbability_value a b) g =
      (ENNReal.ofReal (b - a))⁻¹ * nonnegativeIntegral_value (Measure.restrict lebesgue (Icc a b : Set ℝ)) g

def interval_jensen_integrable : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (f : LReal → ℝ) (Φ : ℝ → ℝ), ConvexOn ℝ univ Φ →
    IntegrableOn f (Icc a b : Set ℝ) lebesgue → IntegrableOn (Φ ∘ f) (Icc a b : Set ℝ) lebesgue →
      Φ ((b - a)⁻¹ * ∫ x in (Icc a b : Set ℝ), f x ∂lebesgue) ≤
        (b - a)⁻¹ * ∫ x in (Icc a b : Set ℝ), Φ (f x) ∂lebesgue

def interval_jensen_nonnegative : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (f : LReal → ℝ) (Φ : ℝ → ℝ), ConvexOn ℝ univ Φ →
    (∀ t, 0 ≤ Φ t) → IntegrableOn f (Icc a b : Set ℝ) lebesgue →
      ENNReal.ofReal (Φ ((b - a)⁻¹ * ∫ x in (Icc a b : Set ℝ), f x ∂lebesgue)) ≤
        (ENNReal.ofReal (b - a))⁻¹ *
          nonnegativeIntegral_value (Measure.restrict lebesgue (Icc a b : Set ℝ))
            (fun x => ENNReal.ofReal (Φ (f x)))

end Specs.D11.Ch10.Jensen
