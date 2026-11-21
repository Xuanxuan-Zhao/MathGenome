import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.AlgebraNull

/-! Independent statements for paper.tex:1654–1690. The integral, ambient
restriction, ordinary a.e. predicate, and sigma-finite-set predicate are the
shared Chapter 1/4/5 objects. A threshold in `ℝ≥0` is finite, as in the
source's positive finite threshold; function values and all estimates are
in `ℝ≥0∞`, with its stipulated zero-times-infinity convention.
No size, completeness, or nonemptiness assumption is imposed on the space.
-/
open Set MeasureTheory
open scoped ENNReal NNReal
universe u
noncomputable section
namespace Specs.D11.Ch05.MarkovZeroFinite

open NonnegativeIntegral
open _root_.Specs.D11.Ch01.ExhaustionRestriction
open _root_.Specs.D11.Ch01.MeasureDefinitions
open _root_.Specs.D11.Ch04.AeCommonException

/-- Both parts of the restricted Markov estimate. -/
def restricted_markov : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞)
    (t : ℝ≥0), Measurable f → 0 < t →
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) ≤ f x} ≤
      nonnegativeIntegral_value (restrictOnSpace_value μ {x | (t : ℝ≥0∞) ≤ f x}) f ∧
    nonnegativeIntegral_value (restrictOnSpace_value μ {x | (t : ℝ≥0∞) ≤ f x}) f ≤
      nonnegativeIntegral_value μ f

/-- The inverse-threshold version, including an infinite integral. -/
def markov_inverse : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞)
    (t : ℝ≥0), Measurable f → 0 < t →
    μ {x | (t : ℝ≥0∞) ≤ f x} ≤ (t : ℝ≥0∞)⁻¹ * nonnegativeIntegral_value μ f

def zero_integral_iff : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞),
    Measurable f → (nonnegativeIntegral_value μ f = 0 ↔ aeEq_value μ f (fun _ => 0))

def finite_values_ae : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞),
    Measurable f → nonnegativeIntegral_value μ f < ∞ →
    almostEverywhere_value μ (fun x => f x < ∞)

/-- This expands to a measurable positivity set covered exactly by a sequence
of measurable finite-measure subsets of itself. -/
def sigmaFinite_positivity : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞),
    Measurable f → nonnegativeIntegral_value μ f < ∞ →
    isSigmaFiniteSet_value μ {x | 0 < f x}

end Specs.D11.Ch05.MarkovZeroFinite
