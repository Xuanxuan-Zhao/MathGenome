import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.ExhaustionRestriction
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.AeCommonException

/-! Independent statements for paper.tex:1553–1596. The integral is the
shared supremum of finite nonnegative simple minorants. All spaces and
measures are arbitrary; no completeness or size assumption is imposed.
`ℝ≥0` parametrizes exactly the finite nonnegative scalars. Indicators extend
by zero, with the `ℝ≥0∞` convention `0 * ∞ = ∞ * 0 = 0`.
-/
open Set MeasureTheory
open scoped ENNReal NNReal
universe u
noncomputable section
namespace Specs.D11.Ch05.AlgebraNull

open NonnegativeIntegral
open _root_.Specs.D11.Ch01.ExhaustionRestriction
open _root_.Specs.D11.Ch01.MeasureDefinitions
open _root_.Specs.D11.Ch04.AeCommonException

def additivity : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ≥0∞),
    Measurable f → Measurable g →
    nonnegativeIntegral_value μ (fun x => f x + g x) =
      nonnegativeIntegral_value μ f + nonnegativeIntegral_value μ g

def homogeneity : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞)
    (a : ℝ≥0), Measurable f →
    nonnegativeIntegral_value μ (fun x => (a : ℝ≥0∞) * f x) =
      (a : ℝ≥0∞) * nonnegativeIntegral_value μ f

def monotonicity : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ≥0∞),
    Measurable f → Measurable g → (∀ x, f x ≤ g x) →
    nonnegativeIntegral_value μ f ≤ nonnegativeIntegral_value μ g

/-- The restricted ambient integral is the integral of extension by zero. -/
def restriction_indicator : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞)
    (E : Set X), Measurable f → MeasurableSet E →
    nonnegativeIntegral_value (restrictOnSpace_value μ E) f =
      nonnegativeIntegral_value μ (E.indicator f)

/-- Literal multiplication by the indicator, including infinite function values. -/
def restriction_indicator_mul : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞)
    (E : Set X), Measurable f → MeasurableSet E →
    nonnegativeIntegral_value (restrictOnSpace_value μ E) f =
      nonnegativeIntegral_value μ
        (fun x => E.indicator (fun _ => (1 : ℝ≥0∞)) x * f x)

/-- The same value on the canonical trace space with its restricted measure. -/
def restriction_subtype : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞)
    (E : Set X), Measurable f → MeasurableSet E →
    nonnegativeIntegral_value (restrictToSubtype_value μ E) (fun x : E => f x) =
      nonnegativeIntegral_value μ (E.indicator f)

def ae_invariance : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ≥0∞),
    Measurable f → Measurable g → aeEq_value μ f g →
    nonnegativeIntegral_value μ f = nonnegativeIntegral_value μ g

/-- No finiteness condition on f, even on the exceptional set itself. -/
def null_integral : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞)
    (N : Set X), Measurable f → measurableNull_value μ N →
    nonnegativeIntegral_value μ (N.indicator f) = 0

def ae_monotonicity : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ≥0∞),
    Measurable f → Measurable g →
    almostEverywhere_value μ (fun x => f x ≤ g x) →
    nonnegativeIntegral_value μ f ≤ nonnegativeIntegral_value μ g

end Specs.D11.Ch05.AlgebraNull
