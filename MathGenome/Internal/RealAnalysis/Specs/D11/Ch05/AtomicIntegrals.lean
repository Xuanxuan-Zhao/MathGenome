import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import Mathlib.MeasureTheory.Measure.Count

/-!
Independent statements for the atomic-integral theorem, paper.tex:1703–1733.
All integrals are the shared supremum over finite nonnegative simple minorants.
Dirac and weighted atomic measures are on an arbitrary measurable space:
singletons need not be measurable, and no completeness or size hypothesis is
imposed. Weights and function values lie in `[0,∞]`, with `0 * ∞ = ∞ * 0 = 0`.
The locations may repeat. Natural indices enumerate the source's sequence.

The counting statement explicitly equips the countable type with the full
power-set sigma-algebra (`⊤`); every function on that space is measurable.
The last statement also records the source convention of specifying the
atomic measure only by its values on measurable sets.
-/

open Set MeasureTheory
open scoped ENNReal

universe u
noncomputable section

namespace Specs.D11.Ch05.AtomicIntegrals

open NonnegativeIntegral

def dirac_integral : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (p : X) (f : X → ℝ≥0∞),
    Measurable f → nonnegativeIntegral_value (Measure.dirac p) f = f p

def counting_integral : Prop :=
  ∀ {X : Type u} [Countable X] (f : X → ℝ≥0∞),
    letI : MeasurableSpace X := ⊤
    nonnegativeIntegral_value (Measure.count : Measure X) f = ∑' x, f x

def atomic_integral : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (p : ℕ → X) (a : ℕ → ℝ≥0∞)
    (f : X → ℝ≥0∞), Measurable f →
    nonnegativeIntegral_value (Measure.sum (fun n => a n • Measure.dirac (p n))) f =
      ∑' n, a n * f (p n)

def atomic_integral_of_values : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (p : ℕ → X) (a : ℕ → ℝ≥0∞) (f : X → ℝ≥0∞),
    Measurable f →
    (∀ (E : Set X), MeasurableSet E →
      μ E = ∑' n, a n * E.indicator (fun _ => (1 : ℝ≥0∞)) (p n)) →
    nonnegativeIntegral_value μ f = ∑' n, a n * f (p n)

end Specs.D11.Ch05.AtomicIntegrals
