import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework
import Mathlib.Topology.Order.Compact

/-!
Independent specification of paper.tex, lines 1738–1747. All spaces in the
tightness definitions are metric with exactly their Borel sigma algebra.
The supremum lives in ℝ≥0∞, where the supremum of an empty family is zero.
The quantified strict criterion is equivalent after shrinking epsilon; for a
fixed epsilon, pointwise strict bounds alone need not give a strict supremum.
-/

open MeasureTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch06.Tightness

universe u
noncomputable section

def uniformlyTightType := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S], Set (ProbabilityMeasure S) → Prop

def uniformlyTightValue : uniformlyTightType := fun {S} _ _ _ A =>
  ∀ ε : ℝ, 0 < ε → ∃ K : Set S, IsCompact K ∧
    (⨆ μ ∈ A, (μ : Measure S) Kᶜ) < ENNReal.ofReal ε

def tightType := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S], ProbabilityMeasure S → Prop

def tightValue : tightType := fun μ => uniformlyTightValue {μ}

def diracLawType := ∀ {S : Type u} [MeasurableSpace S], S → ProbabilityMeasure S

def diracLawValue : diracLawType := fun x =>
  ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩

def naturalDiracFamilyType := Set (ProbabilityMeasure ℝ)

def naturalDiracFamilyValue : naturalDiracFamilyType :=
  (fun n : ℕ => diracLawValue (n : ℝ)) '' Set.Ici 1

def uniformlyTightIffType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (A : Set (ProbabilityMeasure S)),
  uniformlyTightValue A ↔ ∀ ε : ℝ, 0 < ε →
    ∃ K : Set S, IsCompact K ∧ ∀ μ ∈ A, (μ : Measure S) Kᶜ < ENNReal.ofReal ε

def uniformlyTightEmptyType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S],
  uniformlyTightValue (∅ : Set (ProbabilityMeasure S))

def tightIffType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ : ProbabilityMeasure S),
  tightValue μ ↔ ∀ ε : ℝ, 0 < ε →
    ∃ K : Set S, IsCompact K ∧ (μ : Measure S) Kᶜ < ENNReal.ofReal ε

def diracLawTightType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (x : S), tightValue (diracLawValue x)

def naturalDiracTightType : Prop :=
  ∀ n : ℕ, 1 ≤ n → tightValue (diracLawValue (n : ℝ))

def naturalDiracFamilyNotUniformlyTightType : Prop :=
  ¬ uniformlyTightValue naturalDiracFamilyValue

end
end Specs.ProbabilityFoundations.Ch06.Tightness
