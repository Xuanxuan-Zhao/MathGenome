import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.LawsAndTransfer
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
Proposition 1.13, paper.tex:449–481. `NullMeasurableSpace Ω P` has precisely
P's completed sigma algebra, and `P.completion` is its canonical completed measure.
The statements hold for arbitrary measures, in particular for every probability
measure on its original, possibly incomplete, sigma algebra. Metric targets carry
the Borel sigma algebra; no completeness or Polish assumption is made.
-/

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions

universe u v

def countablyGeneratedVersionType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace.CountablyGenerated S]
  (P : Measure Ω) (X : Ω → S), @Measurable (NullMeasurableSpace Ω P) S _ _ X →
  ∃ X0 : Ω → S, Measurable X0 ∧ X =ᵐ[P] X0 ∧
    ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ ∀ ω, ω ∉ N → X0 ω = X ω

def metricVersionType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [SeparableSpace S] [Nonempty S] (P : Measure Ω) (X : Ω → S),
  @Measurable (NullMeasurableSpace Ω P) S _ _ X →
  ∃ X0 : Ω → S, Measurable X0 ∧ X =ᵐ[P] X0 ∧
    ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ ∀ ω, ω ∉ N → X0 ω = X ω

def realVersionType : Prop := ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ),
  @Measurable (NullMeasurableSpace Ω P) ℝ _ _ X →
  ∃ X0 : Ω → ℝ, Measurable X0 ∧ X =ᵐ[P] X0 ∧
    ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ ∀ ω, ω ∉ N → X0 ω = X ω

def extendedRealVersionType : Prop := ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → EReal),
  @Measurable (NullMeasurableSpace Ω P) EReal _ _ X →
  ∃ X0 : Ω → EReal, Measurable X0 ∧ X =ᵐ[P] X0 ∧
    ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ ∀ ω, ω ∉ N → X0 ω = X ω

def nonnegativeVersionType : Prop := ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ≥0∞),
  @Measurable (NullMeasurableSpace Ω P) ℝ≥0∞ _ _ X →
  ∃ X0 : Ω → ℝ≥0∞, Measurable X0 ∧ X =ᵐ[P] X0 ∧
    ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ ∀ ω, ω ∉ N → X0 ω = X ω

def lawPreservedType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
  (X X0 : Ω → S), @Measurable (NullMeasurableSpace Ω P) S _ _ X →
  Measurable X0 → X =ᵐ[P] X0 →
  @Measure.map (NullMeasurableSpace Ω P) S _ _ X P.completion = Measure.map X0 P

def nonnegativeExpectationPreservedType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
  (X X0 : Ω → S), @Measurable (NullMeasurableSpace Ω P) S _ _ X →
  Measurable X0 → X =ᵐ[P] X0 →
  ∀ f : S → ℝ≥0∞, Measurable f →
  (∫⁻ ω : NullMeasurableSpace Ω P, f (X ω) ∂P.completion) = ∫⁻ ω, f (X0 ω) ∂P

def realIntegrabilityPreservedType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
  (X X0 : Ω → S), @Measurable (NullMeasurableSpace Ω P) S _ _ X →
  Measurable X0 → X =ᵐ[P] X0 →
  ∀ f : S → ℝ, Measurable f →
  (Integrable (fun (ω : NullMeasurableSpace Ω P) => f (X ω)) P.completion ↔ Integrable (fun ω => f (X0 ω)) P)

def realExpectationPreservedType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
  (X X0 : Ω → S), @Measurable (NullMeasurableSpace Ω P) S _ _ X →
  Measurable X0 → X =ᵐ[P] X0 →
  ∀ f : S → ℝ, Measurable f → Integrable (fun ω => f (X0 ω)) P →
  (∫ ω : NullMeasurableSpace Ω P, f (X ω) ∂P.completion) = ∫ ω, f (X0 ω) ∂P

def complexIntegrabilityPreservedType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
  (X X0 : Ω → S), @Measurable (NullMeasurableSpace Ω P) S _ _ X →
  Measurable X0 → X =ᵐ[P] X0 →
  ∀ f : S → ℂ, Measurable f →
  (Integrable (fun (ω : NullMeasurableSpace Ω P) => f (X ω)) P.completion ↔ Integrable (fun ω => f (X0 ω)) P)

def complexExpectationPreservedType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
  (X X0 : Ω → S), @Measurable (NullMeasurableSpace Ω P) S _ _ X →
  Measurable X0 → X =ᵐ[P] X0 →
  ∀ f : S → ℂ, Measurable f → Integrable (fun ω => f (X0 ω)) P →
  (∫ ω : NullMeasurableSpace Ω P, f (X ω) ∂P.completion) = ∫ ω, f (X0 ω) ∂P

end Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions
