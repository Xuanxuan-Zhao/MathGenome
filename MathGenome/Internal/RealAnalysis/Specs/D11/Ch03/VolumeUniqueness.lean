import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures

/-! Independent statements of paper.tex:999–1020. The measurable space on
`Point d` is the Borel structure; it is not the completed Lebesgue structure.
The first assertion uses left-closed, right-open bounded coordinate boxes.
The second keeps finiteness on bounded Borel sets and invariance under images
of Borel sets as explicit hypotheses. The scalar is a strictly positive real. -/

open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch03.VolumeUniqueness

open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures

def box_uniqueness : Prop :=
  ∀ (d : ℕ) [NeZero d] (μ : Measure (Point d)),
    (∀ a b : Fin d → ℝ,
      μ (endpointBox a b (fun _ => true) (fun _ => false)) = boxContent a b) →
    μ = borelMeasure_value d

def translation_invariant_uniqueness : Prop :=
  ∀ (d : ℕ) [NeZero d] (μ : Measure (Point d)), μ ≠ 0 →
    (∀ (a : Point d) (E : Set (Point d)), MeasurableSet E →
      μ ((fun x => a + x) '' E) = μ E) →
    (∀ E : Set (Point d), MeasurableSet E → Bornology.IsBounded E → μ E < ∞) →
    ∃! c : ℝ, 0 < c ∧ μ = ENNReal.ofReal c • borelMeasure_value d

end Specs.D11.Ch03.VolumeUniqueness
