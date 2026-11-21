import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.GeneratorUniqueness
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Uniqueness on generators

Both conclusions of paper.tex:402–421 use the canonical measure interface,
whose correspondence with functions on measurable sets is proved upstream.

For finite measures, the equality class is a Dynkin system: equal finite total
masses give complement closure, and countable additivity gives disjoint-union
closure. Mathlib's `ext_of_generate_finite` implements this pi–lambda argument.

For the exhaustion case, `Measure.ext_of_generateFrom_of_iUnion` localizes to
the finite restrictions on the generators in the cover and then assembles their
equalities. It even allows a cover without monotonicity. Here we retain the
source's increasing exhaustion and finiteness assumptions for both measures.
-/

open Set MeasureTheory MeasurableSpace
open scoped ENNReal

universe u

namespace D11.Ch01.GeneratorUniqueness

theorem finite_generator_uniqueness {α : Type u} [m : MeasurableSpace α]
    (μ ν : Measure α) (P : Set (Set α)) (hgen : m = generateFrom P)
    (hP : ∀ s ∈ P, ∀ t ∈ P, s ∩ t ∈ P)
    (hμ : μ univ < ∞) (_hν : ν univ < ∞)
    (heq : ∀ s ∈ P, μ s = ν s) (hmass : μ univ = ν univ) : μ = ν := by
  let : IsFiniteMeasure μ := ⟨hμ⟩
  have hpi : IsPiSystem P := fun s hs t ht _ => hP s hs t ht
  exact ext_of_generate_finite P hgen hpi heq hmass

theorem exhaustion_generator_uniqueness {α : Type u} [m : MeasurableSpace α]
    (μ ν : Measure α) (P : Set (Set α)) (hgen : m = generateFrom P)
    (hP : ∀ s ∈ P, ∀ t ∈ P, s ∩ t ∈ P)
    (heq : ∀ s ∈ P, μ s = ν s) (E : ℕ → Set α)
    (hE : ∀ n, E n ∈ P) (_hmono : Monotone E) (hcover : (⋃ n, E n) = univ)
    (hfinite : ∀ n, μ (E n) < ∞ ∧ ν (E n) < ∞) : μ = ν := by
  have hpi : IsPiSystem P := fun s hs t ht _ => hP s hs t ht
  exact Measure.ext_of_generateFrom_of_iUnion P E hgen hpi hcover hE
    (fun n => (hfinite n).1.ne) heq

end D11.Ch01.GeneratorUniqueness
