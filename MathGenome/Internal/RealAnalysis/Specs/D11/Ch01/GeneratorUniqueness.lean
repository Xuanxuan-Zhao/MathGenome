import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.PiLambda

/-!
Independent statements of paper.tex:402–421, uniqueness on generators.

The measures and generated sigma-algebra are the shared canonical objects.
The upstream source/native correspondence identifies equality of native measures
with equality on the original measurable domain. No topology, nonempty-space
assumption, or positivity of total mass is required.

As in the upstream pi–lambda interface, the pi-system hypothesis explicitly
requires closure under binary intersections, including empty intersections.
It does not require that the family contain the whole space. The first statement
therefore retains the separate equality-of-total-mass hypothesis.
-/

open Set MeasureTheory MeasurableSpace
open scoped ENNReal

universe u

namespace Specs.D11.Ch01.GeneratorUniqueness

/-- The finite-measure case, including equality on the whole space. -/
def finite_generator_uniqueness : Prop :=
  ∀ {α : Type u} [m : MeasurableSpace α] (μ ν : Measure α)
    (P : Set (Set α)),
    m = generateFrom P →
    (∀ s ∈ P, ∀ t ∈ P, s ∩ t ∈ P) →
    μ univ < ∞ → ν univ < ∞ →
    (∀ s ∈ P, μ s = ν s) → μ univ = ν univ → μ = ν

/-- The common increasing finite-mass exhaustion by generators case. -/
def exhaustion_generator_uniqueness : Prop :=
  ∀ {α : Type u} [m : MeasurableSpace α] (μ ν : Measure α)
    (P : Set (Set α)),
    m = generateFrom P →
    (∀ s ∈ P, ∀ t ∈ P, s ∩ t ∈ P) →
    (∀ s ∈ P, μ s = ν s) →
    ∀ E : ℕ → Set α,
      (∀ n, E n ∈ P) → Monotone E → (⋃ n, E n) = univ →
      (∀ n, μ (E n) < ∞ ∧ ν (E n) < ∞) → μ = ν

end Specs.D11.Ch01.GeneratorUniqueness
