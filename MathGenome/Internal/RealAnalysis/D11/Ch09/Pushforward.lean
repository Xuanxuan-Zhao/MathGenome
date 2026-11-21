import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.D11.Ch04.MeasurableMapTests
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.Pushforward

/-!
Pushforward of a positive measure (paper.tex:2987–2997).

Measurability is an explicit argument of the construction, as in the source.
The result is a native positive measure on the specified target space, using
the Chapter 1 correspondence. Its measurable-set values are the prescribed
inverse-image values. No assertion is made that other sets are measurable.
-/

open Set MeasureTheory
open scoped ENNReal

universe u v

namespace D11.Ch09.Pushforward

/-- Push a positive measure forward along a measurable map. -/
noncomputable def pushforward {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (_hu : Measurable u) (μ : Measure X) : Measure Y :=
  Measure.map u μ

theorem pushforward_apply {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (B : Set Y)
    (hB : MeasurableSet B) : pushforward u hu μ B = μ (u ⁻¹' B) :=
  Measure.map_apply hu hB

theorem pushforward_empty {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) :
    pushforward u hu μ ∅ = 0 :=
  measure_empty

theorem pushforward_countable_additivity {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (B : ℕ → Set Y)
    (hB : ∀ n, MeasurableSet (B n))
    (hd : Pairwise fun i j => Disjoint (B i) (B j)) :
    pushforward u hu μ (⋃ n, B n) = ∑' n, pushforward u hu μ (B n) :=
  measure_iUnion hd hB

/-- Total mass is preserved, including when it is infinite. -/
theorem pushforward_univ {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) :
    pushforward u hu μ univ = μ univ := by
  rw [pushforward_apply u hu μ univ MeasurableSet.univ, preimage_univ]

end D11.Ch09.Pushforward
