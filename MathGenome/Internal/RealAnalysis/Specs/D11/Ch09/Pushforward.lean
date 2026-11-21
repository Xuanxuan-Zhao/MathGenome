import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import Mathlib.MeasureTheory.Measure.Map

/-!
Independent interface for paper.tex:2987–2997, `D11.09.pushforward`.

The spaces carry their specified sigma-algebras. The upstream correspondence
identifies native `Measure` with the source's positive measure on measurable
sets. Evaluation below is asserted only for measurable target sets; no
completion or extra measurability is inferred from native outer values.
There are no nonemptiness, finiteness, or sigma-finiteness hypotheses.
-/

open Set MeasureTheory
open scoped ENNReal

universe u v

namespace Specs.D11.Ch09.Pushforward

def pushforward_type :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y), Measurable u → Measure X → Measure Y

noncomputable def pushforward_value : pushforward_type.{u,v} :=
  fun u _hu μ => Measure.map u μ

/-- The defining formula, on exactly the original target sigma-algebra. -/
def pushforward_apply : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (B : Set Y),
    MeasurableSet B → pushforward_value u hu μ B = μ (u ⁻¹' B)

def pushforward_empty : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (hu : Measurable u) (μ : Measure X),
    pushforward_value u hu μ ∅ = 0

def pushforward_countable_additivity : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (B : ℕ → Set Y),
    (∀ n, MeasurableSet (B n)) →
    Pairwise (fun i j => Disjoint (B i) (B j)) →
    pushforward_value u hu μ (⋃ n, B n) = ∑' n, pushforward_value u hu μ (B n)

def pushforward_univ : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (hu : Measurable u) (μ : Measure X),
    pushforward_value u hu μ univ = μ univ

end Specs.D11.Ch09.Pushforward
