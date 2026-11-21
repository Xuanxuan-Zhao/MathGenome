import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Independent statements for elementary measure bounds and continuity

These are the conclusions of paper.tex:225–256. The canonical `Measure` is
the positive measure of the upstream interface; its correspondence with the
source's function on measurable sets is established by that prerequisite.
Every set evaluated here is assumed measurable or is a countable union,
intersection, or difference of such sets. No completeness, nonemptiness,
finiteness of the space, or sigma-finiteness is assumed.

The arrows in the source include monotonicity and convergence. We record
these together with the corresponding supremum/infimum identity. The
decreasing case allows initial infinite values and asks for just one finite
term, at an arbitrary index.
-/

open Set MeasureTheory Filter
open scoped ENNReal Topology

universe u

namespace Specs.D11.Ch01.MeasureBoundsContinuity

def monotonicity : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (A B : Set α),
    MeasurableSet A → MeasurableSet B → A ⊆ B → μ A ≤ μ B

def difference : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (A B : Set α),
    MeasurableSet A → MeasurableSet B → A ⊆ B → μ A < ∞ →
      μ (B \ A) = μ B - μ A

def countable_subadditivity : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : ℕ → Set α),
    (∀ n, MeasurableSet (E n)) → μ (⋃ n, E n) ≤ ∑' n, μ (E n)

def continuity_from_below : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : ℕ → Set α) (s : Set α),
    (∀ n, MeasurableSet (E n)) → Monotone E → (⋃ n, E n) = s →
      Monotone (fun n => μ (E n)) ∧
      (⨆ n, μ (E n)) = μ s ∧
      Tendsto (fun n => μ (E n)) atTop (𝓝 (μ s))

def continuity_from_above : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : ℕ → Set α) (s : Set α),
    (∀ n, MeasurableSet (E n)) → Antitone E → (⋂ n, E n) = s →
    (∃ N, μ (E N) < ∞) →
      Antitone (fun n => μ (E n)) ∧
      (⨅ n, μ (E n)) = μ s ∧
      Tendsto (fun n => μ (E n)) atTop (𝓝 (μ s))

end Specs.D11.Ch01.MeasureBoundsContinuity
