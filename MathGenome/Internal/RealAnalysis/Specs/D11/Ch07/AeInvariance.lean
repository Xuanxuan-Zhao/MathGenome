import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! Independent specification of paper.tex:2467–2488.
The raw modes admit the stronger normed-group congruences below. The Lp
statements explicitly assume measurability of all four representatives on
the original sigma algebra. No completeness or mass assumption is imposed.
The counterexample uses completed restricted Lebesgue measure on [0,1]. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u v
noncomputable section
namespace Specs.D11.Ch07.AeInvariance
open Specs.D11.Ch04.AeCommonException
open Specs.D11.Ch07.ConvergenceDefinitions

def ae_convergence_congr : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f g : ℕ → X → E) (F G : X → E),
    (∀ n, aeEq_value μ (f n) (g n)) → aeEq_value μ F G →
    (aeConverges_value μ f F ↔ aeConverges_value μ g G)

def in_measure_congr : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f g : ℕ → X → E) (F G : X → E),
    (∀ n, aeEq_value μ (f n) (g n)) → aeEq_value μ F G →
    (inMeasureConverges_value μ f F ↔ inMeasureConverges_value μ g G)

def locally_in_measure_congr : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f g : ℕ → X → E) (F G : X → E),
    (∀ n, aeEq_value μ (f n) (g n)) → aeEq_value μ F G →
    (locallyInMeasureConverges_value μ f F ↔ locallyInMeasureConverges_value μ g G)

def almost_uniform_congr : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f g : ℕ → X → E) (F G : X → E),
    (∀ n, aeEq_value μ (f n) (g n)) → aeEq_value μ F G →
    (almostUniformConverges_value μ f F ↔ almostUniformConverges_value μ g G)

def lp_convergence_congr : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [MeasurableSpace E] (μ : Measure X) (p : ℝ) (f g : ℕ → X → E) (F G : X → E),
    (∀ n, Measurable (f n)) → (∀ n, Measurable (g n)) →
    Measurable F → Measurable G →
    (∀ n, aeEq_value μ (f n) (g n)) → aeEq_value μ F G →
    (lpConverges_value μ p f F ↔ lpConverges_value μ p g G)

def linfty_convergence_congr : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [MeasurableSpace E] (μ : Measure X) (f g : ℕ → X → E) (F G : X → E),
    (∀ n, Measurable (f n)) → (∀ n, Measurable (g n)) →
    Measurable F → Measurable G →
    (∀ n, aeEq_value μ (f n) (g n)) → aeEq_value μ F G →
    (linftyConverges_value μ f F ↔ linftyConverges_value μ g G)

/-- Completion of the ordinary subtype restriction of real volume. -/
abbrev Interval := NullMeasurableSpace unitInterval (volume : Measure unitInterval)

def spike_type := ℕ → Interval → ℝ

def spike_value : spike_type := by
  classical
  exact fun n x => if x = (0 : unitInterval) then (n : ℝ) else 0

/-- Each representative is measurable and zero a.e., but its value at zero
escapes to +infinity; its attained supremum error over the whole interval is n.
The zero sequence converges both pointwise and uniformly; the spike sequence
has no finite pointwise limit at zero and cannot converge uniformly to zero. -/
def singleton_counterexample : Prop :=
  let μ := (volume : Measure unitInterval).completion
  (∀ n, Measurable (spike_value n)) ∧
  Measurable (fun _ : Interval => (0 : ℝ)) ∧
  (∀ n, aeEq_value μ (spike_value n) (fun _ => 0)) ∧
  Tendsto (fun n => spike_value n (0 : unitInterval)) atTop atTop ∧
  (∀ a : ℝ, ¬ Tendsto (fun n => spike_value n (0 : unitInterval)) atTop (𝓝 a)) ∧
  (∀ n, (∀ x, ‖spike_value n x - 0‖ ≤ (n : ℝ)) ∧
    ‖spike_value n (0 : unitInterval) - 0‖ = (n : ℝ)) ∧
  pointwiseConverges_value (fun (_ : ℕ) (_ : Interval) => (0 : ℝ)) (fun _ => 0) ∧
  uniformConverges_value (fun (_ : ℕ) (_ : Interval) => (0 : ℝ)) (fun _ => 0) ∧
  ¬ pointwiseConverges_value spike_value (fun _ => 0) ∧
  ¬ uniformConverges_value spike_value (fun _ => 0)

end Specs.D11.Ch07.AeInvariance
