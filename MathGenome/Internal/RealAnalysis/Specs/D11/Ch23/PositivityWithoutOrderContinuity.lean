import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.ElementaryIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.Lattice

/-! Independent statements for paper.tex:6330–6339. `ℝ≥0` is the closed
half-line with its usual topology and order; `atTop` is infinity on it.
The space contains exactly the continuous functions with a finite real limit.
No order continuity or integral representation is built into these objects. -/

open Filter Topology MeasureTheory
open scoped NNReal

noncomputable section

namespace Specs.D11.Ch23.PositivityWithoutOrderContinuity

/-- All continuous functions on the half-line with a finite limit at infinity. -/
def limitSpace : Submodule ℝ (ℝ≥0 → ℝ) where
  carrier := {f | Continuous f ∧ ∃ l : ℝ, Tendsto f atTop (𝓝 l)}
  zero_mem' := ⟨continuous_const, ⟨0, tendsto_const_nhds⟩⟩
  add_mem' := by
    rintro f g ⟨hf, a, ha⟩ ⟨hg, b, hb⟩
    exact ⟨hf.add hg, a + b, ha.add hb⟩
  smul_mem' := by
    rintro c f ⟨hf, a, ha⟩
    exact ⟨continuous_const.mul hf, c * a, tendsto_const_nhds.mul ha⟩

/-- The finite limit, chosen from its existence assertion. -/
def limitValue (f : limitSpace) : ℝ := Classical.choose f.property.2

/-- The exact ramp sequence specified in the source. -/
def ramp (n : ℕ) (x : ℝ≥0) : ℝ := min (max ((x : ℝ) - n) 0) 1

def lattice_stone : Prop :=
  D11.Ch23.Specs.IsVectorLattice limitSpace ∧ D11.Ch23.Specs.IsStone limitSpace

def positive_linear : Prop :=
  ∃ L : limitSpace →ₗ[ℝ] ℝ,
    (∀ f, L f = limitValue f) ∧
    (∀ f : limitSpace, Tendsto (f : ℝ≥0 → ℝ) atTop (𝓝 (L f))) ∧
    (∀ f : limitSpace, (∀ x, 0 ≤ (f : ℝ≥0 → ℝ) x) → 0 ≤ L f)

def ramp_mem : Prop := ∀ n : ℕ, ramp n ∈ limitSpace

/-- The piecewise formulas include both endpoints, which agree. -/
def ramp_properties : Prop :=
  (∀ (n : ℕ) (x : ℝ≥0),
    ((x : ℝ) ≤ n → ramp n x = 0) ∧
    ((n : ℝ) ≤ x → (x : ℝ) ≤ n + 1 → ramp n x = (x : ℝ) - n) ∧
    ((n : ℝ) + 1 ≤ x → ramp n x = 1)) ∧
  (∀ x : ℝ≥0, Antitone (fun n => ramp n x)) ∧
  (∀ x : ℝ≥0, Tendsto (fun n => ramp n x) atTop (𝓝 0)) ∧
  (∀ n : ℕ, Tendsto (ramp n) atTop (𝓝 1))

/-- The explicit decreasing null sequence keeps functional value one. -/
def failure_of_order_continuity : Prop :=
  ∀ L : limitSpace →ₗ[ℝ] ℝ, (∀ f, L f = limitValue f) →
    (∃ f : ℕ → limitSpace,
      (∀ n, (f n : ℝ≥0 → ℝ) = ramp n) ∧
      (∀ x, Antitone (fun n => (f n : ℝ≥0 → ℝ) x)) ∧
      (∀ x, Tendsto (fun n => (f n : ℝ≥0 → ℝ) x) atTop (𝓝 0)) ∧
      (∀ n, L (f n) = 1) ∧
      ¬ Tendsto (fun n => L (f n)) atTop (𝓝 0)) ∧
    ¬ D11.Ch23.Specs.IsElementaryIntegral limitSpace L

/-- No measurable structure and positive measure can represent the limit
while making every member measurable and absolutely integrable. -/
def no_representation : Prop :=
  ∀ m : MeasurableSpace ℝ≥0,
    ¬ ∃ (μ : @Measure ℝ≥0 m)
      (hint : ∀ f : limitSpace,
        @_root_.Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value ℝ≥0 ℝ m _ _ _ μ (f : ℝ≥0 → ℝ)),
      ∀ f : limitSpace, limitValue f =
        @_root_.Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value ℝ≥0 ℝ m _ _ _ μ (f : ℝ≥0 → ℝ) (hint f)

end Specs.D11.Ch23.PositivityWithoutOrderContinuity
