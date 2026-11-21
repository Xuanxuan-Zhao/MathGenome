import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Filter.Pi

open Set Filter MeasureTheory
open scoped Topology

namespace D12Complex.FiniteDeletedLimits.Spec

/-- Finite localization with independent symmetric deletions, including an empty pole set. -/
def finite_deleted_limits : Prop :=
  ∀ (s : Finset ℝ) (l u : ℝ) (f : ℝ → ℂ),
    l < u →
    (∀ a ∈ s, l < a ∧ a < u) →
    ContinuousOn f (Icc l u \ (s : Set ℝ)) →
    (∀ a ∈ s, ∃ (δ : ℝ) (A : ℂ) (h : ℝ → ℂ),
      0 < δ ∧ ContinuousOn h (Icc (a - δ) (a + δ)) ∧
      ∀ x ∈ Icc (a - δ) (a + δ), x ≠ a →
        f x = A / ((x : ℂ) - (a : ℂ)) + h x) →
    (∀ ε : s → ℝ, (∀ a, 0 < ε a) →
      IntegrableOn f (Icc l u \ ⋃ a : s, Ioo (a.val - ε a) (a.val + ε a))) ∧
    ∃ L : ℂ, Tendsto
      (fun ε : s → ℝ => ∫ x in Icc l u \ ⋃ a : s,
        Ioo (a.val - ε a) (a.val + ε a), f x)
      (Filter.pi (fun _ : s => 𝓝[>] (0 : ℝ))) (𝓝 L)

end D12Complex.FiniteDeletedLimits.Spec
