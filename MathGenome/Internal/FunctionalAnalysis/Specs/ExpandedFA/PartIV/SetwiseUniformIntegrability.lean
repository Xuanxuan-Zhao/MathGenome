import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Analysis.RCLike.Basic

/-!
Independent specification of the uniform-control portion of
`fa2:p4:hahn-vitali-saks`, paper.tex:19793–19848.
Functions represent their L¹ classes: integrability is assumed explicitly, and
all hypotheses and conclusions are invariant under almost-everywhere equality.
No finiteness, nonatomicity, nonemptiness, or completeness of the measure space
is imposed beyond the manuscript's σ-finiteness.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

universe u v

namespace ExpandedFA.PartIV.SetwiseUniformIntegrability.Spec

/-- Convergence to a finite scalar on every measurable set, including sets
of infinite underlying measure. -/
def SetwiseConvergent {α : Type u} {𝕜 : Type v} [RCLike 𝕜]
    [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → 𝕜) : Prop :=
  ∀ A : Set α, MeasurableSet A →
    ∃ z : 𝕜, Tendsto (fun n => ∫ x in A, f n x ∂μ) atTop (𝓝 z)

/-- The full three-part conclusion assigned to this goal. The finite-measure
set in the last clause is common to the entire sequence. -/
def UniformL1Control {α : Type u} {𝕜 : Type v} [RCLike 𝕜]
    [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → 𝕜) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ n, (∫ x, ‖f n x‖ ∂μ) ≤ C) ∧
  (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ A : Set α, MeasurableSet A → μ A < ENNReal.ofReal δ →
      ∀ n, (∫ x in A, ‖f n x‖ ∂μ) < ε) ∧
  (∀ ε : ℝ, 0 < ε → ∃ F : Set α, MeasurableSet F ∧ μ F < ⊤ ∧
    ∀ n, (∫ x in Fᶜ, ‖f n x‖ ∂μ) < ε)

/-- Setwise convergence implies uniform L¹ boundedness, uniformly absolutely
continuous norm integrals, and uniform finite-measure spatial tails. -/
def MainStatement : Prop :=
  ∀ (α : Type u) (𝕜 : Type v) [RCLike 𝕜] [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (f : ℕ → α → 𝕜),
    (∀ n, Integrable (f n) μ) → SetwiseConvergent μ f → UniformL1Control μ f

end ExpandedFA.PartIV.SetwiseUniformIntegrability.Spec
