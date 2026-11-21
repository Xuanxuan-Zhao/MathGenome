import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.RCLike.Basic

/-! Independent statement of `fa2:p2:linfinity-weak-l1`, paper.tex:9819–9844.
Weak nullity tests every continuous scalar-linear functional on Banach L∞.
The measure is arbitrary; only the set of integration has finite measure.
`RCLike` includes both real and complex scalars, and the norm is absolute value. -/
namespace ExpandedFA.Compactness.WeakLinfinityFiniteL1.Spec

open MeasureTheory Filter
open scoped ENNReal Topology
universe u v

/-- Banach weak nullity implies local L¹ convergence of the absolute values.
No nonzero-measure, sigma-finiteness, or separability assumption is imposed. -/
def LocalL1Convergence : Prop :=
  ∀ (𝕜 : Type v) [RCLike 𝕜] (α : Type u) [MeasurableSpace α]
    (μ : Measure α) (g : ℕ → Lp 𝕜 ∞ μ),
    (∀ φ : Lp 𝕜 ∞ μ →L[𝕜] 𝕜, Tendsto (fun n => φ (g n)) atTop (𝓝 0)) →
    ∀ A : Set α, MeasurableSet A → μ A < ∞ →
      Tendsto (fun n => ∫ x in A, ‖g n x‖ ∂μ) atTop (𝓝 0)

/-- The explicit real-to-complex transport used in the source proof. -/
def RealToComplexWeakNull : Prop :=
  ∀ (α : Type u) [MeasurableSpace α] (μ : Measure α) (g : ℕ → Lp ℝ ∞ μ),
    (∀ φ : Lp ℝ ∞ μ →L[ℝ] ℝ, Tendsto (fun n => φ (g n)) atTop (𝓝 0)) →
    ∀ φ : Lp ℂ ∞ μ →L[ℂ] ℂ,
      Tendsto (fun n => φ (Complex.ofRealCLM.compLpL ∞ μ (g n))) atTop (𝓝 0)

end ExpandedFA.Compactness.WeakLinfinityFiniteL1.Spec
