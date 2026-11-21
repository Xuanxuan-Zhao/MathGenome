import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Singularities
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Asymptotics
open scoped Topology

/-! Growth and limit classification, paper.tex:1678–1722. All limits are
punctured; no condition is imposed on the representative's value at `a`.
The norm of the complex inverse power is exactly `‖z-a‖⁻ᵐ`. -/
namespace Specs.D12Complex.Ch07.SingularityGrowth
open _root_.D12Complex

def bigO_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), IsolatedSingularityAt f a → ∀ m : ℕ,
    (f =O[𝓝[≠] a] (fun z => ((z-a)^m)⁻¹) ↔
      RemovableSingularityAt f a ∨ ∃ k : ℕ, k ≤ m ∧ PoleOfOrderAt f a k)

def littleO_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), IsolatedSingularityAt f a → ∀ m : ℕ, 1 ≤ m →
    (f =o[𝓝[≠] a] (fun z => ((z-a)^m)⁻¹) ↔
      RemovableSingularityAt f a ∨ ∃ k : ℕ, k ≤ m-1 ∧ PoleOfOrderAt f a k)

def finiteLimit_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), IsolatedSingularityAt f a →
    ((∃ L : ℂ, Tendsto f (𝓝[≠] a) (𝓝 L)) ↔ RemovableSingularityAt f a)

/-- Every extension takes the unique punctured limit as its center value. -/
def extension_value_type : Prop :=
  ∀ (f g : ℂ → ℂ) (a L : ℂ) (r : ℝ), 0 < r →
    HolomorphicOn (Metric.ball a r) g →
    (∀ z ∈ puncturedDisk a r, f z = g z) →
    Tendsto f (𝓝[≠] a) (𝓝 L) → g a = L

def pole_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), IsolatedSingularityAt f a →
    (Tendsto (fun z => ‖f z‖) (𝓝[≠] a) atTop ↔ PoleAt f a)

def bounded_removable_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), IsolatedSingularityAt f a →
    (∃ C : ℝ, ∀ᶠ z in 𝓝[≠] a, ‖f z‖ ≤ C) → RemovableSingularityAt f a

def mul_tendsto_zero_removable_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), IsolatedSingularityAt f a →
    Tendsto (fun z => (z-a)*f z) (𝓝[≠] a) (𝓝 0) → RemovableSingularityAt f a

end Specs.D12Complex.Ch07.SingularityGrowth
