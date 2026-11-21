import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.WindingIndex
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! The full conclusions of D12.04.03, for the canonical integral cycles.
An unbounded complementary component is represented by `connectedComponentIn`;
no simplicity or separation property of the trace is assumed. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch04.IndexProperties
open _root_.D12Complex

def cycle_index_integer_type : Prop :=
  ∀ (Γ : IntegralCycle) (a : ℂ), a ∉ Γ.trace → ∃ n : ℤ, Γ.index a = (n : ℂ)

def cycle_index_continuousOn_type : Prop :=
  ∀ Γ : IntegralCycle, ContinuousOn Γ.index Γ.traceᶜ

def cycle_index_locally_constant_type : Prop :=
  ∀ (Γ : IntegralCycle) (a : ℂ), a ∉ Γ.trace →
    ∀ᶠ b in 𝓝 a, b ∉ Γ.trace ∧ Γ.index b = Γ.index a

def cycle_index_zero_on_unbounded_component_type : Prop :=
  ∀ (Γ : IntegralCycle) (a : ℂ), a ∉ Γ.trace →
    ¬ Bornology.IsBounded (connectedComponentIn Γ.traceᶜ a) → Γ.index a = 0

def cycle_index_bounded_support_type : Prop :=
  ∀ Γ : IntegralCycle, Bornology.IsBounded (Function.support Γ.index)

end Specs.D12Complex.Ch04.IndexProperties
