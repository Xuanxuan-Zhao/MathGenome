import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
The integral-based index of paper.tex:935–941 (D12.04.03).

The canonical chains, active traces, cycles, and contour integrals are exactly
those of Ch03. The chain version allows the same formula for any finite chain;
the cycle version restricts it to integer combinations of closed piecewise C1
paths. Both values are complex numbers. No integer-valuedness is assumed.

The source defines the index only off the active trace. We extend it by zero
on that trace to obtain a total function of the point; this auxiliary value has
no mathematical meaning as an index. All integral comparison statements below
retain the off-trace hypothesis. In particular, an inactive path contributes
neither to the trace nor to the integral.
-/

noncomputable section
open Classical

namespace D12Complex

namespace IntegralChain

/-- Normalized contour integral off the active trace; extended by zero on it. -/
def index (Γ : IntegralChain) (a : ℂ) : ℂ :=
  if a ∈ Γ.trace then 0 else
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Γ.integral (fun z => 1 / (z - a))

end IntegralChain

namespace IntegralCycle

/-- The index of a finite cycle, using its underlying Ch03 chain. -/
def index (Γ : IntegralCycle) (a : ℂ) : ℂ := Γ.chain.index a

end IntegralCycle
end D12Complex

namespace Specs.D12Complex.Ch04.WindingIndex
open _root_.D12Complex

def chainIndex_type := IntegralChain → ℂ → ℂ

def chainIndex_value : chainIndex_type := fun Γ a =>
  if a ∈ Γ.trace then 0 else
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Γ.integral (fun z => 1 / (z - a))

def cycleIndex_type := IntegralCycle → ℂ → ℂ

def cycleIndex_value : cycleIndex_type := fun Γ a => Γ.chain.index a

def chain_index_eq_integral_type : Prop :=
  ∀ (Γ : IntegralChain) (a : ℂ), a ∉ Γ.trace →
    Γ.index a =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Γ.integral (fun z => 1 / (z - a))

def cycle_index_eq_integral_type : Prop :=
  ∀ (Γ : IntegralCycle) (a : ℂ), a ∉ Γ.trace →
    Γ.index a =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Γ.integral (fun z => 1 / (z - a))

def chain_zero_trace_type : Prop := (0 : IntegralChain).trace = ∅

def cycle_zero_trace_type : Prop := (0 : IntegralCycle).trace = ∅

def chain_zero_index_type : Prop := ∀ a : ℂ, (0 : IntegralChain).index a = 0

def cycle_zero_index_type : Prop := ∀ a : ℂ, (0 : IntegralCycle).index a = 0

/-- The contour's continuity hypothesis holds at every allowed point. -/
def reciprocal_continuousOn_trace_type : Prop :=
  ∀ (Γ : IntegralChain) (a : ℂ), a ∉ Γ.trace →
    ContinuousOn (fun z : ℂ => 1 / (z - a)) Γ.trace

end Specs.D12Complex.Ch04.WindingIndex
