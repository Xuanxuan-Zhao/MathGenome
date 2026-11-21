import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.WindingIndex
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathsChains

/-!
Implementation of the integral index (D12.04.03). The canonical definitions
live in the independent Spec for reuse by later Specs. Integrality, support,
and homotopy properties are separate obligations, not definition fields.
-/

noncomputable section

namespace D12Complex.WindingIndex

abbrev chainIndex : Specs.D12Complex.Ch04.WindingIndex.chainIndex_type :=
  _root_.D12Complex.IntegralChain.index

abbrev cycleIndex : Specs.D12Complex.Ch04.WindingIndex.cycleIndex_type :=
  _root_.D12Complex.IntegralCycle.index

end D12Complex.WindingIndex

namespace D12Complex

namespace IntegralChain

/-- The source formula is asserted only away from the active trace. -/
theorem index_eq_integral (Γ : IntegralChain) (a : ℂ) (ha : a ∉ Γ.trace) :
    Γ.index a =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Γ.integral (fun z => 1 / (z - a)) := by
  simp only [index, ite_eq_right ha]

@[simp] theorem zero_index (a : ℂ) : (0 : IntegralChain).index a = 0 := by
  simp [index]

/-- Off-trace reciprocal kernels meet the original contour-integral hypothesis. -/
theorem reciprocal_continuousOn_trace (Γ : IntegralChain) (a : ℂ)
    (ha : a ∉ Γ.trace) : ContinuousOn (fun z : ℂ => 1 / (z - a)) Γ.trace := by
  apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
  intro z hz
  change z - a ≠ 0
  exact sub_ne_zero.mpr (fun h : z = a => ha (h ▸ hz))

end IntegralChain

namespace IntegralCycle

theorem index_eq_integral (Γ : IntegralCycle) (a : ℂ) (ha : a ∉ Γ.trace) :
    Γ.index a =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Γ.integral (fun z => 1 / (z - a)) :=
  Γ.chain.index_eq_integral a ha

@[simp] theorem zero_index (a : ℂ) : (0 : IntegralCycle).index a = 0 := by
  exact IntegralChain.zero_index a

end IntegralCycle

namespace WindingIndex

/-- The empty trace of the zero chain is the Ch03 active-trace convention. -/
theorem chain_zero_trace : (0 : IntegralChain).trace = ∅ := IntegralChain.zero_trace

theorem cycle_zero_trace : (0 : IntegralCycle).trace = ∅ := IntegralCycle.zero_trace

end WindingIndex
end D12Complex
