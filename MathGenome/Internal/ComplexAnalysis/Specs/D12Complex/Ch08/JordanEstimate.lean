import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PiecewiseC1Length
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! The oriented upper semicircle runs from r to -r with angle 0 ≤ t ≤ π.
The integral and trace supremum are the canonical Chapter 3 objects. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.JordanEstimate

/-- The upper semicircle, retaining its actual angular parametrization. -/
def upperSemicircle (r : ℝ) : PiecewiseC1Path :=
  ⟨⟨0, Real.pi, Real.pi_pos.le, circleMap 0 r,
    (continuous_circleMap 0 r).continuousOn⟩,
    ⟨C1Partition.single _ (contDiff_circleMap 0 r).contDiffOn⟩⟩

end D12Complex.JordanEstimate

namespace Specs.D12Complex.Ch08.JordanEstimate
open _root_.D12Complex _root_.D12Complex.JordanEstimate

def upperSemicircle_type := ℝ → PiecewiseC1Path
def upperSemicircle_value : upperSemicircle_type := upperSemicircle

/-- paper.tex:2074–2094. No holomorphy or off-trace continuity is assumed. -/
def jordan_estimate_type : Prop :=
  ∀ (r c : ℝ), 0 < r → 0 < c → ∀ (q : ℂ → ℂ),
    ContinuousOn q (upperSemicircle r).trace →
    ‖(upperSemicircle r).integral (fun z => Complex.exp (Complex.I * (c : ℂ) * z) * q z)‖ ≤
      (Real.pi / c) * (upperSemicircle r).traceSupNorm q

/-- The radius-dependent family can have arbitrary dependence on r; only
continuity on each positive-radius trace and decay of those suprema are used. -/
def jordan_integral_tendsto_zero_type : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (q : ℝ → ℂ → ℂ),
    (∀ r : ℝ, 0 < r → ContinuousOn (q r) (upperSemicircle r).trace) →
    Tendsto (fun r => (upperSemicircle r).traceSupNorm (q r)) atTop (𝓝 0) →
    Tendsto (fun r => (upperSemicircle r).integral
      (fun z => Complex.exp (Complex.I * (c : ℂ) * z) * q r z)) atTop (𝓝 0)

end Specs.D12Complex.Ch08.JordanEstimate
