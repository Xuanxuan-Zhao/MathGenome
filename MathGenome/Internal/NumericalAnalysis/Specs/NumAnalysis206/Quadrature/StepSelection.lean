import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IsLUB
import Mathlib.Order.Filter.Extr

open Set Filter Topology
noncomputable section

namespace NumAnalysis206.Quadrature

/-- Fixed derivative and uniform sample budgets; arithmetic in the stencil is exact.
The budgets do not vary with the step. To apply these bounds to a stencil, the
same budgets must hold over the entire allowed neighborhood. -/
def centralBound (M η h : ℝ) : ℝ := M * h ^ 2 / 6 + η / h

def forwardBound (M η h : ℝ) : ℝ := M * h / 2 + 2 * η / h

namespace StepSelectionSpec

def centralMin : Prop := ∀ (H M η : ℝ), 0 < H → 0 < M → 0 < η →
  let q := min H ((3 * η / M) ^ (1 / 3 : ℝ))
  q ∈ Ioc 0 H ∧ IsMinOn (centralBound M η) (Ioc 0 H) q

def forwardMin : Prop := ∀ (H M η : ℝ), 0 < H → 0 < M → 0 < η →
  let q := min H ((4 * η / M) ^ (1 / 2 : ℝ))
  q ∈ Ioc 0 H ∧ IsMinOn (forwardBound M η) (Ioc 0 H) q

def centralNoise : Prop := ∀ (H η : ℝ), 0 < H → 0 < η →
  StrictAntiOn (centralBound 0 η) (Ioc 0 H) ∧
  IsMinOn (centralBound 0 η) (Ioc 0 H) H

def forwardNoise : Prop := ∀ (H η : ℝ), 0 < H → 0 < η →
  StrictAntiOn (forwardBound 0 η) (Ioc 0 H) ∧
  IsMinOn (forwardBound 0 η) (Ioc 0 H) H

def centralExact : Prop := ∀ (H M : ℝ), 0 < H → 0 < M →
  Tendsto (centralBound M 0) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
  IsGLB (centralBound M 0 '' Ioc 0 H) 0 ∧
  ∀ h ∈ Ioc 0 H, ¬ IsMinOn (centralBound M 0) (Ioc 0 H) h

def forwardExact : Prop := ∀ (H M : ℝ), 0 < H → 0 < M →
  Tendsto (forwardBound M 0) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
  IsGLB (forwardBound M 0 '' Ioc 0 H) 0 ∧
  ∀ h ∈ Ioc 0 H, ¬ IsMinOn (forwardBound M 0) (Ioc 0 H) h

def zeroBudgets : Prop := ∀ h : ℝ,
  centralBound 0 0 h = 0 ∧ forwardBound 0 0 h = 0

end StepSelectionSpec
end NumAnalysis206.Quadrature
