import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.ProperSpace

/-! Independent statements for paper.tex:1528–1559, D12.06.05.
The maximum is the supremum of the actual values on the circle; attainment
is asserted separately. Intermediate radii are positive. No boundary
extension on the original annulus is assumed. -/

open Set Metric

namespace D12Complex.ThreeCircles

noncomputable def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' sphere (0 : ℂ) r)

end D12Complex.ThreeCircles

namespace Specs.D12Complex.Ch06.ThreeCircles
open _root_.D12Complex _root_.D12Complex.ThreeCircles

def circleMaximum_type := (ℂ → ℂ) → ℝ → ℝ
noncomputable def circleMaximum_value : circleMaximum_type := maximumModulus

def maximum_attained_type : Prop :=
  ∀ (f : ℂ → ℂ) (r₀ r₃ t : ℝ),
    HolomorphicOn {z | r₀ < ‖z‖ ∧ ‖z‖ < r₃} f →
    0 < t → r₀ < t → t < r₃ →
    ∃ z : ℂ, ‖z‖ = t ∧ ‖f z‖ = maximumModulus f t ∧
      ∀ w : ℂ, ‖w‖ = t → ‖f w‖ ≤ ‖f z‖

/-- The zero case uses zero circle maxima, before any logarithm is taken. -/
def maximum_zero_type : Prop :=
  ∀ (f : ℂ → ℂ) (r₀ r₃ t : ℝ),
    HolomorphicOn {z | r₀ < ‖z‖ ∧ ‖z‖ < r₃} f →
    EqOn f (fun _ => 0) {z | r₀ < ‖z‖ ∧ ‖z‖ < r₃} →
    0 < t → r₀ < t → t < r₃ → maximumModulus f t = 0

def three_circles_multiplicative_type : Prop :=
  ∀ (f : ℂ → ℂ) (r₀ r₁ r r₂ r₃ : ℝ),
    HolomorphicOn {z | r₀ < ‖z‖ ∧ ‖z‖ < r₃} f →
    0 < r₁ → r₀ < r₁ → r₁ < r → r < r₂ → r₂ < r₃ →
    maximumModulus f r ≤
      (maximumModulus f r₁) ^ (Real.log (r₂ / r) / Real.log (r₂ / r₁)) *
      (maximumModulus f r₂) ^ (1 - Real.log (r₂ / r) / Real.log (r₂ / r₁))

def maximum_positive_type : Prop :=
  ∀ (f : ℂ → ℂ) (r₀ r₃ t : ℝ),
    HolomorphicOn {z | r₀ < ‖z‖ ∧ ‖z‖ < r₃} f →
    (∃ z : ℂ, (r₀ < ‖z‖ ∧ ‖z‖ < r₃) ∧ f z ≠ 0) →
    0 < t → r₀ < t → t < r₃ → 0 < maximumModulus f t

def three_circles_log_type : Prop :=
  ∀ (f : ℂ → ℂ) (r₀ r₁ r r₂ r₃ : ℝ),
    HolomorphicOn {z | r₀ < ‖z‖ ∧ ‖z‖ < r₃} f →
    (∃ z : ℂ, (r₀ < ‖z‖ ∧ ‖z‖ < r₃) ∧ f z ≠ 0) →
    0 < r₁ → r₀ < r₁ → r₁ < r → r < r₂ → r₂ < r₃ →
    Real.log (maximumModulus f r) ≤
      Real.log (r₂ / r) / Real.log (r₂ / r₁) * Real.log (maximumModulus f r₁) +
      Real.log (r / r₁) / Real.log (r₂ / r₁) * Real.log (maximumModulus f r₂)

def logMaximum_convex_type : Prop :=
  ∀ (f : ℂ → ℂ) (r₀ r₃ : ℝ),
    HolomorphicOn {z | r₀ < ‖z‖ ∧ ‖z‖ < r₃} f →
    (∃ z : ℂ, (r₀ < ‖z‖ ∧ ‖z‖ < r₃) ∧ f z ≠ 0) →
    ConvexOn ℝ {x : ℝ | r₀ < Real.exp x ∧ Real.exp x < r₃}
      (fun x => Real.log (maximumModulus f (Real.exp x)))

end Specs.D12Complex.Ch06.ThreeCircles
