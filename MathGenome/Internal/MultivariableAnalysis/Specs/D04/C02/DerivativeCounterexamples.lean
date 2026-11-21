import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Independent statements for the four examples at d04:02:counterexamples.
Real division is totalized in Lean; each rational expression below already
has value zero at the origin. The norm is the shared Euclidean norm. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C02.DerivativeCounterexamples
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
namespace Model

def point (x y : ℝ) : E 2 := WithLp.toLp 2 ![x, y]
def u (p : E 2) : ℝ := p 0 * p 1 / (p 0 ^ 2 + p 1 ^ 2)
def v (p : E 2) : ℝ := p 0 ^ 3 / (p 0 ^ 2 + p 1 ^ 2)
def w (p : E 2) : ℝ := p 0 ^ 3 * p 1 / (p 0 ^ 4 + p 1 ^ 2)
def z (x : ℝ) : ℝ := x ^ 2 * Real.sin x⁻¹
end Model
open Model
abbrev pointType := ℝ → ℝ → E 2
def pointValue : pointType := point
abbrev uType := E 2 → ℝ
def uValue : uType := u
abbrev vType := E 2 → ℝ
def vValue : vType := v
abbrev wType := E 2 → ℝ
def wValue : wType := w
abbrev zType := ℝ → ℝ
def zValue : zType := z

def origin_valuesType : Prop := u 0 = 0 ∧ v 0 = 0 ∧ w 0 = 0 ∧ z 0 = 0

def u_partialsType : Prop := ∀ j : Fin 2, HasDirectionalDerivative u 0 (standardBasis 2 j) 0
def u_diagonalType : Prop := ∀ x : ℝ, x ≠ 0 → u (point x x) = 1 / 2
def u_discontinuousType : Prop := ¬ ContinuousAt u 0

def v_boundType : Prop := ∀ p : E 2, |v p| ≤ ‖p‖
def v_continuousType : Prop := Continuous v
def v_directionsType : Prop := ∀ d : E 2, HasDirectionalDerivative v 0 d (v d)
def v_nonlinearType : Prop :=
  v (point 1 0) = 1 ∧ v (point 0 1) = 0 ∧ v (point 1 1) = 1 / 2 ∧
  v (point 1 1) ≠ v (point 1 0) + v (point 0 1)
def v_not_differentiableType : Prop := ¬ TotalDifferentiableAt univ v 0

def w_boundType : Prop := ∀ p : E 2, |w p| ≤ |p 0| / 2
def w_continuousType : Prop := Continuous w
def w_directionsType : Prop := ∀ d : E 2, HasDirectionalDerivative w 0 d 0
def w_parabolaType : Prop := ∀ x : ℝ, w (point x (x ^ 2)) = x / 2
def w_ratio_not_tendstoType : Prop :=
  ¬ Tendsto (fun x : ℝ => |w (point x (x ^ 2))| / ‖point x (x ^ 2)‖)
    (𝓝[≠] 0) (𝓝 0)
def w_signed_ratio_not_tendstoType : Prop :=
  ¬ Tendsto (fun x : ℝ => w (point x (x ^ 2)) / ‖point x (x ^ 2)‖)
    (𝓝[≠] 0) (𝓝 0)
def w_not_differentiableType : Prop := ¬ TotalDifferentiableAt univ w 0

def z_derivative_zeroType : Prop := HasDerivAt z 0 0
def z_derivative_off_zeroType : Prop := ∀ x : ℝ, x ≠ 0 →
  HasDerivAt z (2 * x * Real.sin x⁻¹ - Real.cos x⁻¹) x
def z_differentiableType : Prop := Differentiable ℝ z
def z_derivative_discontinuousType : Prop := ¬ ContinuousAt (deriv z) 0
end Specs.D04.C02.DerivativeCounterexamples
