import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.GradientIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The helical arc of paper.tex, d04:09:helix. Length and line integrals
use the shared polygonal-length and proper Riemann definitions. -/
noncomputable section
open Set
namespace Specs.D04.C09.Helix
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model
open Specs.SingleVariableAnalysis.Ch08.Integral
namespace Model

def helix (a b t : ℝ) : E 3 := WithLp.toLp 2 ![a * Real.cos t, a * Real.sin t, b * t]
def helixVelocity (a b t : ℝ) : E 3 :=
  WithLp.toLp 2 ![-a * Real.sin t, a * Real.cos t, b]
def height (x : E 3) : ℝ := x 2
end Model
open Model

abbrev helixType := ℝ → ℝ → ℝ → E 3
def helixValue : helixType := helix
def helixVelocityValue : helixType := helixVelocity
abbrev heightType := E 3 → ℝ
def heightValue : heightType := height

def helix_derivativeType : Prop := ∀ a b t : ℝ,
  HasDerivAt (helix a b) (helixVelocity a b t) t

def helix_speedType : Prop := ∀ a b t : ℝ,
  ‖deriv (helix a b) t‖ = Real.sqrt (a ^ 2 + b ^ 2)

def height_gradientType : Prop := ∀ x : E 3,
  scalarGradient height x = WithLp.toLp 2 ![0, 0, 1]

def helix_lengthType : Prop := ∀ a b T : ℝ, 0 < a → 0 ≤ T →
  length (helix a b) 0 T = ENNReal.ofReal (T * Real.sqrt (a ^ 2 + b ^ 2))

/-- Cumulative arc length, as the proper speed integral and as prefix length.
This includes t=0 and never asserts an inverse on a degenerate interval. -/
def helix_arclengthType : Prop := ∀ a b T : ℝ, 0 < a → 0 ≤ T →
  ∀ t ∈ Icc 0 T,
    ∃ h : realIntegrableValue (fun u => ‖deriv (helix a b) u‖) 0 t,
      realIntegralValue (fun u => ‖deriv (helix a b) u‖) h =
        t * Real.sqrt (a ^ 2 + b ^ 2) ∧
      length (helix a b) 0 t = ENNReal.ofReal (t * Real.sqrt (a ^ 2 + b ^ 2))

/-- Supplies the continuous path, its C¹ data, and existence and values of
both integrals. The data use the actual derivative, including endpoints. -/
def helix_integralsType : Prop := ∀ a b T : ℝ, 0 < a → 0 ≤ T →
  ∃ γ : IntervalPath 3 0 T, (∀ t, γ t = helix a b t) ∧
    ∃ d : PiecewiseC1Data γ, (∀ i t, d.velocity i t = helixVelocity a b t) ∧
      ∃ hw : WorkIntegrable d (scalarGradient height),
        ∃ hs : ScalarIntegrable d height,
          workLineIntegral d (scalarGradient height) hw = b * T ∧
          scalarLineIntegral d height hs = b * T ^ 2 * Real.sqrt (a ^ 2 + b ^ 2) / 2

/-- Explicit zero-duration specialization. -/
def helix_zeroType : Prop := ∀ a b : ℝ, 0 < a →
  length (helix a b) 0 0 = 0 ∧
  ∃ γ : IntervalPath 3 0 0, (∀ t, γ t = helix a b t) ∧
    ∃ d : PiecewiseC1Data γ,
      ∃ hw : WorkIntegrable d (scalarGradient height),
        ∃ hs : ScalarIntegrable d height,
          workLineIntegral d (scalarGradient height) hw = 0 ∧
          scalarLineIntegral d height hs = 0
end Specs.D04.C09.Helix
