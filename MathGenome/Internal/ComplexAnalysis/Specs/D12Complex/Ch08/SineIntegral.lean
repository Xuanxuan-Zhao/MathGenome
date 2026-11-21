import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.PrincipalValues
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! The explicit values and convergence distinctions in paper.tex:2140–2178.
The real integral is an ordinary limit of finite interval integrals. The
complex principal value uses the shared independent-deletion/ordinary-tail
definition, rather than a scalar integral over the pole. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace D12Complex.SineIntegral.Definitions

/-- The continuous extension of `sin (c*x) / x`, with value `c` at zero. -/
def sineKernel (c x : ℝ) : ℝ := c * Real.sinc (c * x)

end D12Complex.SineIntegral.Definitions

namespace Specs.D12Complex.Ch08.SineIntegral
open _root_.D12Complex.SineIntegral.Definitions
open _root_.D12Complex.PrincipalValues.Definitions

def sineKernel_type := ℝ → ℝ → ℝ
def sineKernel_value : sineKernel_type := fun c x => c * Real.sinc (c * x)

def principal_value_exp_div_type : Prop :=
  ∀ c : ℝ, 0 < c → HasPrincipalValue
    (fun x : ℝ => Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ))
    {0} (Real.pi * Complex.I)

def sineKernel_removable_type : Prop :=
  ∀ c : ℝ, Continuous (sineKernel c) ∧ sineKernel c 0 = c ∧
    (∀ x : ℝ, x ≠ 0 → sineKernel c x = Real.sin (c*x) / x) ∧
    Tendsto (fun x : ℝ => Real.sin (c*x) / x) (𝓝[≠] 0) (𝓝 c)

def sine_integral_type : Prop :=
  ∀ c : ℝ, 0 < c →
    (∀ b : ℝ, IntervalIntegrable (sineKernel c) volume 0 b) ∧
    Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, sineKernel c x) atTop (𝓝 (Real.pi / 2)) ∧
    Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, Real.sin (c*x) / x) atTop (𝓝 (Real.pi / 2))

def absolute_sine_integral_diverges_type : Prop :=
  ∀ c : ℝ, 0 < c →
    Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, |sineKernel c x|) atTop atTop ∧
    ¬ IntegrableOn (fun x : ℝ => |Real.sin (c*x)| / x) (Ioi (0 : ℝ))

def exp_div_not_integrable_near_zero_type : Prop :=
  ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ¬ IntegrableOn
      (fun x : ℝ => Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ))
      (Ioo (-ε) ε)

end Specs.D12Complex.Ch08.SineIntegral
