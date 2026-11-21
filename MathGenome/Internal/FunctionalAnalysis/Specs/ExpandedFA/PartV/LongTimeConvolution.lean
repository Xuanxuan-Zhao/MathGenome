import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Independent statements for paper.tex, `fa2:p5:long-time-convolution`.
Functions are represented on ℝ with the restricted Lebesgue measure on (0,∞).
Their values outside this half-line play no role. The index n in `kernelPower`
stands for the positive convolution power n+1, so no delta distribution is used.
Both real and complex scalar fields, and the zero kernel, are included. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace ExpandedFA.PartV.LongTimeConvolution

abbrev halfLineMeasure : Measure ℝ := volume.restrict (Ioi 0)

/-- Forward convolution, extended by zero to nonpositive times. -/
def causalConv {𝕜 : Type} [RCLike 𝕜] (k f : ℝ → 𝕜) : ℝ → 𝕜 :=
  posConvolution k f (ContinuousLinearMap.mul ℝ 𝕜)

def kernelPower {𝕜 : Type} [RCLike 𝕜] (k : ℝ → 𝕜) : ℕ → ℝ → 𝕜
  | 0 => k
  | n+1 => causalConv k (kernelPower k n)

/-- Total definition; the series theorem proves that the nonintegrable branch
is never taken under its hypotheses. -/
def powerClass {𝕜 : Type} [RCLike 𝕜] (k : ℝ → 𝕜) (n : ℕ) :
    Lp 𝕜 1 halfLineMeasure := by
  classical
  exact if h : MemLp (kernelPower k n) 1 halfLineMeasure then h.toLp (kernelPower k n) else 0

def resolvent {𝕜 : Type} [RCLike 𝕜] (k : ℝ → 𝕜) : Lp 𝕜 1 halfLineMeasure :=
  ∑' n : ℕ, powerClass k n

def laplace (k : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t, Complex.exp (-z * (t : ℂ)) * k t ∂halfLineMeasure

namespace Spec

def Series : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (k : ℝ → 𝕜), Integrable k halfLineMeasure →
    (eLpNorm k 1 halfLineMeasure).toReal < 1 →
    (∀ n, MemLp (kernelPower k n) 1 halfLineMeasure) ∧
    HasSum (powerClass k) (resolvent k) ∧
    ‖resolvent k‖ ≤ (eLpNorm k 1 halfLineMeasure).toReal /
      (1 - (eLpNorm k 1 halfLineMeasure).toReal)

def LpSolution : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (k : ℝ → 𝕜), Integrable k halfLineMeasure →
    (eLpNorm k 1 halfLineMeasure).toReal < 1 →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp 𝕜 p halfLineMeasure),
    ∃ u : Lp 𝕜 p halfLineMeasure,
      (u : ℝ → 𝕜) =ᵐ[halfLineMeasure] (fun t => f t + causalConv k u t) ∧
      (u : ℝ → 𝕜) =ᵐ[halfLineMeasure]
        (fun t => f t + causalConv (resolvent k) f t) ∧
      ∀ v : Lp 𝕜 p halfLineMeasure,
        (v : ℝ → 𝕜) =ᵐ[halfLineMeasure] (fun t => f t + causalConv k v t) → v = u

def LaplaceIdentity : Prop :=
  ∀ (k : ℝ → ℂ), Integrable k halfLineMeasure →
    (eLpNorm k 1 halfLineMeasure).toReal < 1 →
    ∀ z : ℂ, 0 ≤ z.re →
      Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * k t) halfLineMeasure ∧
      Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * resolvent k t) halfLineMeasure ∧
      1 - laplace k z ≠ 0 ∧
      laplace (resolvent k) z = laplace k z / (1 - laplace k z)

/-- For real kernels the complex-valued Laplace transform embeds the real
resolvent, rather than silently replacing it with an unrelated complex object. -/
def RealLaplaceIdentity : Prop :=
  ∀ (k : ℝ → ℝ), Integrable k halfLineMeasure →
    (eLpNorm k 1 halfLineMeasure).toReal < 1 →
    ∀ z : ℂ, 0 ≤ z.re →
      1 - laplace (fun t => (k t : ℂ)) z ≠ 0 ∧
      laplace (fun t => (resolvent k t : ℂ)) z =
        laplace (fun t => (k t : ℂ)) z / (1 - laplace (fun t => (k t : ℂ)) z)

/-- Pointwise convergence concerns the displayed integral representative,
not the arbitrary representative chosen by the L∞ quotient. -/
def LongTimeLimit : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (k : ℝ → 𝕜), Integrable k halfLineMeasure →
    (eLpNorm k 1 halfLineMeasure).toReal < 1 →
    ∀ (f : ℝ → 𝕜) (ℓ : 𝕜), AEStronglyMeasurable f halfLineMeasure →
      (∃ M : ℝ, ∀ t, 0 < t → ‖f t‖ ≤ M) →
      Tendsto f atTop (𝓝 ℓ) →
      Tendsto (fun t => f t + causalConv (resolvent k) f t) atTop
        (𝓝 (ℓ / (1 - ∫ s, k s ∂halfLineMeasure)))

/-- The dominated-convergence assertion used to assemble the long-time limit. -/
def ConvolutionLimit : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (r f : ℝ → 𝕜) (ℓ : 𝕜),
    Integrable r halfLineMeasure → AEStronglyMeasurable f halfLineMeasure →
    (∃ M : ℝ, ∀ t, 0 < t → ‖f t‖ ≤ M) → Tendsto f atTop (𝓝 ℓ) →
    Tendsto (causalConv r f) atTop (𝓝 ((∫ s, r s ∂halfLineMeasure) * ℓ))

def UnstableExample : Prop :=
  let k : ℝ → ℝ := fun t => 2 * Real.exp (-t)
  let u : ℝ → ℝ := fun t => 2 * Real.exp t - 1
  Integrable k halfLineMeasure ∧ (∫ t, k t ∂halfLineMeasure) = 2 ∧
    (∀ t, 0 ≤ t → u t = 1 + causalConv k u t) ∧
    Tendsto u atTop atTop

end Spec
end ExpandedFA.PartV.LongTimeConvolution
