import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.LocalConvergence
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! The local piecewise C¹ corollary in paper.tex:4807–4828.
A finite piecewise C¹ neighborhood can be shortened until its only possible
break is x. We express C¹ on its two open sides by differentiability and
continuity of the real-variable derivative, and retain explicit finite bounds.
There is no condition on f x, and x ranges over all ℝ, including period seams.
The derivative bounds are hypotheses; the one-sided Lipschitz estimates and
Dini integrability are conclusions to be proved.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Convergence
open Set Filter
open scoped Topology
open Ch08.Integral Ch10.SeveralEndpoints PeriodicSetup LocalConvergence

/-- C¹ on an open cell with a finite derivative bound. -/
def sideC1Bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b M : ℝ) : Prop :=
  (∀ y ∈ Ioo a b, DifferentiableAt ℝ f y) ∧
  ContinuousOn (deriv f) (Ioo a b) ∧
  ∀ y ∈ Ioo a b, ‖deriv f y‖ ≤ M

/-- The local two-cell form of piecewise C¹ regularity with bounded derivatives.
The bounds may differ on the two sides. All assigned values are ordinary finite
scalars, with no matching to either limiting value required. -/
def localPiecewiseC1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (x : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ Mminus Mplus : ℝ, 0 ≤ Mminus ∧ 0 ≤ Mplus ∧
    sideC1Bound f (x-r) x Mminus ∧ sideC1Bound f x (x+r) Mplus

def complexDiniCondition : Prop := ∀ (f : ℝ → ℂ) (x : ℝ) (Lm Lp : ℂ),
  localPiecewiseC1 f x →
  Tendsto f (𝓝[<] x) (𝓝 Lm) → Tendsto f (𝓝[>] x) (𝓝 Lp) →
  ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi ∧
    convergesValue .real (diniDensity f x Lm Lp) (0 : WithBot ℝ) (δ : WithTop ℝ)

def realDiniCondition : Prop := ∀ (f : ℝ → ℝ) (x Lm Lp : ℝ),
  localPiecewiseC1 f x →
  Tendsto f (𝓝[<] x) (𝓝 Lm) → Tendsto f (𝓝[>] x) (𝓝 Lp) →
  ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi ∧
    convergesValue .real (fun t => |f (x+t)+f (x-t)-Lp-Lm| / t)
      (0 : WithBot ℝ) (δ : WithTop ℝ)

def complexConvergence : Prop := ∀ (f : ℝ → ℂ), periodicComplexValue f →
  ∀ (h : ∀ n : ℤ, complexIntegrableValue (fun y => f y * modeValue (-n) y)
    (-Real.pi) Real.pi) (x : ℝ) (Lm Lp : ℂ),
  localPiecewiseC1 f x →
  Tendsto f (𝓝[<] x) (𝓝 Lm) → Tendsto f (𝓝[>] x) (𝓝 Lp) →
  Tendsto (fun N : ℕ => partialSumValue f h N x) atTop (𝓝 ((Lm+Lp)/2))

def realConvergence : Prop := ∀ (f : ℝ → ℝ), periodicRealValue f →
  ∀ (h : ∀ n : ℤ, complexIntegrableValue (fun y => (f y : ℂ) * modeValue (-n) y)
    (-Real.pi) Real.pi) (x Lm Lp : ℝ),
  localPiecewiseC1 f x →
  Tendsto f (𝓝[<] x) (𝓝 Lm) → Tendsto f (𝓝[>] x) (𝓝 Lp) →
  Tendsto (fun N : ℕ => partialSumValue (fun y => (f y : ℂ)) h N x)
    atTop (𝓝 (((Lm+Lp)/2 : ℝ) : ℂ))

end Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Convergence
