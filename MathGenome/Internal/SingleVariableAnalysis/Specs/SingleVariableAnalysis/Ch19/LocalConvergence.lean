import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Convolution
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.RiemannLebesgueImproper

/-! Dini's local condition, paper.tex:4796–4829. Values assigned at x are
unrestricted. Integrals are the Chapter 10 independent endpoint limits of
proper Darboux integrals. The real case uses the canonical embedding into ℂ.
The piecewise C¹ corollary is allocated to PiecewiseC1Convergence. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.LocalConvergence
open Ch08.Integral Ch10.SeveralEndpoints Ch10.Absolute PeriodicSetup
open Filter Set
open scoped Topology

/-- Symmetric error, retaining the order of the two one-sided limits. -/
def symmetricError (f : ℝ → ℂ) (x : ℝ) (Lminus Lplus : ℂ) (t : ℝ) : ℂ :=
  f (x+t) + f (x-t) - Lplus - Lminus

/-- Only positive arguments enter the improper integral. -/
def diniDensity (f : ℝ → ℂ) (x : ℝ) (Lminus Lplus : ℂ) (t : ℝ) : ℝ :=
  ‖symmetricError f x Lminus Lplus t‖ / t

/-- Its total value at zero is immaterial to every regular truncation. -/
def sineQuotient (f : ℝ → ℂ) (x : ℝ) (Lminus Lplus : ℂ) (t : ℝ) : ℂ :=
  symmetricError f x Lminus Lplus t / (Real.sin (t/2) : ℂ)

/-- The original local hypothesis implies local proper integrability and
absolute improper integrability of the sine-denominator quotient on (0,π). -/
def quotientIntegrability : Prop := ∀ (f : ℝ → ℂ), periodicComplexValue f →
  ∀ (x : ℝ) (Lminus Lplus : ℂ) (δ : ℝ), 0 < δ → δ < Real.pi →
  Tendsto f (𝓝[<] x) (𝓝 Lminus) → Tendsto f (𝓝[>] x) (𝓝 Lplus) →
  convergesValue .real (diniDensity f x Lminus Lplus) (0 : WithBot ℝ) (δ : WithTop ℝ) →
  locallyIntegrableValue .complex (sineQuotient f x Lminus Lplus)
    (0 : WithBot ℝ) (Real.pi : WithTop ℝ) ∧
  absoluteValue .complex (sineQuotient f x Lminus Lplus)
    (0 : WithBot ℝ) (Real.pi : WithTop ℝ)

/-- Pointwise convergence to the midpoint of the finite one-sided limits. -/
def complexLocalConvergence : Prop := ∀ (f : ℝ → ℂ), periodicComplexValue f →
  ∀ (h : ∀ n : ℤ, complexIntegrableValue (fun y => f y * modeValue (-n) y)
    (-Real.pi) Real.pi) (x : ℝ) (Lminus Lplus : ℂ) (δ : ℝ),
  0 < δ → δ < Real.pi →
  Tendsto f (𝓝[<] x) (𝓝 Lminus) → Tendsto f (𝓝[>] x) (𝓝 Lplus) →
  convergesValue .real (diniDensity f x Lminus Lplus) (0 : WithBot ℝ) (δ : WithTop ℝ) →
  Tendsto (fun N : ℕ => partialSumValue f h N x) atTop (𝓝 ((Lminus + Lplus)/2))

/-- Real scalar specialization, with a real midpoint embedded into ℂ. -/
def realLocalConvergence : Prop := ∀ (f : ℝ → ℝ), periodicRealValue f →
  ∀ (h : ∀ n : ℤ, complexIntegrableValue (fun y => (f y : ℂ) * modeValue (-n) y)
    (-Real.pi) Real.pi) (x Lminus Lplus δ : ℝ),
  0 < δ → δ < Real.pi →
  Tendsto f (𝓝[<] x) (𝓝 Lminus) → Tendsto f (𝓝[>] x) (𝓝 Lplus) →
  convergesValue .real (fun t => |f (x+t) + f (x-t) - Lplus - Lminus| / t)
    (0 : WithBot ℝ) (δ : WithTop ℝ) →
  Tendsto (fun N : ℕ => partialSumValue (fun y => (f y : ℂ)) h N x)
    atTop (𝓝 (((Lminus + Lplus)/2 : ℝ) : ℂ))

end Specs.SingleVariableAnalysis.Ch19.LocalConvergence
