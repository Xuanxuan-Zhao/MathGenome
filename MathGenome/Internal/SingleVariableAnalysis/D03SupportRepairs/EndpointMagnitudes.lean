import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
The magnitude quantities from paper.tex, section `inverse-endpoint-support`
(original lines 1739–1742). Later endpoint statements specialize `F` to
`Real.arcsin` or `Real.arccos` and approach either endpoint through `(-1, 1)`.
-/

namespace D03SupportRepairs

/-- Absolute value of the usual real derivative. -/
noncomputable def derivativeMagnitude (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  |deriv F x|

/-- Absolute value of the secant quotient based at the actual value `F a`. -/
noncomputable def secantMagnitude (F : ℝ → ℝ) (a x : ℝ) : ℝ :=
  |(F x - F a) / (x - a)|

end D03SupportRepairs
