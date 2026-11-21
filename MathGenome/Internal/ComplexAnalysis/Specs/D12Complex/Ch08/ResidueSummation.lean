import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.Trigonometric
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Independent statements of paper.tex:2217–2254, `d12:08-07-summation`.
The index is all integers, and `HasSum` and `tsum` use the ordinary unordered
summation filter. The norm series states absolute convergence explicitly.
The real hyperbolic quotient is also identified with the shared complex `coth`.
-/

noncomputable section
namespace Specs.D12Complex.Ch08.ResidueSummation

/-- Absolute summability, rather than convergence of symmetric partial sums. -/
def absoluteSummability_type : Prop :=
  ∀ a : ℝ, 0 < a → Summable (fun n : ℤ => ‖(1 / ((n : ℝ)^2 + a^2) : ℝ)‖)

/-- The value of the unordered real sum. -/
def hasSum_type : Prop :=
  ∀ a : ℝ, 0 < a → HasSum (fun n : ℤ => (1 / ((n : ℝ)^2 + a^2) : ℝ))
    (Real.pi / a * (Real.cosh (Real.pi * a) / Real.sinh (Real.pi * a)))

def tsum_eq_type : Prop :=
  ∀ a : ℝ, 0 < a → (∑' n : ℤ, (1 / ((n : ℝ)^2 + a^2) : ℝ)) =
    Real.pi / a * (Real.cosh (Real.pi * a) / Real.sinh (Real.pi * a))

/-- The same formula using the project's canonical complex hyperbolic cotangent. -/
def tsum_eq_coth_type : Prop :=
  ∀ a : ℝ, 0 < a → (∑' n : ℤ, (1 / ((n : ℂ)^2 + (a : ℂ)^2) : ℂ)) =
    (Real.pi : ℂ) / a * _root_.D12Complex.coth ((Real.pi : ℂ) * a)

end Specs.D12Complex.Ch08.ResidueSummation
