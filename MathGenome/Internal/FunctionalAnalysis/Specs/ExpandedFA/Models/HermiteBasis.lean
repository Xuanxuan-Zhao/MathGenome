import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space

/-! Independent statements for the basis and differential-equation clauses of
paper.tex:16094--16112 (fa2:p3:hermite-oscillator). Operator-domain, resolvent,
essential self-adjointness, and ground-state clauses belong to ops_oscillator. -/

noncomputable section
open MeasureTheory Polynomial
open scoped ContDiff

namespace ExpandedFA.Models.HermiteBasis

/-- The physicists' Hermite polynomial, via its polynomial raising recursion.
The link to the manuscript's Rodrigues definition is a proof obligation. -/
def physicistsHermite : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => 2 * X * physicistsHermite n - derivative (physicistsHermite n)

/-- The manuscript's Rodrigues definition, without changing the Gaussian scale. -/
def H (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ)^n * Real.exp (x^2) * deriv^[n] (fun y : ℝ => Real.exp (-(y^2))) x

/-- Positive normalization denominator, exactly as in the manuscript. -/
def normalization (n : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ)^n * (n.factorial : ℝ) * Real.sqrt Real.pi)

/-- Real Hermite function. Scalar-valued versions use the canonical real inclusion. -/
def h (n : ℕ) (x : ℝ) : ℝ := Real.exp (-(x^2)/2) * H n x / normalization n

namespace Spec

def RodriguesIdentification : Prop := ∀ n x, H n x = (physicistsHermite n).eval x

def Smooth : Prop := ∀ n, ContDiff ℝ ∞ (h n)

def DifferentialEquation : Prop := ∀ n x,
  -deriv (deriv (h n)) x + x^2 * h n x = (2 * (n : ℝ) + 1) * h n x

def NormalizationPositive : Prop := ∀ n, 0 < normalization n

/-- Includes the exact unnormalized squared norm and all cross terms. -/
def GaussianOrthogonality : Prop := ∀ n m,
  (∫ x : ℝ, H n x * H m x * Real.exp (-(x^2))) =
    if n = m then (2 : ℝ)^n * (n.factorial : ℝ) * Real.sqrt Real.pi else 0

def SquareIntegrable : Prop := ∀ n, MemLp (h n) 2 volume

def NormalizedOrthogonality : Prop := ∀ n m,
  (∫ x : ℝ, h n x * h m x) = if n = m then 1 else 0

/-- A genuine complete orthonormal basis, over both real and complex scalars.
Equality in L² is stated as almost-everywhere equality of representatives. -/
def CompleteOrthonormalBasis : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  ∃ b : HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (volume : Measure ℝ)),
    ∀ n, (fun x => b n x) =ᵐ[volume] fun x => algebraMap ℝ 𝕜 (h n x)

end Spec
end ExpandedFA.Models.HermiteBasis
