import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.RCLike.Lemmas

/-! Independent specification of paper.tex:15898–15923.
The Hilbert space uses Lebesgue measure restricted to the open interval, exactly
as in the source. Orthogonality and the norm formula are stated on the closed
interval. All scalar Hilbert-space assertions cover both ℝ and ℂ via `RCLike`.
Completeness is explicitly closure of the linear span equal to the whole space.
-/
noncomputable section
open MeasureTheory Polynomial
open scoped ENNReal Topology

namespace ExpandedFA.Models.LegendreBasisSpec

/-- The Rodrigues polynomial, formed using the algebraic polynomial derivative. -/
def legendre (n : ℕ) : Polynomial ℝ :=
  Polynomial.C ((2 ^ n * (n.factorial : ℝ))⁻¹) *
    Polynomial.derivative^[n] ((Polynomial.X ^ 2 - 1) ^ n)

/-- Lebesgue measure on the open interval in the source. -/
abbrev intervalMeasure : Measure ℝ := volume.restrict (Set.Ioo (-1 : ℝ) 1)

abbrev intervalL2 (𝕜 : Type*) [RCLike 𝕜] := Lp 𝕜 2 intervalMeasure

/-- A polynomial is square integrable on this finite interval. This only uses
compactness and continuity, and assumes none of the Legendre conclusions. -/
theorem polynomial_memLp (𝕜 : Type*) [RCLike 𝕜] (p : Polynomial 𝕜) :
    MemLp (fun x : ℝ => p.eval (x : 𝕜)) 2 intervalMeasure := by
  have hc : Continuous (fun x : ℝ => p.eval (x : 𝕜)) :=
    p.continuous.comp RCLike.continuous_ofReal
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn (s := Set.Icc (-1 : ℝ) 1))
  apply MemLp.of_bound hc.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hC x ⟨hx.1.le, hx.2.le⟩

/-- Canonical polynomial class in the a.e. L² quotient. -/
def polynomialL2 (𝕜 : Type*) [RCLike 𝕜] (p : Polynomial 𝕜) : intervalL2 𝕜 :=
  (polynomial_memLp 𝕜 p).toLp (fun x : ℝ => p.eval (x : 𝕜))

/-- The exact normalized real Rodrigues polynomial, also in the complex space. -/
def normalizedL2 (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) : intervalL2 𝕜 :=
  (Real.sqrt (((2 * n + 1 : ℕ) : ℝ) / 2) : 𝕜) •
    polynomialL2 𝕜 ((legendre n).map (algebraMap ℝ 𝕜))

/-- The polynomial definition agrees with the analytic Rodrigues formula. -/
def RodriguesFormula : Prop := ∀ n x,
  (legendre n).eval x = (2 ^ n * (n.factorial : ℝ))⁻¹ *
    iteratedDeriv n (fun x : ℝ => (x ^ 2 - 1) ^ n) x

def Orthogonality : Prop := ∀ (m n : ℕ), m ≠ n →
  (∫ x in (-1 : ℝ)..1, (legendre m).eval x * (legendre n).eval x) = 0

def SquaredNorm : Prop := ∀ n : ℕ,
  (∫ x in (-1 : ℝ)..1, ((legendre n).eval x) ^ 2) = 2 / (2 * (n : ℝ) + 1)

/-- The same exact value for the norm of the open-interval a.e. class. -/
def SquaredL2Norm : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (n : ℕ),
  ‖polynomialL2 𝕜 ((legendre n).map (algebraMap ℝ 𝕜))‖^2 =
    2 / (2*(n : ℝ)+1)

def NormalizedOrthonormal : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  Orthonormal 𝕜 (normalizedL2 𝕜)

/-- This is the full Hilbert basis completeness requirement, in addition to
orthonormality. A merely orthonormal sequence does not satisfy this statement. -/
def CompleteSpan : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  (Submodule.span 𝕜 (Set.range (normalizedL2 𝕜))).topologicalClosure = ⊤

/-- An actual Hilbert basis with precisely the prescribed vectors. -/
def HilbertBasisExistence : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  ∃ b : HilbertBasis ℕ 𝕜 (intervalL2 𝕜), ∀ n, b n = normalizedL2 𝕜 n

end ExpandedFA.Models.LegendreBasisSpec
