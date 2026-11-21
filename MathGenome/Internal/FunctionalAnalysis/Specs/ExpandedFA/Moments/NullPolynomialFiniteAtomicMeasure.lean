import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.HamburgerDeterminacy
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Independent statements for the null-polynomial case of
`fa2:p3:jacobi-moment` (current paper.tex:15753–15778).
The polynomial form, quotient, completion, and representing-measure predicate
are the shared moment-problem objects. -/

noncomputable section
open MeasureTheory Polynomial
namespace ExpandedFA.Moments.NullPolynomialFiniteAtomicMeasureSpec

/-- Both the separated polynomial quotient and its Hilbert completion are finite
 dimensional. A nonzero constant null polynomial is permitted. -/
def FiniteDimension : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p : ℂ[X]), p ≠ 0 → momentForm m p p = 0 →
  FiniteDimensional ℂ (PolynomialQuotient m h) ∧
  FiniteDimensional ℂ (MomentHilbertSpace m h)

/-- Uniqueness is among all representing positive Borel measures. The finite
set has distinct real nodes, strictly positive finite masses and no zero weights;
it may be empty, so the zero measure is included. Each node is a root of the
original null polynomial, irrespective of its repeated or nonreal roots. -/
def UniqueAtomicMeasure : Prop := ∀ (m : ℕ → ℝ) (_h : HankelNonnegative m)
    (p : ℂ[X]), p ≠ 0 → momentForm m p p = 0 →
  ∃ μ : Measure ℝ, RepresentsHamburgerMoments m μ ∧
    (∀ ν : Measure ℝ, RepresentsHamburgerMoments m ν → ν = μ) ∧
    ∃ s : Finset ℝ,
      (∀ t ∈ s, 0 < μ {t} ∧ μ {t} < ⊤ ∧ p.eval (t : ℂ) = 0) ∧
      μ = ∑ t ∈ s, μ {t} • Measure.dirac t

end ExpandedFA.Moments.NullPolynomialFiniteAtomicMeasureSpec
