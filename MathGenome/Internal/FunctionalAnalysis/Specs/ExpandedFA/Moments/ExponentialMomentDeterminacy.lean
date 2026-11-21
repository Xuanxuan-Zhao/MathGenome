import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.HamburgerExistence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! Sufficient conditions in paper.tex, `fa2:p3:moment-determinacy`.
The measures are the unnormalized finite positive Borel measures of the
Hamburger interface, including the zero measure. -/
noncomputable section
open MeasureTheory
namespace ExpandedFA.Moments.ExponentialMomentDeterminacySpec

/-- The positive even-moment series gives the same cosh integral for every
representing measure, and a positive absolute exponential moment. -/
def CommonExponentialMoment : Prop :=
  ∀ (m : ℕ → ℝ) (r : ℝ), 0 < r →
    Summable (fun n : ℕ => m (2 * n) * r ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) →
    ∀ μ : Measure ℝ, RepresentsHamburgerMoments m μ →
      Integrable (fun t : ℝ => Real.exp (r * |t|)) μ ∧
      (∫ t : ℝ, Real.cosh (r * t) ∂μ) =
        ∑' n : ℕ, m (2 * n) * r ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

/-- The common exponential moment implies equality, without a mass-one
normalization or a nonzero-mass assumption. -/
def ExponentialUniqueness : Prop :=
  ∀ (m : ℕ → ℝ) (μ ν : Measure ℝ),
    RepresentsHamburgerMoments m μ → RepresentsHamburgerMoments m ν →
    (∃ r : ℝ, 0 < r ∧ Integrable (fun t : ℝ => Real.exp (r * |t|)) μ ∧
      Integrable (fun t : ℝ => Real.exp (r * |t|)) ν) → μ = ν

def SeriesDeterminacy : Prop :=
  ∀ m : ℕ → ℝ, FiniteHankelNonnegative m →
    (∃ r : ℝ, 0 < r ∧
      Summable (fun n : ℕ => m (2 * n) * r ^ (2 * n) / (Nat.factorial (2 * n) : ℝ))) →
    ∃! μ : Measure ℝ, RepresentsHamburgerMoments m μ

def BoundedEvenDeterminacy : Prop :=
  ∀ m : ℕ → ℝ, FiniteHankelNonnegative m →
    (∃ C : ℝ, ∀ n : ℕ, m (2 * n) ≤ C) →
    ∃! μ : Measure ℝ, RepresentsHamburgerMoments m μ

end ExpandedFA.Moments.ExponentialMomentDeterminacySpec
