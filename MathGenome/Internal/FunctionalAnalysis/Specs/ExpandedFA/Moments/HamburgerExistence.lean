import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.PolynomialMomentHilbertSpace
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SymmetryAndDeficiencies
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Hamburger existence, paper.tex:15440–15475, with the manuscript's conjugate-linear
first inner product and exact partial-operator power domains. No positive mass,
strict positivity, infinite dimension, or moment determinacy is assumed.
-/
noncomputable section
open MeasureTheory
namespace ExpandedFA.Moments
open Unbounded Unbounded.OperatorDomainsSpec Unbounded.SymmetryAndDeficienciesSpec

/-- A positive Borel measure on the real line with every absolute moment finite
and with the prescribed (unnormalized) real moments. Measures in Mathlib are
positive by definition; the measurable space here is the Borel space of ℝ. -/
def RepresentsHamburgerMoments (m : ℕ → ℝ) (μ : Measure ℝ) : Prop :=
  IsFiniteMeasure μ ∧
    (∀ n : ℕ, Integrable (fun t : ℝ => |t| ^ n) μ) ∧
    ∀ n : ℕ, (∫ t : ℝ, t ^ n ∂μ) = m n

/-- Existence of a finite positive representing measure, including the zero measure. -/
def HasHamburgerMeasure (m : ℕ → ℝ) : Prop :=
  ∃ μ : Measure ℝ, RepresentsHamburgerMoments m μ

/-- A self-adjoint operator and vector realize all moments, with genuine domain
membership for every power, including the zeroth power. -/
def RealizesHamburgerMoments {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (m : ℕ → ℝ) (A : Operator ℂ H H) (e : H) : Prop :=
  selfAdjointValue A ∧ ∀ n : ℕ,
    ∃ he : e ∈ (powerValue A n).domain,
      inner ℂ e (powerValue A n ⟨e, he⟩) = (m n : ℂ)

/-- The existential Hilbert space need not be nonzero; the polynomial completion
is a small Hilbert space and witnesses this formulation. -/
def HasHamburgerOperator (m : ℕ → ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (A : Operator ℂ H H) (e : H),
      RealizesHamburgerMoments m A e

namespace HamburgerExistenceSpec

def MeasureNecessity : Prop :=
  ∀ (m : ℕ → ℝ) (μ : Measure ℝ), RepresentsHamburgerMoments m μ →
    FiniteHankelNonnegative m

/-- The extension is on the polynomial Hilbert completion, not an assumed
certificate attached to a positive sequence. -/
def PolynomialExtension : Prop :=
  ∀ (m : ℕ → ℝ) (h : HankelNonnegative m),
    ∃ A : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h),
      PolynomialMomentHilbertSpaceSpec.multiplicationValue m h ≤ A ∧ selfAdjointValue A

def ExtensionRealizes : Prop :=
  ∀ (m : ℕ → ℝ) (h : HankelNonnegative m)
    (A : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h)),
    PolynomialMomentHilbertSpaceSpec.multiplicationValue m h ≤ A → selfAdjointValue A →
    RealizesHamburgerMoments m A (PolynomialMomentHilbertSpaceSpec.constantValue m h)

/-- The spectral-measure implication retains all absolute moments. -/
def OperatorSufficiency : Prop :=
  ∀ m : ℕ → ℝ, HasHamburgerOperator m → HasHamburgerMeasure m

/-- The full three-way equivalence from the source. -/
def HamburgerExistence : Prop :=
  ∀ m : ℕ → ℝ,
    (FiniteHankelNonnegative m ↔ HasHamburgerMeasure m) ∧
    (FiniteHankelNonnegative m ↔ HasHamburgerOperator m)

end HamburgerExistenceSpec
end ExpandedFA.Moments
