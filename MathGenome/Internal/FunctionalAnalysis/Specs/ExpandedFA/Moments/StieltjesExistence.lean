import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.PolynomialMomentHilbertSpace
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.FriedrichsExtension
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Stieltjes existence, paper.tex, fa2:p3:stieltjes-moment and the existence
part of fa2:p3:stieltjes-determinacy. Measures on ℝ concentrated on [0,∞)
are used as the equivalent extension-by-zero representation. No support bound,
strict positivity, positive total mass, or density of polynomials in L² of a
representing measure is assumed. Uniqueness is a separate obligation. -/
noncomputable section
open MeasureTheory Polynomial
open scoped InnerProductSpace
namespace ExpandedFA.Moments.StieltjesExistence
open Unbounded PolynomialMomentHilbertSpaceSpec

/-- The shifted Hankel sequence. -/
def shiftedMoments (m : ℕ → ℝ) (n : ℕ) : ℝ := m (n + 1)

/-- A positive Borel measure with finite mass, nonnegative support, and every
absolute moment finite. `Integrable` includes absolute integrability. -/
def Represents (μ : Measure ℝ) (m : ℕ → ℝ) : Prop :=
  IsFiniteMeasure μ ∧ μ (Set.Iio 0) = 0 ∧
    ∀ n : ℕ, Integrable (fun t : ℝ => t ^ n) μ ∧ (∫ t : ℝ, t ^ n ∂μ) = m n

/-- A nonnegative self-adjoint extension in the original polynomial Hilbert
space; the equality of partial operators includes their domains. -/
def NonnegativeExtension (m : ℕ → ℝ) (h : HankelNonnegative m)
    (A : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h)) : Prop :=
  multiplicationValue m h ≤ A ∧ Dense (A.domain : Set (MomentHilbertSpace m h)) ∧
    A.IsClosed ∧ A = HilbertAdjointSpec.adjointValue A ∧
    ∀ x : A.domain, 0 ≤ (inner ℂ (x : MomentHilbertSpace m h) (A x)).re

/-- The power domain and its exact action on every polynomial vector. -/
def PolynomialPowers (m : ℕ → ℝ) (h : HankelNonnegative m)
    (A : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h)) : Prop :=
  ∀ (n : ℕ) (p : MomentPolynomials m h),
    ∃ hp : polynomialClass m h p ∈ (OperatorDomainsSpec.powerValue A n).domain,
      OperatorDomainsSpec.powerValue A n ⟨polynomialClass m h p, hp⟩ =
        polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n * rawPolynomial p))

namespace Spec

def ShiftedForm : Prop := ∀ (m : ℕ → ℝ) (p q : ℂ[X]),
  momentForm (shiftedMoments m) p q = momentForm m p (X * q)

def ExtensionExists : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m),
  HankelNonnegative (shiftedMoments m) →
    ∃ A : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h),
      NonnegativeExtension m h A ∧ PolynomialPowers m h A

def Necessity : Prop := ∀ (m : ℕ → ℝ) (μ : Measure ℝ), Represents μ m →
  HankelNonnegative m ∧ HankelNonnegative (shiftedMoments m)

def Sufficiency : Prop := ∀ (m : ℕ → ℝ), HankelNonnegative m →
  HankelNonnegative (shiftedMoments m) → ∃ μ : Measure ℝ, Represents μ m

def Existence : Prop := ∀ m : ℕ → ℝ,
  (∃ μ : Measure ℝ, Represents μ m) ↔
    HankelNonnegative m ∧ HankelNonnegative (shiftedMoments m)

def FiniteExistence : Prop := ∀ m : ℕ → ℝ,
  (∃ μ : Measure ℝ, Represents μ m) ↔
    FiniteHankelNonnegative m ∧ FiniteHankelNonnegative (shiftedMoments m)

def ZeroMass : Prop := ∀ (m : ℕ → ℝ), HankelNonnegative m → m 0 = 0 →
  Represents 0 m ∧ ∀ μ : Measure ℝ, Represents μ m → μ = 0

end Spec
end ExpandedFA.Moments.StieltjesExistence
