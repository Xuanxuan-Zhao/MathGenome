import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.PolynomialMomentHilbertSpace
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SymmetryAndDeficiencies
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-! Independent statements for the strictly positive part of
`fa2:p3:jacobi-moment`, paper.tex:15621–15657. The null-polynomial branch
is separately allocated to `ops_moment_finite_null`. -/
noncomputable section
open Polynomial Complex
namespace ExpandedFA.Moments

/-- Strict positivity for every nonzero complex polynomial, with no normalization of m₀. -/
def HankelPositive (m : ℕ → ℝ) : Prop :=
  ∀ p : ℂ[X], p ≠ 0 → 0 < (momentForm m p p).re

namespace JacobiRecurrenceSpec

def complexify (p : ℝ[X]) : ℂ[X] := p.map (algebraMap ℝ ℂ)

/-- Real orthonormal polynomials with the source's positive-leading-coefficient
normalization and three-term recurrence. The last term at n=0 is zero. -/
structure PolynomialJacobiSystem (m : ℕ → ℝ) where
  p : ℕ → ℝ[X]
  a : ℕ → ℝ
  b : ℕ → ℝ
  degree : ∀ n, (p n).natDegree = n
  leading_positive : ∀ n, 0 < (p n).leadingCoeff
  orthonormal : ∀ j k, momentForm m (complexify (p j)) (complexify (p k)) =
    if j = k then 1 else 0
  a_zero : a 0 = 0
  a_positive : ∀ n, 0 < a (n + 1)
  recurrence : ∀ n, (X : ℝ[X]) * p n =
    a (n + 1) • p (n + 1) + b n • p n +
      if n = 0 then 0 else a n • p (n - 1)

abbrev SequenceHilbertSpace := lp (fun _ : ℕ => ℂ) 2

/-- The unitary identification includes the exact finite-support domain, the
basis vectors, and every matrix coordinate of the operator action. -/
def IsJacobiRealization (m : ℕ → ℝ) (h : HankelNonnegative m)
    (d : PolynomialJacobiSystem m)
    (U : MomentHilbertSpace m h ≃ₗᵢ[ℂ] SequenceHilbertSpace) : Prop :=
  (∀ n, U (polynomialClass m h (ofPolynomial (complexify (d.p n)))) =
    lp.single 2 n 1) ∧
  (∀ y : SequenceHilbertSpace,
    U.symm y ∈ (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h).domain ↔
      (Function.support (fun n => y n)).Finite) ∧
  (∀ (x : (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h).domain) (n : ℕ),
    U (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h x) n =
      (d.a (n + 1) : ℂ) * U (x : MomentHilbertSpace m h) (n + 1) +
      (d.b n : ℂ) * U (x : MomentHilbertSpace m h) n +
      if n = 0 then 0 else (d.a n : ℂ) * U (x : MomentHilbertSpace m h) (n - 1))

def OrthonormalPolynomialsExpected : Prop := ∀ (m : ℕ → ℝ),
  HankelPositive m → Nonempty (PolynomialJacobiSystem m)

def JacobiRealizationExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m),
  HankelPositive m → ∃ (d : PolynomialJacobiSystem m)
    (U : MomentHilbertSpace m h ≃ₗᵢ[ℂ] SequenceHilbertSpace), IsJacobiRealization m h d U

/-- The additional construction identity used to assemble the unitary model.
This is an obligation to prove, not an assumed property of arbitrary systems. -/
def IsAlignedWithGramSchmidt (m : ℕ → ℝ) (h : HankelNonnegative m)
    (d : PolynomialJacobiSystem m) : Prop := ∀ n,
  polynomialClass m h (ofPolynomial (complexify (d.p n))) =
    InnerProductSpace.gramSchmidtNormed ℂ
      (fun k : ℕ => polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ k))) n

/-- Remaining polynomial construction, including the bridge to the unitary used
by the analytic part of the proof. -/
def AlignedPolynomialConstructionExpected : Prop :=
  ∀ (m : ℕ → ℝ) (h : HankelNonnegative m), HankelPositive m →
    ∃ d : PolynomialJacobiSystem m, IsAlignedWithGramSchmidt m h d

/-- A conditional assembly lemma, separate from the construction obligation. -/
def RealizationAssemblyExpected : Prop :=
  ∀ (m : ℕ → ℝ) (h : HankelNonnegative m), HankelPositive m →
    ∀ d : PolynomialJacobiSystem m, IsAlignedWithGramSchmidt m h d →
      ∃ U : MomentHilbertSpace m h ≃ₗᵢ[ℂ] SequenceHilbertSpace,
        IsJacobiRealization m h d U

/-- The indices retain the canonical Hilbert cardinal definition. Density is
quantified as a certificate; it is already guaranteed by the moment construction. -/
def DeficiencyAlternativesExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hd : Dense ((PolynomialMomentHilbertSpaceSpec.multiplicationValue m h).domain :
      Set (MomentHilbertSpace m h))),
  HankelPositive m →
  let S := PolynomialMomentHilbertSpaceSpec.multiplicationValue m h
  (Unbounded.SymmetryAndDeficienciesSpec.deficiencyIndexValue S hd I = 0 ∧
    Unbounded.SymmetryAndDeficienciesSpec.deficiencyIndexValue S hd (-I) = 0) ∨
  (Unbounded.SymmetryAndDeficienciesSpec.deficiencyIndexValue S hd I = 1 ∧
    Unbounded.SymmetryAndDeficienciesSpec.deficiencyIndexValue S hd (-I) = 1)

/-- A useful stronger bound, also valid for degenerate nonnegative moment forms. -/
def DeficiencyBoundExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hd : Dense ((PolynomialMomentHilbertSpaceSpec.multiplicationValue m h).domain :
      Set (MomentHilbertSpace m h))) (z : ℂ),
  Unbounded.SymmetryAndDeficienciesSpec.deficiencyIndexValue
    (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h) hd z ≤ 1

end JacobiRecurrenceSpec
end ExpandedFA.Moments
