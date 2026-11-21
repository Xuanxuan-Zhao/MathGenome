import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.TorusFourierBasis
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent statements for the finite-polynomial estimates in
`paper.tex`, fa2:p4:lacunary-subspace, lines 19744–19774.
The completion and unbounded-member assertions are allocated separately.
All integrals below use Haar probability measure on the angular circle. -/
noncomputable section
open MeasureTheory
open scoped Real ENNReal

namespace ExpandedFA.PartIV.LacunaryNormsSpec

abbrev Circle := AddCircle (2 * π)
abbrev μ : Measure Circle := AddCircle.haarAddCircle

/-- One fixed sequence, indexed from zero, for every exponent p. -/
def frequency (j : ℕ) : ℕ := 2 ^ (2 ^ j)

/-- The actual trigonometric polynomial, with arbitrary finite index set. -/
def polynomial (s : Finset ℕ) (a : ℕ → ℂ) : C(Circle, ℂ) :=
  ∑ j ∈ s, a j • fourier (frequency j : ℤ)

def coefficientSq (s : Finset ℕ) (a : ℕ → ℂ) : ℝ := ∑ j ∈ s, ‖a j‖ ^ 2

def coefficientNorm (s : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  Real.sqrt (coefficientSq s a)

/-- Real-valued Lp norm of the concrete continuous polynomial. -/
def polynomialNorm (p : ℝ≥0∞) (s : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  (eLpNorm (polynomial s a) p μ).toReal

def Increasing : Prop := StrictMono frequency

def TailDominance : Prop := ∀ m : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
  m * (∑ k ∈ Finset.range j, frequency k) < frequency j

/-- The tail has unique multiplicities for every fixed moment order. -/
def TailMultiplicity : Prop := ∀ m : ℕ, ∃ J : ℕ, ∀ (N : ℕ) (r q : ℕ → ℕ),
  (∀ j, j < J → r j = 0 ∧ q j = 0) →
  (∀ j, r j ≤ m ∧ q j ≤ m) →
  (∑ j ∈ Finset.range N, r j * frequency j) =
    (∑ j ∈ Finset.range N, q j * frequency j) →
  ∀ j, j < N → r j = q j

def TailEvenMoment : Prop := ∀ m : ℕ, 0 < m → ∃ J : ℕ,
  ∀ (s : Finset ℕ) (a : ℕ → ℂ), (∀ j ∈ s, J ≤ j) →
    (∫ t : Circle, ‖polynomial s a t‖ ^ (2 * m) ∂μ) ≤
      (m.factorial : ℝ) * (coefficientSq s a) ^ m

/-- The bound includes J=0 and zero coefficient families. -/
def HeadBound : Prop := ∀ (J : ℕ) (a : ℕ → ℂ) (t : Circle),
  ‖polynomial (Finset.range J) a t‖ ≤
    Real.sqrt (J : ℝ) * coefficientNorm (Finset.range J) a

def Parseval : Prop := ∀ (s : Finset ℕ) (a : ℕ → ℂ),
  (∫ t : Circle, ‖polynomial s a t‖ ^ 2 ∂μ) = coefficientSq s a

/-- An exponent-dependent constant for all finite polynomials at each even exponent.
This is obtained by adjoining the finite head to the moment-controlled tail. -/
def EvenNormUpper : Prop := ∀ m : ℕ, 0 < m → ∃ C : ℝ, 0 < C ∧
  ∀ (s : Finset ℕ) (a : ℕ → ℂ),
    polynomialNorm (2 * m : ℕ) s a ≤ C * coefficientNorm s a

/-- Full finite-family estimate, with constants independent of s and a.
The single frequency function above is used for every finite p≥1. -/
def NormEquivalence : Prop := ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (s : Finset ℕ) (a : ℕ → ℂ),
    c * coefficientNorm s a ≤ polynomialNorm p s a ∧
      polynomialNorm p s a ≤ C * coefficientNorm s a

-- Independent types of the reductions from the tail-moment estimate.
def EvenUpperOfTail : Prop := TailEvenMoment → EvenNormUpper
def NormEquivalenceOfTail : Prop := TailEvenMoment → NormEquivalence

end ExpandedFA.PartIV.LacunaryNormsSpec
