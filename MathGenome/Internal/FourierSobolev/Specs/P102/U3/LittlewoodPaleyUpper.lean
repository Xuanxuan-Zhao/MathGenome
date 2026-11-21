import MathGenome.Internal.FourierSobolev.Specs.P102.U3.Mihlin
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.RandomSignMoments
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Independent scope for the upper half of paper.tex:1248–1261.
The Fourier normalization, Euclidean volume, and all exponents are the shared
Mihlin interfaces. The definitions below make no multiplier-existence assumption.
`multiplier` is a total choice; the theorems must prove its actual Fourier action.
The infinite square function is ENNReal-valued, so a divergent sum stays infinite.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace P102.U3.LittlewoodPaley
open P102.Specs.U3 (Euclidean)
open P102.U3.Mihlin
open P102.U2.CZWeak (Operator)
open P102.U2.CZLpData (Exponent StrongOperator Agrees)

/-- A smooth real function supported in a fixed annulus. Both functions in the
source are in this class; the bounds do not require the partition identity. -/
def Annular {d : ℕ} (η : Euclidean d → ℝ) : Prop :=
  ContDiff ℝ ∞ η ∧
  (∀ ξ, ‖ξ‖ ≤ (1 / 4 : ℝ) → η ξ = 0) ∧
  (∀ ξ, (4 : ℝ) ≤ ‖ξ‖ → η ξ = 0)

def symbol {d : ℕ} (η : Euclidean d → ℝ) (j : ℤ) (ξ : Euclidean d) : ℂ :=
  (η (scale (-j) • ξ) : ℂ)

/-- Agreement with the L² multiplier on the entire L²/Lᵖ intersection. -/
def HasLpSymbol {d : ℕ} (p : Exponent) (m : Euclidean d → ℂ)
    (R : StrongOperator d p) : Prop :=
  ∃ T : Operator d, HasL2Symbol T m ∧ Agrees T p R

/-- Canonical choice of bounded multiplier, once existence and uniqueness have
been proved. The default branch has no mathematical force in any theorem. -/
def multiplier {d : ℕ} (p : Exponent) (m : Euclidean d → ℂ) : StrongOperator d p := by
  classical
  exact if h : ∃ R : StrongOperator d p, HasLpSymbol p m R then Classical.choose h else 0

def projection {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ) (j : ℤ) :
    StrongOperator d p := multiplier p (symbol η j)

def signedSymbol {d : ℕ} (η : Euclidean d → ℝ) (J : Finset ℤ)
    (ε : ℤ → Bool) (ξ : Euclidean d) : ℂ :=
  ∑ j ∈ J, (P102.U3.RandomSigns.sign (ε j) : ℂ) * symbol η j ξ

def signedOperator {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (J : Finset ℤ) (ε : ℤ → Bool) : StrongOperator d p :=
  ∑ j ∈ J, (P102.U3.RandomSigns.sign (ε j) : ℂ) • projection p η j

def finiteSquare {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ) (J : Finset ℤ)
    (f : Lp (α := Euclidean d) ℂ p.val volume) (x : Euclidean d) : ℝ :=
  Real.sqrt (∑ j ∈ J, ‖projection p η j f x‖ ^ 2)

def infiniteSquare {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (f : Lp (α := Euclidean d) ℂ p.val volume) (x : Euclidean d) : ℝ≥0∞ :=
  (∑' j : ℤ, ‖projection p η j f x‖ₑ ^ (2 : ℕ)) ^ (1 / 2 : ℝ)

/-- The same finite constant works for every finite set and the full square
function, and is chosen before the input f. `MemLp` includes measurability and
rules out an infinite norm. ENNReal has its usual extended norm. -/
def UpperBound {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ) (C : ℝ≥0) : Prop :=
  ∀ f : Lp (α := Euclidean d) ℂ p.val volume,
    (∀ J : Finset ℤ, MemLp (finiteSquare p η J f) p.val volume ∧
      eLpNorm (finiteSquare p η J f) p.val volume ≤ (C : ℝ≥0∞) * ‖f‖ₑ) ∧
    Measurable (infiniteSquare p η f) ∧
    (∀ᵐ x ∂volume, infiniteSquare p η f x < (∞ : ℝ≥0∞)) ∧
    MemLp (fun x => (infiniteSquare p η f x).toReal) p.val volume ∧
    eLpNorm (infiniteSquare p η f) p.val volume ≤ (C : ℝ≥0∞) * ‖f‖ₑ

/-- A common symbol derivative bound and an operator norm bound independent of
both finite scale set and signs. The latter is an assertion, not an assumption. -/
def SignedControl {d : ℕ} (η : Euclidean d → ℝ) : Prop :=
  (∃ A : ℝ, 0 ≤ A ∧ ∀ (J : Finset ℤ) (ε : ℤ → Bool),
    SymbolBound (signedSymbol η J ε) A) ∧
  ∀ p : Exponent, ∃ B : ℝ≥0, ∀ (J : Finset ℤ) (ε : ℤ → Bool),
    HasLpSymbol p (signedSymbol η J ε) (signedOperator p η J ε) ∧
    ‖signedOperator p η J ε‖ ≤ B

/-- A constructive enlarged cutoff. It is one on the closed annulus [1/2,2],
which contains the topological support of the partition block. -/
def enlargedCutoff {d : ℕ} (χ : Euclidean d → ℝ) (ξ : Euclidean d) : ℝ :=
  χ ((1 / 2 : ℝ) • ξ) * (1 - χ ((4 : ℝ) • ξ))

end P102.U3.LittlewoodPaley

namespace P102.Specs.U3.LittlewoodPaleyUpper
open P102.U3.Mihlin P102.U3.LittlewoodPaley
open P102.U2.CZLpData (Exponent)

def cutoffType : Prop :=
  ∀ (d : ℕ) (χ : Euclidean d → ℝ), IsCutoff χ →
    Annular (annulus χ) ∧ HasCompactSupport (annulus χ) ∧
    Annular (enlargedCutoff χ) ∧ HasCompactSupport (enlargedCutoff χ) ∧
    ∀ ξ ∈ tsupport (annulus χ), enlargedCutoff χ ξ = 1

def projectionsType : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ η : Euclidean d → ℝ, Annular η →
    ∀ (p : Exponent) (j : ℤ), HasLpSymbol p (symbol η j) (projection p η j)

def signedType : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ η : Euclidean d → ℝ, Annular η → SignedControl η

def upperType : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ η : Euclidean d → ℝ, Annular η →
    ∀ p : Exponent, ∃ C : ℝ≥0, 0 < C ∧ UpperBound p η C

/-- Full assigned obligation: all cutoffs and all 1<p<∞; both projection
families, uniform signed control, finite and infinite upper estimates. -/
def theoremType : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ χ : Euclidean d → ℝ, IsCutoff χ → IsPartition χ →
    ∃ ηtilde : Euclidean d → ℝ,
      Annular ηtilde ∧ HasCompactSupport ηtilde ∧
      (∀ ξ ∈ tsupport (annulus χ), ηtilde ξ = 1) ∧
      SignedControl (annulus χ) ∧ SignedControl ηtilde ∧
      ∀ p : Exponent,
        (∀ j, HasLpSymbol p (symbol (annulus χ) j) (projection p (annulus χ) j)) ∧
        (∀ j, HasLpSymbol p (symbol ηtilde j) (projection p ηtilde j)) ∧
        ∃ C : ℝ≥0, 0 < C ∧ UpperBound p (annulus χ) C ∧ UpperBound p ηtilde C

end P102.Specs.U3.LittlewoodPaleyUpper
