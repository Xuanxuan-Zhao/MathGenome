import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.ZeroCovers
import Mathlib.Topology.Order.Basic

/-!
Independent specification of K03.08.zero_vs_content (paper.tex:2165–2177).
The set is the canonical rational points of the real closed unit interval.
Countable length zero uses precisely the preceding countable-cover definition.
Finite content zero uses finite open bounded interval covers. The lower bound
is also stated for closed bounded intervals, allowing degenerate intervals;
thus endpoint inclusion does not weaken the asserted finite-cover obstruction.
-/
namespace Specs.SingleVariableAnalysis.Ch08.ZeroVsContent

open Set
open scoped BigOperators

def rationalUnitIntervalType := Set ℝ

def rationalUnitIntervalValue : Set ℝ :=
  Set.range (fun q : ℚ => (q : ℝ)) ∩ Icc 0 1

def finiteContentZeroType := Set ℝ → Prop

def finiteContentZeroValue : finiteContentZeroType := fun E =>
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ℕ) (a b : ℕ → ℝ),
    (∀ i ∈ s, a i < b i) ∧ E ⊆ ⋃ i ∈ s, Ioo (a i) (b i) ∧
      (∑ i ∈ s, (b i - a i)) < ε

def rationalUnitIntervalLengthZero : Prop :=
  ZeroCovers.lengthZeroValue rationalUnitIntervalValue

def closureRationalUnitInterval : Prop :=
  closure rationalUnitIntervalValue = Icc (0 : ℝ) 1

def rationalUnitIntervalFiniteClosedCoverLength : Prop :=
  ∀ (s : Finset ℕ) (a b : ℕ → ℝ),
    (∀ i ∈ s, a i ≤ b i) →
    rationalUnitIntervalValue ⊆ ⋃ i ∈ s, Icc (a i) (b i) →
      1 ≤ ∑ i ∈ s, (b i - a i)

/-- This form covers open, closed, and half-open bounded intervals uniformly.
The covering sets may in fact be any subsets of the specified closed hulls. -/
def rationalUnitIntervalFiniteCoverLength : Prop :=
  ∀ (s : Finset ℕ) (a b : ℕ → ℝ) (J : ℕ → Set ℝ),
    (∀ i ∈ s, a i ≤ b i) →
    (∀ i ∈ s, J i ⊆ Icc (a i) (b i)) →
    rationalUnitIntervalValue ⊆ ⋃ i ∈ s, J i →
      1 ≤ ∑ i ∈ s, (b i - a i)

def rationalUnitIntervalFiniteOpenCoverLength : Prop :=
  ∀ (s : Finset ℕ) (a b : ℕ → ℝ),
    (∀ i ∈ s, a i ≤ b i) →
    rationalUnitIntervalValue ⊆ ⋃ i ∈ s, Ioo (a i) (b i) →
      1 ≤ ∑ i ∈ s, (b i - a i)

def rationalUnitIntervalNotFiniteContentZero : Prop :=
  ¬ finiteContentZeroValue rationalUnitIntervalValue

def lengthZeroNotFiniteContentZero : Prop :=
  ∃ E : Set ℝ, ZeroCovers.lengthZeroValue E ∧ ¬ finiteContentZeroValue E

end Specs.SingleVariableAnalysis.Ch08.ZeroVsContent
