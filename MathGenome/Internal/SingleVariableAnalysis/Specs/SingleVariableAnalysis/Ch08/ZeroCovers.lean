import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Nonnegative
import Mathlib.Data.Set.Countable
import Mathlib.Order.Interval.Set.OrdConnected

/-!
Independent specification of K03.08.zero_covers, paper.tex:2142–2167.
The covering intervals have finite real endpoints, and are open and nonempty.
Lean index n represents source index n+1. The total length is the upstream
extended nonnegative sum, so divergence is not assigned a default real sum.
No integral or measure predicate is used in this definition.

The last statement expresses the assertion for every nondegenerate interval,
including unbounded intervals and every choice of endpoint inclusion:
an order-connected set with two distinct ordered points contains [c,d].
-/
namespace Specs.SingleVariableAnalysis.Ch08.ZeroCovers

open Set
open scoped BigOperators ENNReal
open Specs.SingleVariableAnalysis.Ch11.Nonnegative

def lengthZeroType := Set ℝ → Prop

def lengthZeroValue : lengthZeroType := fun E =>
  ∀ ε : ℝ, 0 < ε → ∃ a b : ℕ → ℝ,
    (∀ n, a n < b n) ∧ E ⊆ ⋃ n, Ioo (a n) (b n) ∧
      nonnegativeExtendedSumValue (fun n => b n - a n) < ENNReal.ofReal ε

def lengthZeroSubset : Prop :=
  ∀ E F : Set ℝ, E ⊆ F → lengthZeroValue F → lengthZeroValue E

def lengthZeroIUnion : Prop :=
  ∀ E : ℕ → Set ℝ, (∀ n, lengthZeroValue (E n)) →
    lengthZeroValue (⋃ n, E n)

def lengthZeroSingleton : Prop := ∀ x : ℝ, lengthZeroValue {x}

def lengthZeroEmpty : Prop := lengthZeroValue ∅

def lengthZeroCountable : Prop :=
  ∀ E : Set ℝ, E.Countable → lengthZeroValue E

def finiteIntervalCoverLength : Prop :=
  ∀ (s : Finset ℕ) (a b : ℕ → ℝ) (c d : ℝ),
    (∀ i ∈ s, a i ≤ b i) →
    Icc c d ⊆ ⋃ i ∈ s, Ioo (a i) (b i) →
      d - c ≤ ∑ i ∈ s, (b i - a i)

def countableIntervalCoverLength : Prop :=
  ∀ (a b : ℕ → ℝ) (c d : ℝ), (∀ i, a i ≤ b i) →
    Icc c d ⊆ ⋃ i, Ioo (a i) (b i) →
      ENNReal.ofReal (d - c) ≤ nonnegativeExtendedSumValue (fun i => b i - a i)

def notLengthZeroOfContainsIcc : Prop :=
  ∀ (E : Set ℝ) (c d : ℝ), c < d → Icc c d ⊆ E → ¬ lengthZeroValue E

def intervalNotLengthZero : Prop :=
  ∀ E : Set ℝ, E.OrdConnected →
    (∃ c ∈ E, ∃ d ∈ E, c < d) → ¬ lengthZeroValue E

end Specs.SingleVariableAnalysis.Ch08.ZeroCovers
