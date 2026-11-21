import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.IntervalCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-! Taylor formulas for continuous closed-interval derivative data.
No values or regularity outside the interval are constrained. -/
namespace NumAnalysis206.Approximation.IntervalTaylorSpec
open Set
open scoped BigOperators

noncomputable def sumValue (D : ℕ → ℝ → ℝ) (r : ℕ) (c x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range r, D k c * (x - c) ^ k / (k.factorial : ℝ)

def sumType := (ℕ → ℝ → ℝ) → ℕ → ℝ → ℝ → ℝ

def lagrange_type : Prop :=
  ∀ {a b c x : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    a ≤ b → 1 ≤ r → IntervalCalculusSpec.jetValue a b r f D →
    c ∈ Icc a b → x ∈ Icc a b →
    ∃ ξ ∈ uIcc c x, f x = sumValue D r c x + D r ξ * (x - c) ^ r / (r.factorial : ℝ)

def bound_type : Prop :=
  ∀ {a b c x M : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    a ≤ b → 1 ≤ r → IntervalCalculusSpec.jetValue a b r f D →
    c ∈ Icc a b → x ∈ Icc a b →
    (∀ t ∈ uIcc c x, |D r t| ≤ M) →
    |f x - sumValue D r c x| ≤ M * |x - c| ^ r / (r.factorial : ℝ)

def integral_type : Prop :=
  ∀ {a b c x : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    a ≤ b → 1 ≤ r → IntervalCalculusSpec.jetValue a b r f D →
    c ∈ Icc a b → x ∈ Icc a b →
    f x = sumValue D r c x +
      ∫ t in c..x, D r t * (x - t) ^ (r - 1) / ((r - 1).factorial : ℝ)

def positive_part_type : Prop :=
  ∀ {a b x : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    a ≤ b → 2 ≤ r → IntervalCalculusSpec.jetValue a b r f D → x ∈ Icc a b →
    f x = sumValue D r a x +
      ∫ t in a..b, D r t * (max (x - t) 0) ^ (r - 1) / ((r - 1).factorial : ℝ)

end NumAnalysis206.Approximation.IntervalTaylorSpec
