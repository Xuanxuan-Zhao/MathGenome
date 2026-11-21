import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Independent statements for paper.tex, Proposition p206:W72 and its examples. -/
namespace Specs.NumAnalysis206.Iterations.InverseSlope
open Set

/-- The closed segment includes either ordering and the coincident endpoints. -/
def Certificate : Prop :=
  ∀ (f : ℝ → ℝ) (x p m : ℝ), f p = 0 → 0 < m →
    ContinuousOn f (uIcc p x) →
    DifferentiableOn ℝ f (Ioo (min p x) (max p x)) →
    (∀ t ∈ Ioo (min p x) (max p x), m ≤ |deriv f t|) →
    |x - p| ≤ |f x| / m

/-- A slope bound verified throughout a bracket restricts to any root segment. -/
def BracketCertificate : Prop :=
  ∀ (f : ℝ → ℝ) (a b x p m : ℝ), x ∈ Icc a b → p ∈ Icc a b →
    f p = 0 → 0 < m → ContinuousOn f (Icc a b) →
    DifferentiableOn ℝ f (Ioo a b) →
    (∀ t ∈ Ioo a b, m ≤ |deriv f t|) → |x - p| ≤ |f x| / m

/-- The certified root need not have a known location inside the bracket. -/
def BracketRootCertificate : Prop :=
  ∀ (f : ℝ → ℝ) (a b x m : ℝ), x ∈ Icc a b →
    (∃ p ∈ Icc a b, f p = 0) → 0 < m → ContinuousOn f (Icc a b) →
    DifferentiableOn ℝ f (Ioo a b) →
    (∀ t ∈ Ioo a b, m ≤ |deriv f t|) →
    ∃ p ∈ Icc a b, f p = 0 ∧ |x - p| ≤ |f x| / m

/-- No finite real coefficient works in any neighborhood of the double root. -/
def SquareCounterexample : Prop :=
  (fun x : ℝ => x ^ 2) 0 = 0 ∧
  ∀ (C r : ℝ), 0 < r →
    ∃ x : ℝ, 0 < |x - 0| ∧ |x - 0| < r ∧
      C * |(fun t : ℝ => t ^ 2) x| < |x - 0|

/-- Exact root, derivative, residual and error for every positive slope. -/
def LinearResidualFacts : Prop :=
  ∀ σ : ℝ, 0 < σ →
    (fun t : ℝ => σ * t) 0 = 0 ∧
    deriv (fun t : ℝ => σ * t) 0 = σ ∧
    |(1 : ℝ) - 0| = 1 ∧ |(fun t : ℝ => σ * t) 1| = σ

/-- Even simple linear roots allow arbitrarily small residual at fixed error one,
violating any proposed function-independent linear inverse-residual coefficient. -/
def LinearCounterexample : Prop :=
  ∀ (C ε : ℝ), 0 < ε → ∃ σ : ℝ, 0 < σ ∧
    (fun t : ℝ => σ * t) 0 = 0 ∧
    deriv (fun t : ℝ => σ * t) 0 = σ ∧
    |(1 : ℝ) - 0| = 1 ∧
    |(fun t : ℝ => σ * t) 1| = σ ∧
    |(fun t : ℝ => σ * t) 1| < ε ∧
    C * |(fun t : ℝ => σ * t) 1| < |(1 : ℝ) - 0|

end Specs.NumAnalysis206.Iterations.InverseSlope
