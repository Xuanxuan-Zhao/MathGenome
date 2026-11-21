import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.BestExistence

noncomputable section

namespace P102.Approximation

/-- Minimality among all real polynomials of degree at most `n`. -/
def IsBestPolynomial {a b : ℝ} (f : C(Set.Icc a b, ℝ)) (n : ℕ)
    (p : Polynomial ℝ) : Prop :=
  p.degree ≤ (n : WithBot ℕ) ∧
    ∀ q : Polynomial ℝ, q.degree ≤ (n : WithBot ℕ) →
      ‖f - p.toContinuousMapOn (Set.Icc a b)‖ ≤
        ‖f - q.toContinuousMapOn (Set.Icc a b)‖

/-- `n+2` ordered, alternating, signed extreme errors, all in the given interval. -/
def HasAlternation {a b : ℝ} (f : C(Set.Icc a b, ℝ)) (n : ℕ)
    (p : Polynomial ℝ) : Prop :=
  ∃ x : Fin (n + 2) → Set.Icc a b,
    StrictMono (fun i => (x i : ℝ)) ∧
      ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
        ∀ i, f (x i) - p.eval (x i : ℝ) =
          σ * (-1 : ℝ) ^ (i : ℕ) * ‖f - p.toContinuousMapOn (Set.Icc a b)‖

end P102.Approximation

namespace Specs.P102.Approximation.Alternation
open _root_.P102.Approximation

/-- Sufficiency in the positive-error alternation criterion. -/
def AlternationSufficient : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (f : C(Set.Icc a b, ℝ)) (n : ℕ)
    (p : Polynomial ℝ), p.degree ≤ (n : WithBot ℕ) →
    0 < ‖f - p.toContinuousMapOn (Set.Icc a b)‖ →
    HasAlternation f n p → IsBestPolynomial f n p

/-- Necessity and sufficiency, with precisely the source's positive-error hypothesis. -/
def AlternationIff : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (f : C(Set.Icc a b, ℝ)) (n : ℕ)
    (p : Polynomial ℝ), p.degree ≤ (n : WithBot ℕ) →
    0 < ‖f - p.toContinuousMapOn (Set.Icc a b)‖ →
    (IsBestPolynomial f n p ↔ HasAlternation f n p)

/-- Exact data have a unique minimizing polynomial, as an equality of polynomials. -/
def ZeroErrorUnique : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (f : C(Set.Icc a b, ℝ)) (n : ℕ)
    (p q : Polynomial ℝ), p.degree ≤ (n : WithBot ℕ) →
    ‖f - p.toContinuousMapOn (Set.Icc a b)‖ = 0 →
    IsBestPolynomial f n q → p = q

/-- Existence and uniqueness, including degree zero and exact polynomial data. -/
def UniqueBest : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (f : C(Set.Icc a b, ℝ)) (n : ℕ),
    ∃! p : Polynomial ℝ, IsBestPolynomial f n p

end Specs.P102.Approximation.Alternation
