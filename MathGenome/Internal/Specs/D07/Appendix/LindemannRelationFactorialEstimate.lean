import MathGenome.Internal.Specs.D07.Appendix.LindemannRelationExponentialIntegralIdentity
import MathGenome.Internal.Specs.D07.Appendix.LindemannRelationIntegerScaling

/-!
Independent statements for paper.tex:7763–7781. A function on Fin m is a
finite root list, retaining repetitions; no distinctness assumption is made.
The analytic estimates only need the scaled factorization, so do not require
the nonzero-root and rationality hypotheses used to construct that data.
The final prime specialization retains the manuscript's integer hypotheses.
-/

noncomputable section

namespace Specs.D07.Appendix.LindemannRelationFactorialEstimate

open Polynomial Filter
open scoped BigOperators Topology

/-- Exactly H_p(T) = T^(p-1) Q(T)^p, over the integers. -/
def auxiliaryPolynomial (Q : ℤ[X]) (p : ℕ) : ℤ[X] := X ^ (p - 1) * Q ^ p

/-- Exactly f_p(x) = H_p(a*x)/(p-1)!, as a complex polynomial. -/
def sourcePolynomial (a : ℤ) (Q : ℤ[X]) (p : ℕ) : ℂ[X] :=
  C ((Nat.factorial (p - 1) : ℂ)⁻¹) *
    ((auxiliaryPolynomial Q p).map (algebraMap ℤ ℂ)).comp (C (a : ℂ) * X)

def SourcePolynomialType := ℤ → ℤ[X] → ℕ → ℂ[X]
def sourcePolynomialValue : SourcePolynomialType := sourcePolynomial

/-- The right-hand side of equation (3), before taking its norm. -/
def weightedIntegralSum {m : ℕ} (β : Fin m → ℂ) (a : ℤ) (Q : ℤ[X]) (p : ℕ) : ℂ :=
  ∑ j, β j * ∫ t : ℝ in 0..1,
    Complex.exp ((1 - (t : ℂ)) * β j) * (sourcePolynomial a Q p).eval ((t : ℂ) * β j)

def WeightedIntegralSumType := ∀ {m : ℕ}, (Fin m → ℂ) → ℤ → ℤ[X] → ℕ → ℂ
def weightedIntegralSumValue : WeightedIntegralSumType := @weightedIntegralSum

/-- One choice of R and C works simultaneously for every p, j, and t.
The positive-natural version implies the stated prime version. -/
def UniformFactorialEstimate : Prop :=
  ∀ (m : ℕ) (β : Fin m → ℂ) (a : ℤ) (Q : ℤ[X]),
    Q.map (algebraMap ℤ ℂ) = ∏ j, (X - C ((a : ℂ) * β j)) →
    ∃ R C : ℝ, 1 ≤ R ∧ C = R * (2 * R) ^ m ∧ 1 ≤ C ∧
      (∀ j, ‖(a : ℂ) * β j‖ ≤ R) ∧
      (∀ (j : Fin m) (t : ℝ), 0 ≤ t → t ≤ 1 → ‖(a : ℂ) * ((t : ℂ) * β j)‖ ≤ R) ∧
      (∀ (p : ℕ), 0 < p → ∀ (j : Fin m) (t : ℝ), 0 ≤ t → t ≤ 1 →
        ‖(sourcePolynomial a Q p).eval ((t : ℂ) * β j)‖ ≤
          C ^ p / (Nat.factorial (p - 1) : ℝ)) ∧
      (∀ (p : ℕ), 0 < p →
        ‖weightedIntegralSum β a Q p‖ ≤
          (∑ j, ‖β j‖ * Real.exp ‖β j‖) * (C ^ p / (Nat.factorial (p - 1) : ℝ)))

/-- The factorial dominates every fixed exponential, including the weight. -/
def FactorialDecay : Prop :=
  ∀ A C : ℝ,
    Tendsto (fun p : ℕ => A * (C ^ p / (Nat.factorial (p - 1) : ℝ))) atTop (𝓝 0)

def IntegralDecay : Prop :=
  ∀ (m : ℕ) (β : Fin m → ℂ) (a : ℤ) (Q : ℤ[X]),
    Q.map (algebraMap ℤ ℂ) = ∏ j, (X - C ((a : ℂ) * β j)) →
    Tendsto (weightedIntegralSum β a Q) atTop (𝓝 0)

/-- In particular, convergence holds along any sequence of arbitrarily
large allowed primes. No monotonicity of the sequence is required. -/
def DecayAlongAllowedPrimes : Prop :=
  ∀ (m : ℕ) (β : Fin m → ℂ) (a : ℤ) (Q : ℤ[X]) (k : ℤ),
    Q.map (algebraMap ℤ ℂ) = ∏ j, (X - C ((a : ℂ) * β j)) →
    ∀ u : ℕ → ℕ, Tendsto u atTop atTop →
      (∀ n, Nat.Prime (u n) ∧ ¬ (u n : ℤ) ∣ k * a * Q.coeff 0) →
      Tendsto (fun n => weightedIntegralSum β a Q (u n)) atTop (𝓝 0)

/-- The allowed primes are cofinal and make the integral sum as small as
desired. The bound and constants do not change with the prime. -/
def ArbitrarilyLargeSmallIntegrals : Prop :=
  ∀ (m : ℕ) (β : Fin m → ℂ) (a k : ℤ) (Q : ℤ[X]),
    0 < a → 0 < k → Q.coeff 0 ≠ 0 →
    Q.map (algebraMap ℤ ℂ) = ∏ j, (X - C ((a : ℂ) * β j)) →
    ∀ ε : ℝ, 0 < ε → ∀ B : ℕ,
      ∃ p : ℕ, B < p ∧ Nat.Prime p ∧ ¬ (p : ℤ) ∣ k * a * Q.coeff 0 ∧
        ‖weightedIntegralSum β a Q p‖ < ε

end Specs.D07.Appendix.LindemannRelationFactorialEstimate
