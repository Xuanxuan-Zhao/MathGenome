import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
Independent specification of K03.16.bernstein (paper.tex:3875–3891).
The domain `unitInterval` is exactly the closed real interval [0,1], with
its subtype topology. `bernstein.z k` has real coordinate k/n, including
both endpoint nodes when n ≥ 1. `Fin (n+1)` enumerates precisely 0,…,n.
Real scalar multiplication of a complex number is multiplication by its
real embedding. The finite formulas below identify the canonical continuous
Bernstein basis and approximation with the manuscript's objects; the
polynomial representation statements assert actual scalar polynomials.
No convergence assertion is assumed here.
-/
noncomputable section
open scoped BigOperators unitInterval

namespace Specs.SingleVariableAnalysis.Ch16.Bernstein

def weightType := ℕ → ℕ → ℝ → ℝ

def weightValue : weightType := fun n k x =>
  (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)

def realApproximationType := ℕ → C(I, ℝ) → C(I, ℝ)

def realApproximationValue : realApproximationType := fun n f =>
  ∑ k : Fin (n + 1), bernstein n k • ContinuousMap.const I (f (bernstein.z k))

def complexApproximationType := ℕ → C(I, ℂ) → C(I, ℂ)

def complexApproximationValue : complexApproximationType := fun n f =>
  ∑ k : Fin (n + 1), bernstein n k • ContinuousMap.const I (f (bernstein.z k))

def nodeCoordinate : Prop := ∀ (n : ℕ) (k : Fin (n + 1)),
  (bernstein.z k : ℝ) = (k : ℝ) / n

def weightCanonical : Prop := ∀ (n k : ℕ) (x : ℝ),
  weightValue n k x = (bernsteinPolynomial ℝ n k).eval x

def weightContinuousCanonical : Prop := ∀ (n k : ℕ) (x : I),
  weightValue n k x = bernstein n k x

def weightNonnegative : Prop := ∀ (n k : ℕ) (x : ℝ),
  x ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ weightValue n k x

def weightSum : Prop := ∀ (n : ℕ) (x : ℝ),
  (∑ k ∈ Finset.range (n + 1), weightValue n k x) = 1

def weightMean : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (x : ℝ),
  (∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n) * weightValue n k x) = x

def weightVariance : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (x : ℝ),
  x ∈ Set.Icc (0 : ℝ) 1 →
  (∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 2 * weightValue n k x) =
    x * (1 - x) / n

def weightEndpoints : Prop := ∀ (n k : ℕ),
  weightValue n k 0 = (if k = 0 then 1 else 0) ∧
  weightValue n k 1 = (if k = n then 1 else 0)

def realFormula : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (f : C(I, ℝ)) (x : I),
  realApproximationValue n f x =
    ∑ k : Fin (n + 1), f (bernstein.z k) * weightValue n k x

def complexFormula : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (f : C(I, ℂ)) (x : I),
  complexApproximationValue n f x =
    ∑ k : Fin (n + 1), f (bernstein.z k) * (weightValue n k x : ℂ)

def realCanonical : Prop := ∀ (n : ℕ) (f : C(I, ℝ)),
  realApproximationValue n f = bernsteinApproximation n f

def complexCanonical : Prop := ∀ (n : ℕ) (f : C(I, ℂ)),
  complexApproximationValue n f = bernsteinApproximation n f

def realPolynomial : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (f : C(I, ℝ)),
  ∃ p : Polynomial ℝ, ∀ x : I, realApproximationValue n f x = p.eval (x : ℝ)

def complexPolynomial : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (f : C(I, ℂ)),
  ∃ p : Polynomial ℂ, ∀ x : I, complexApproximationValue n f x = p.eval ((x : ℝ) : ℂ)

def realEndpoints : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (f : C(I, ℝ)),
  realApproximationValue n f 0 = f 0 ∧ realApproximationValue n f 1 = f 1

def complexEndpoints : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (f : C(I, ℂ)),
  complexApproximationValue n f 0 = f 0 ∧ complexApproximationValue n f 1 = f 1

end Specs.SingleVariableAnalysis.Ch16.Bernstein
