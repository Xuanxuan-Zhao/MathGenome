import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Recurrence.RepeatedRoots
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! The characteristic-zero, nonzero-root conclusion of paper.tex, p204:W16.
Degree is the WithBot-valued polynomial degree, so the zero polynomial is included.
The root space means generalized eigenvectors of the left shift within the
recurrence solution module. -/
noncomputable section
open scoped BigOperators
open Polynomial
universe u
namespace Specs.FiniteCombinatorics.Recurrence

def rootSpan {K : Type u} [Field K] (lam : K) (m : ℕ) : Submodule K (ℕ → K) :=
  Submodule.span K (Set.range (fun j : Fin m => rootSequenceValue lam j.val))

def exponential_polynomial_span : Prop :=
  ∀ {K : Type u} [Field K] [CharZero K] (lam : K), lam ≠ 0 →
    ∀ (m : ℕ) (a : ℕ → K),
      a ∈ rootSpan lam m ↔
        ∃ P : K[X], P.degree < m ∧ ∀ n : ℕ, a n = P.eval (n : K) * lam ^ n

def exponential_polynomial_unique : Prop :=
  ∀ {K : Type u} [Field K] [CharZero K] (lam : K), lam ≠ 0 →
    ∀ (m : ℕ) (a : ℕ → K), a ∈ rootSpan lam m →
      ∃! P : K[X], P.degree < m ∧ ∀ n : ℕ, a n = P.eval (n : K) * lam ^ n

def exponential_polynomial_root_space : Prop :=
  ∀ {K : Type u} [Field K] [CharZero K] {r : ℕ} (c : Fin r → K), 1 ≤ r →
    ∀ (s : Finset K) (m : K → ℕ), (∀ lam ∈ s, 0 < m lam) →
      characteristicPolynomialValue c = ∏ lam ∈ s, (X - C lam) ^ m lam →
      ∀ lam ∈ s, lam ≠ 0 →
        rootSpan lam (m lam) =
          solutionSpaceValue c ⊓ (leftShiftValue (K := K)).genEigenspace lam ⊤

/-- Direct formulation of the root-space description, including uniqueness. -/
def exponential_polynomial_root_space_iff : Prop :=
  ∀ {K : Type u} [Field K] [CharZero K] {r : ℕ} (c : Fin r → K), 1 ≤ r →
    ∀ (s : Finset K) (m : K → ℕ), (∀ lam ∈ s, 0 < m lam) →
      characteristicPolynomialValue c = ∏ lam ∈ s, (X - C lam) ^ m lam →
      ∀ lam ∈ s, lam ≠ 0 → ∀ a : ℕ → K,
        (a ∈ solutionSpaceValue c ∧ a ∈ (leftShiftValue (K := K)).genEigenspace lam ⊤) ↔
          ∃! P : K[X], P.degree < m lam ∧ ∀ n : ℕ, a n = P.eval (n : K) * lam ^ n

end Specs.FiniteCombinatorics.Recurrence
