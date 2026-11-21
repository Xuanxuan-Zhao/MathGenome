import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Basis.Defs

/-! Independent specifications for paper.tex, W46–W47.
`degreeLE K n` includes zero; all degree inequalities use `WithBot ℕ`.
The finite-set indexing permits empty data, but uniqueness in degree ≤ n
is asserted only when the number of nodes is n + 1. -/

noncomputable section
open Polynomial

universe u v
namespace Specs.NumAnalysis206.Approximation

variable {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]

/-- Each quotient is multiplication by the inverse of its scalar denominator. -/
def cardinalValue (s : Finset ι) (x : ι → K) (i : ι) : K[X] :=
  ∏ j ∈ s.erase i, C ((x i - x j)⁻¹) * (X - C (x j))

def cardinalType :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι],
    Finset ι → (ι → K) → ι → K[X]

def interpolantValue (s : Finset ι) (x y : ι → K) : K[X] :=
  ∑ i ∈ s, C (y i) * cardinalValue s x i

def interpolantType :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι],
    Finset ι → (ι → K) → (ι → K) → K[X]

-- W46: construction, degree, cardinal values and edge cases.
def cardinalDegree : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (x : ι → K), Set.InjOn x s →
    ∀ i ∈ s, (cardinalValue s x i).degree ≤ (s.card - 1 : ℕ)

def cardinalEval : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (x : ι → K), Set.InjOn x s →
    ∀ i ∈ s, ∀ j ∈ s,
      (cardinalValue s x i).eval (x j) = if i = j then 1 else 0

def interpolantEval : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (x y : ι → K), Set.InjOn x s →
    ∀ i ∈ s, (interpolantValue s x y).eval (x i) = y i

def interpolantDegreeLt : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (x y : ι → K), Set.InjOn x s →
    (interpolantValue s x y).degree < (s.card : WithBot ℕ)

def cardinalSingleton : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (x : ι → K) (i : ι), cardinalValue {i} x i = 1

def interpolantEmpty : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (x y : ι → K), interpolantValue ∅ x y = 0

-- W47: the degree convention is bridged explicitly, including zero.
def degreeLeIffLtCard : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (n : ℕ), s.card = n + 1 →
    ∀ p : K[X], p.degree ≤ (n : WithBot ℕ) ↔ p.degree < (s.card : WithBot ℕ)

def interpolantUnique : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (x y : ι → K) (n : ℕ),
    Set.InjOn x s → s.card = n + 1 →
    ∀ p : K[X],
      (p.degree ≤ (n : WithBot ℕ) ∧ ∀ i ∈ s, p.eval (x i) = y i) ↔
      p = interpolantValue s x y

def existsUniqueInterpolant : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (x y : ι → K) (n : ℕ),
    Set.InjOn x s → s.card = n + 1 →
    ∃! p : K[X], p.degree ≤ (n : WithBot ℕ) ∧ ∀ i ∈ s, p.eval (x i) = y i

/-- The actual cardinal polynomials constitute a basis of P_n(K), and
its coordinates are precisely evaluation at the nodes (the duality claim). -/
def cardinalBasis : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (x : ι → K) (n : ℕ),
    Set.InjOn x s → s.card = n + 1 →
    ∃ b : Module.Basis s K (Polynomial.degreeLE K (n : WithBot ℕ)),
      (∀ i : s, (b i).val = cardinalValue s x i) ∧
      (∀ (p : Polynomial.degreeLE K (n : WithBot ℕ)) (i : s),
        b.repr p i = p.val.eval (x i))

def emptyDataNotUnique : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (x y : ι → K) (n : ℕ),
    ¬ ∃! p : K[X], p.degree ≤ (n : WithBot ℕ) ∧
      ∀ i ∈ (∅ : Finset ι), p.eval (x i) = y i

end Specs.NumAnalysis206.Approximation
