import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.Lagrange
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Independent specifications for the operator and norm assertions of W52.
The polynomial space is embedded in the continuous real functions on the interval;
its norm is the inherited uniform norm, not a coefficient norm. -/
noncomputable section
open Polynomial
open scoped BigOperators

namespace NumAnalysis206.Approximation

abbrev IntervalContinuous (a b : ℝ) := C(Set.Icc a b, ℝ)

/-- Degree at most `n` polynomials, viewed as functions with the uniform norm. -/
def polynomialSpace (a b : ℝ) (n : ℕ) : Submodule ℝ (IntervalContinuous a b) :=
  (Polynomial.degreeLE ℝ (n : WithBot ℕ)).map
    (Polynomial.toContinuousMapOnAlgHom (Set.Icc a b)).toLinearMap

end NumAnalysis206.Approximation

namespace Specs.NumAnalysis206.Approximation
open _root_.NumAnalysis206.Approximation

/-- The cardinal sum is a continuous function on the compact interval. -/
def lebesgueFunction {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b) :
    IntervalContinuous a b :=
  ⟨fun t => ∑ i, |(cardinalValue Finset.univ (fun j => (x j : ℝ)) i).eval t|,
    by fun_prop⟩

/-- The maximum, equivalently the uniform norm of the nonnegative cardinal sum.
`lebesgueMaximum` below explicitly requires attainment and the upper bound. -/
def lebesgueConstantValue {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b) : ℝ :=
  ‖lebesgueFunction x‖

/-- Evaluation followed by the finite Lagrange sum, on the common uniform-norm space. -/
def interpolationOperatorValue {a b : ℝ} {n : ℕ}
    (x : Fin (n + 1) → Set.Icc a b) :
    IntervalContinuous a b →L[ℝ] IntervalContinuous a b :=
  ∑ i, (ContinuousMap.evalCLM ℝ (x i)).smulRight
    ((cardinalValue Finset.univ (fun j => (x j : ℝ)) i).toContinuousMapOn (Set.Icc a b))

def lebesgueFunctionType :=
  ∀ {a b : ℝ} {n : ℕ}, (Fin (n + 1) → Set.Icc a b) → IntervalContinuous a b

def lebesgueConstantType :=
  ∀ {a b : ℝ} {n : ℕ}, (Fin (n + 1) → Set.Icc a b) → ℝ

def interpolationOperatorType :=
  ∀ {a b : ℝ} {n : ℕ}, (Fin (n + 1) → Set.Icc a b) →
    (IntervalContinuous a b →L[ℝ] IntervalContinuous a b)

def interpolationFormula : Prop :=
  ∀ {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b)
    (f : IntervalContinuous a b) (t : Set.Icc a b),
    interpolationOperatorValue x f t =
      (interpolantValue Finset.univ (fun j => (x j : ℝ)) (fun j => f (x j))).eval (t : ℝ)

def interpolationNodes : Prop :=
  ∀ {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b), Function.Injective x →
    ∀ (f : IntervalContinuous a b) (i : Fin (n + 1)),
      interpolationOperatorValue x f (x i) = f (x i)

def interpolationRange : Prop :=
  ∀ {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b), Function.Injective x →
    ∀ f : IntervalContinuous a b, interpolationOperatorValue x f ∈ polynomialSpace a b n

def interpolationReproduces : Prop :=
  ∀ {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b), Function.Injective x →
    ∀ p : ℝ[X], p.degree ≤ (n : WithBot ℕ) →
      interpolationOperatorValue x (p.toContinuousMapOn (Set.Icc a b)) =
        p.toContinuousMapOn (Set.Icc a b)

def lebesgueMaximum : Prop :=
  ∀ {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b), a < b →
    ∃ t : Set.Icc a b,
      lebesgueConstantValue x = lebesgueFunction x t ∧
      ∀ u : Set.Icc a b, lebesgueFunction x u ≤ lebesgueConstantValue x

def interpolationNorm : Prop :=
  ∀ {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b), a < b →
    Function.Injective x → ‖interpolationOperatorValue x‖ = lebesgueConstantValue x

set_option backward.isDefEq.respectTransparency false in
/-- The range-restricted realization has exactly the same norm. -/
def polynomialValuedRealization : Prop :=
  ∀ {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b), a < b →
    Function.Injective x →
    ∃ J : IntervalContinuous a b →L[ℝ] polynomialSpace a b n,
      (∀ f, (J f : IntervalContinuous a b) = interpolationOperatorValue x f) ∧
      ‖J‖ = lebesgueConstantValue x

end Specs.NumAnalysis206.Approximation
