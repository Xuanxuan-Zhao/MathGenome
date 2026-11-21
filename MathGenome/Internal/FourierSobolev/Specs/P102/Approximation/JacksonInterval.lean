import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.JacksonInverse
import Mathlib.Topology.ContinuousMap.Polynomial

/-! Algebraic Jackson approximation on a real compact interval.  The modulus
uses ordinary distance and the error uses the actual uniform norm.  Coefficients
are real for real functions and complex for complex functions. -/
noncomputable section
open Set

namespace P102.Approximation.JacksonInterval.Expected

abbrev Interval (a b : ℝ) := Icc a b

/-- Restriction of an algebraic polynomial to the real interval. -/
def polynomialMap {𝕜 : Type*} [RCLike 𝕜] (a b : ℝ)
    (p : Polynomial 𝕜) : C(Interval a b, 𝕜) :=
  ⟨fun x => p.eval (algebraMap ℝ 𝕜 (x : ℝ)), by fun_prop⟩

def modulusValue {E : Type*} [NormedAddCommGroup E] (a b : ℝ)
    (f : C(Interval a b, E)) (δ : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x y : Interval a b, dist x y ≤ δ ∧ r = ‖f x - f y‖}

def bestErrorValue {𝕜 : Type*} [RCLike 𝕜] (a b : ℝ)
    (f : C(Interval a b, 𝕜)) (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ p : Polynomial 𝕜, p.natDegree ≤ n ∧
    r = ‖f - polynomialMap a b p‖}

def modulusType := ∀ {E : Type*} [NormedAddCommGroup E] (a b : ℝ),
  C(Interval a b, E) → ℝ → ℝ

def bestErrorType := ∀ {𝕜 : Type*} [RCLike 𝕜] (a b : ℝ),
  C(Interval a b, 𝕜) → ℕ → ℝ

/-- The constant is independent of the interval, function, degree, and field. -/
def directStatement : Prop := ∃ C : ℝ, 0 ≤ C ∧
  ∀ (a b : ℝ), a < b → ∀ n : ℕ, 1 ≤ n →
    (∀ f : C(Interval a b, ℝ),
      bestErrorValue a b f n ≤ C * modulusValue a b f ((b - a) / (n : ℝ))) ∧
    (∀ f : C(Interval a b, ℂ),
      bestErrorValue a b f n ≤ C * modulusValue a b f ((b - a) / (n : ℝ)))

/-- A singleton is approximated exactly by a constant, including degree zero. -/
def singletonStatement : Prop := ∀ (a : ℝ) (n : ℕ),
  (∀ f : C(Interval a a, ℝ), bestErrorValue a a f n = 0) ∧
  (∀ f : C(Interval a a, ℂ), bestErrorValue a a f n = 0)

/-- The complete Theorem 1.15, including arbitrary positive periods, both
coefficient fields, and exactly the periodic range 0 < α < 1. -/
def jacksonStatement : Prop :=
  JacksonPeriodic.Expected.directStatement ∧
  JacksonInverse.Expected.equivalenceStatement ∧ directStatement ∧ singletonStatement

end P102.Approximation.JacksonInterval.Expected
