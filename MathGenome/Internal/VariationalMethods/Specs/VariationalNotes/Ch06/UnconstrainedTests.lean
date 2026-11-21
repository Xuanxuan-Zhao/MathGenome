import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Basic

open Set Filter
open scoped Topology ContDiff

namespace Specs.VariationalNotes.Ch06

/-- Twice Fréchet differentiability at a point: genuine differentiability in a
neighborhood, and differentiability of the derivative map at the point.
There is no neighborhood continuity assumption on the second derivative. -/
def TwiceFrechetAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → ℝ) (a : X) (B : X →L[ℝ] X →L[ℝ] ℝ) : Prop :=
  (∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x) ∧ HasFDerivAt (fderiv ℝ f) B a

universe u

/-- The local minimum is relative to the given open domain. -/
def FirstOrder : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] (U : Set X) (f : X → ℝ) (a : X),
    IsOpen U → a ∈ U → IsLocalMinOn f U a → DifferentiableAt ℝ f a →
    fderiv ℝ f a = 0

/-- The Hessian is the derivative of the first derivative, evaluated twice
on a direction. -/
def SecondOrderNecessary : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] (U : Set X) (f : X → ℝ) (a : X)
    (B : X →L[ℝ] X →L[ℝ] ℝ),
    IsOpen U → a ∈ U → IsLocalMinOn f U a → TwiceFrechetAt f a B →
    ∀ d : X, 0 ≤ B d d

/-- Positive definiteness gives quantitative quadratic growth on a ball
contained in the original domain. No positive-dimensional assumption. -/
def SecondOrderSufficient : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] (U : Set X) (f : X → ℝ) (a : X)
    (B : X →L[ℝ] X →L[ℝ] ℝ),
    IsOpen U → a ∈ U → TwiceFrechetAt f a B → fderiv ℝ f a = 0 →
    (∀ d : X, d ≠ 0 → 0 < B d d) →
    ∃ c > 0, ∃ ρ > 0, Metric.ball a ρ ⊆ U ∧
      ∀ x ∈ Metric.ball a ρ, f a + c * ‖x - a‖ ^ 2 ≤ f x

/-- The scalar examples have the same vanishing first and second derivative
at zero, but opposite strict extrema (in fact global strict extrema). -/
def FourthPowerExamples : Prop :=
  ContDiff ℝ ∞ (fun x : ℝ => x ^ 4) ∧
  ContDiff ℝ ∞ (fun x : ℝ => -(x ^ 4)) ∧
  deriv (fun x : ℝ => x ^ 4) 0 = 0 ∧
  deriv (deriv (fun x : ℝ => x ^ 4)) 0 = 0 ∧
  deriv (fun x : ℝ => -(x ^ 4)) 0 = 0 ∧
  deriv (deriv (fun x : ℝ => -(x ^ 4))) 0 = 0 ∧
  TwiceFrechetAt (fun x : ℝ => x ^ 4) 0 0 ∧
  fderiv ℝ (fun x : ℝ => x ^ 4) 0 = 0 ∧
  TwiceFrechetAt (fun x : ℝ => -(x ^ 4)) 0 0 ∧
  fderiv ℝ (fun x : ℝ => -(x ^ 4)) 0 = 0 ∧
  (∀ x : ℝ, x ≠ 0 → (0 : ℝ) ^ 4 < x ^ 4) ∧
  (∀ x : ℝ, x ≠ 0 → -(x ^ 4) < -((0 : ℝ) ^ 4))

end Specs.VariationalNotes.Ch06
