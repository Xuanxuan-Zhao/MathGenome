import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.Compact

noncomputable section

namespace P102.Approximation

/-- Restrictions to `[a,b]` of real polynomials of degree at most `n`. -/
def polynomialSpace (a b : ℝ) (n : ℕ) : Submodule ℝ C(Set.Icc a b, ℝ) :=
  (Polynomial.degreeLE ℝ (n : WithBot ℕ)).map
    (Polynomial.toContinuousMapOnAlgHom (Set.Icc a b)).toLinearMap

/-- The infimum of the uniform errors of all degree-at-most-`n` polynomials. -/
def bestError (a b : ℝ) (f : C(Set.Icc a b, ℝ)) (n : ℕ) : ℝ :=
  sInf ((fun p : Polynomial ℝ => ‖f - p.toContinuousMapOn (Set.Icc a b)‖) ''
    {p | p.degree ≤ (n : WithBot ℕ)})

end P102.Approximation

namespace Specs.P102.Approximation.BestExistence
open _root_.P102.Approximation

/-- The subspace is the actual polynomial evaluation image. -/
def SpaceCharacterization : Prop :=
  ∀ (a b : ℝ) (n : ℕ) (g : C(Set.Icc a b, ℝ)),
    g ∈ polynomialSpace a b n ↔
      ∃ p : Polynomial ℝ, p.degree ≤ (n : WithBot ℕ) ∧
        p.toContinuousMapOn (Set.Icc a b) = g

def SpaceFiniteDimensional : Prop :=
  ∀ (a b : ℝ) (n : ℕ), FiniteDimensional ℝ (polynomialSpace a b n)

/-- Every continuous error has a finite real uniform norm, attained on the interval. -/
def UniformNormAttained : Prop :=
  ∀ (a b : ℝ), a < b → ∀ g : C(Set.Icc a b, ℝ),
    ∃ x : Set.Icc a b, |g x| = ‖g‖ ∧ ∀ y : Set.Icc a b, |g y| ≤ ‖g‖

/-- Existence, including constants and zero approximation error. -/
def BestExists : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (f : C(Set.Icc a b, ℝ)) (n : ℕ),
    ∃ p : Polynomial ℝ, p.degree ≤ (n : WithBot ℕ) ∧
      ‖f - p.toContinuousMapOn (Set.Icc a b)‖ = bestError a b f n ∧
      ∀ q : Polynomial ℝ, q.degree ≤ (n : WithBot ℕ) →
        ‖f - p.toContinuousMapOn (Set.Icc a b)‖ ≤
          ‖f - q.toContinuousMapOn (Set.Icc a b)‖

end Specs.P102.Approximation.BestExistence
