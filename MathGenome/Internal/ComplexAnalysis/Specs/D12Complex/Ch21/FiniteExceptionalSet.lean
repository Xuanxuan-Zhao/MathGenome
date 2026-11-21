import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.FractionFieldIrreducibility
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! Independent specification of paper.tex:3566–3604 (D12.21.02).
The inner polynomial variable is z and the outer variable is w. All
exceptional parameters and roots here are finite complex numbers. The
separate behavior over infinity belongs to the subsequent local-parameter
and growth results; no point at infinity is included in this set.
-/

noncomputable section
open Polynomial

namespace Specs.D12Complex.Ch21.FiniteExceptionalSet

def fiber_type := Polynomial (Polynomial ℂ) → ℂ → Polynomial ℂ
def fiber_value (P : Polynomial (Polynomial ℂ)) (z : ℂ) : Polynomial ℂ :=
  P.map (Polynomial.evalRingHom z)

def resultantPolynomial_type := Polynomial (Polynomial ℂ) → Polynomial ℂ
/-- This is the determinant-defined resultant, not an arbitrary polynomial
chosen to vanish at some bad parameters. -/
def resultantPolynomial_value (P : Polynomial (Polynomial ℂ)) : Polynomial ℂ :=
  P.resultant P.derivative

def exceptionalSet_type := Polynomial (Polynomial ℂ) → Set ℂ
def exceptionalSet_value (P : Polynomial (Polynomial ℂ)) : Set ℂ :=
  {z | (P.leadingCoeff * resultantPolynomial_value P).eval z = 0}

/-- The source orders the domain as (A,B) with degree bounds d-1,d,
and sends it to AP + BP_w. Mathlib's matrix for (P_w,P) has exactly
this order. Its size is (d-1)+d, also when d=1. -/
def resultant_sylvester_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    P.natDegree = d → 0 < d →
    resultantPolynomial_value P =
      (Polynomial.sylvester P.derivative P (d - 1) d).det

/-- Specialization uses the original degree bounds, so this holds even
at parameters where one of the actual specialized degrees drops. -/
def resultant_specialize_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    P.natDegree = d → 0 < d → ∀ z : ℂ,
    (resultantPolynomial_value P).eval z =
      (fiber_value P z).resultant (fiber_value P z).derivative d (d - 1)

/-- Explicitly retain the zero-dimensional first summand for d=1. -/
def resultant_degree_one_type : Prop :=
  ∀ P : Polynomial (Polynomial ℂ), P.natDegree = 1 →
    resultantPolynomial_value P = P.leadingCoeff

def resultant_nonzero_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    resultantPolynomial_value P ≠ 0

/-- Cardinality and membership describe every finite root, and nodup plus
the multiplicity conclusion record distinctness and simplicity. -/
def finite_exceptional_set_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    resultantPolynomial_value P ≠ 0 ∧
    (exceptionalSet_value P).Finite ∧
    ∀ z : ℂ, z ∉ exceptionalSet_value P →
      (fiber_value P z).natDegree = d ∧
      (fiber_value P z).roots.Nodup ∧
      (fiber_value P z).roots.toFinset.card = d ∧
      (∀ w : ℂ, w ∈ (fiber_value P z).roots.toFinset ↔
        (fiber_value P z).eval w = 0) ∧
      (∀ w : ℂ, (fiber_value P z).eval w = 0 →
        (fiber_value P z).rootMultiplicity w = 1 ∧
        (fiber_value P z).derivative.eval w ≠ 0)

end Specs.D12Complex.Ch21.FiniteExceptionalSet
