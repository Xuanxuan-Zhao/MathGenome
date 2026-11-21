import MathGenome.Internal.Specs.D07.Ch11.DegreeConventions
import MathGenome.Internal.Specs.D07.Ch11.PolynomialArithmetic
import Mathlib.Data.ZMod.Basic

/-!
Independent specification of K07.11.degree_arithmetic
(paper.tex:2202–2229; chapters/M07.11.tex:57–84).

These are the same formal polynomials, coefficients and bottom-valued degree
as in the upstream specifications. General bounds permit the zero ring and
zero polynomials. Equality requires the stated nonzero leading product, not
a domain hypothesis. The unit assertion concerns either leading coefficient.
The concrete example uses the residue ring `ZMod 4` and the formal polynomial
`C 2 * X`; neither evaluation functions nor natural degree replace degree.
-/

universe u

namespace Specs.D07.Ch11.DegreeArithmetic

open Polynomial

def DegreeAdditionBound : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : Polynomial R),
    (f + g).degree ≤ max f.degree g.degree

def DegreeMultiplicationBound : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : Polynomial R),
    (f * g).degree ≤ f.degree + g.degree

def ProductOfNonzeroLeadingCoefficients : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : Polynomial R),
    f ≠ 0 → g ≠ 0 → f.leadingCoeff * g.leadingCoeff ≠ 0 →
      f * g ≠ 0 ∧
      (f * g).degree = f.degree + g.degree ∧
      (f * g).leadingCoeff = f.leadingCoeff * g.leadingCoeff

/-- A unit leading coefficient cannot annihilate the other nonzero one. -/
def LeadingProductNonzeroOfUnit : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : Polynomial R),
    f ≠ 0 → g ≠ 0 → (IsUnit f.leadingCoeff ∨ IsUnit g.leadingCoeff) →
      f.leadingCoeff * g.leadingCoeff ≠ 0

def ProductOfUnitLeadingCoefficient : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : Polynomial R),
    f ≠ 0 → g ≠ 0 → (IsUnit f.leadingCoeff ∨ IsUnit g.leadingCoeff) →
      f * g ≠ 0 ∧
      (f * g).degree = f.degree + g.degree ∧
      (f * g).leadingCoeff = f.leadingCoeff * g.leadingCoeff

/-- The canonical polynomial ring, with its existing operations, is a domain. -/
def PolynomialDomain : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R], IsDomain (Polynomial R)

def ProductOverDomain : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (f g : Polynomial R),
    f ≠ 0 → g ≠ 0 →
      f * g ≠ 0 ∧
      (f * g).degree = f.degree + g.degree ∧
      (f * g).leadingCoeff = f.leadingCoeff * g.leadingCoeff

/-- Both displayed factors are `2X`, nonzero of degree one, but their product
and square vanish, so the degree inequality is strict. -/
def DegreeDropExample : Prop :=
  let f : Polynomial (ZMod 4) := C 2 * X
  let g : Polynomial (ZMod 4) := C 2 * X
  f ≠ 0 ∧ g ≠ 0 ∧
    f.degree = (1 : WithBot ℕ) ∧ g.degree = (1 : WithBot ℕ) ∧
    f * g = 0 ∧ f ^ 2 = 0 ∧
    (f * g).degree = ⊥ ∧ (f * g).degree < f.degree + g.degree

end Specs.D07.Ch11.DegreeArithmetic
