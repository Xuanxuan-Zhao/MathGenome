import MathGenome.Internal.Specs.D07.Ch11.PolynomialUnitsNilpotentCoefficientIdeal
import Mathlib.Data.ZMod.Basic

/-!
Independent statements of K07.11.polynomial_units, paper.tex:2279–2315.
The objects are formal polynomials with their canonical ring operations.
The general criterion permits the zero ring and imposes neither a domain
nor a uniform nilpotence exponent. The domain assertion explicitly retains
nontriviality through `IsDomain`. The final assertion uses the actual residue
ring modulo four and asserts nonconstancy as a statement about polynomials.
-/

universe u

namespace Specs.D07.Ch11.PolynomialUnits

open Polynomial

def DomainUnitIffConstant : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (f : Polynomial R),
    IsUnit f ↔ ∃ a : R, IsUnit a ∧ f = C a

def UnitIffCoefficients : Prop :=
  ∀ (R : Type u) [CommRing R] (f : Polynomial R),
    IsUnit f ↔ IsUnit (f.coeff 0) ∧
      ∀ i : ℕ, 0 < i → IsNilpotent (f.coeff i)

def NonconstantUnitExample : Prop :=
  let f : Polynomial (ZMod 4) := 1 + C 2 * X
  let g : Polynomial (ZMod 4) := 1 - C 2 * X
  f * g = 1 ∧ g * f = 1 ∧ IsUnit f ∧
    (∀ a : ZMod 4, f ≠ C a)

end Specs.D07.Ch11.PolynomialUnits
