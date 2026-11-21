import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Data.Rat.Cast.Defs

/-!
Independent statements for K07.11.shift_irreducibility, paper.tex:2726–2742.
The variable is formal and substitution is `Polynomial.comp`. The general
statements allow every commutative unital ring, including the zero ring.
The multiplier is a unit of that same coefficient ring.
-/

universe u

namespace Specs.D07.Ch11.ShiftIrreducibility

open Polynomial

/-- Both orders of substitution by the affine expression and its inverse. -/
def InverseSubstitutions : Prop :=
  ∀ (R : Type u) [CommRing R] (u : Rˣ) (a : R) (f : R[X]),
    (f.comp (C (u : R) * X + C a)).comp
        (C (↑(u⁻¹) : R) * (X - C a)) = f ∧
    (f.comp (C (↑(u⁻¹) : R) * (X - C a))).comp
        (C (u : R) * X + C a) = f

/-- The automorphism has the specified action on all polynomials, its inverse,
constants and the indeterminate. -/
def AffineAutomorphism : Prop :=
  ∀ (R : Type u) [CommRing R] (u : Rˣ) (a : R),
    ∃ e : R[X] ≃+* R[X],
      (∀ f, e f = f.comp (C (u : R) * X + C a)) ∧
      (∀ f, e.symm f = f.comp (C (↑(u⁻¹) : R) * (X - C a))) ∧
      (∀ r, e (C r) = C r) ∧ e X = C (u : R) * X + C a

/-- Units and every factorization are preserved and reflected. -/
def UnitsAndFactorizations : Prop :=
  ∀ (R : Type u) [CommRing R] (u : Rˣ) (a : R),
    (∀ f : R[X], IsUnit (f.comp (C (u : R) * X + C a)) ↔ IsUnit f) ∧
    (∀ f g h : R[X], f = g * h ↔
      f.comp (C (u : R) * X + C a) =
        g.comp (C (u : R) * X + C a) * h.comp (C (u : R) * X + C a))

def AffineIrreducibility : Prop :=
  ∀ (R : Type u) [CommRing R] (u : Rˣ) (a : R) (f : R[X]),
    Irreducible (f.comp (C (u : R) * X + C a)) ↔ Irreducible f

def ShiftPreservesIrreducibility : Prop :=
  ∀ (R : Type u) [CommRing R] (a : R) (f : R[X]),
    Irreducible (f.comp (X + C a)) ↔ Irreducible f

/-- The displayed expansion is an identity over any commutative ring. -/
def ShiftedQuarticExpansion : Prop :=
  ∀ (R : Type u) [CommRing R],
    (X + 1 : R[X]) ^ 4 + 1 = X ^ 4 + 4 * X ^ 3 + 6 * X ^ 2 + 4 * X + 2

/-- The example satisfies the integer Eisenstein hypotheses at 2. -/
def ShiftedQuarticEisenstein : Prop :=
  let f : ℤ[X] := (X + 1) ^ 4 + 1
  f.Monic ∧ f.natDegree = 4 ∧ ¬(2 : ℤ) ∣ f.leadingCoeff ∧
    (∀ i : ℕ, i < f.natDegree → (2 : ℤ) ∣ f.coeff i) ∧
    ¬(2 : ℤ) ^ 2 ∣ f.coeff 0

def ShiftedQuarticIrreducible : Prop :=
  Irreducible ((X + 1 : ℚ[X]) ^ 4 + 1)

def QuarticIrreducible : Prop :=
  Irreducible ((X : ℚ[X]) ^ 4 + 1)

end Specs.D07.Ch11.ShiftIrreducibility
