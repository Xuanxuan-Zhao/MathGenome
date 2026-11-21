import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Polynomial.Basic

/-! Independent statements for K07.16.structure_existence, paper.tex:3208–3270.
The finite direct sums include the empty sum. The free rank is shared by both
forms. Repeated elementary divisors are allowed; associated prime bases use
one representative, expressed by the `Associated → Eq` condition. -/

universe u v
namespace Specs.D07.Ch16.StructureExistence
open scoped DirectSum

/-- Both existence statements, with nonzero nonunit ordered invariant factors,
positive elementary exponents, and the torsion criterion for the free rank. -/
def Decompositions : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    ∃ (r s t : ℕ) (d : Fin s → R) (p : Fin t → R) (e : Fin t → ℕ),
      (∀ i, d i ≠ 0 ∧ ¬ IsUnit (d i)) ∧
      (∀ i j, i ≤ j → d i ∣ d j) ∧
      (∀ i, Prime (p i) ∧ 0 < e i) ∧
      (∀ i j, Associated (p i) (p j) → p i = p j) ∧
      Nonempty (M ≃ₗ[R] ((Fin r → R) × (⨁ i : Fin s, R ⧸ Ideal.span {d i}))) ∧
      Nonempty (M ≃ₗ[R] ((Fin r → R) × (⨁ i : Fin t, R ⧸ Ideal.span {p i ^ e i}))) ∧
      (r = 0 ↔ Module.IsTorsion R M)

/-- The free rank in any such decomposition vanishes exactly for torsion
modules, independently of the chosen isomorphism or invariant-factor chain. -/
def FreeRankCriterion : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (r s : ℕ) (d : Fin s → R), (∀ i, d i ≠ 0) →
    Nonempty (M ≃ₗ[R] ((Fin r → R) × (⨁ i : Fin s, R ⧸ Ideal.span {d i}))) →
    (r = 0 ↔ Module.IsTorsion R M)

/-- Finite generation and the PID assumptions apply to both directions here. -/
def FreeIffTorsionFree : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    Module.Free R M ↔ Module.IsTorsionFree R M

/-- Rational numbers, with the usual integer scalar action, are torsion-free
but admit no integer basis, even an infinite one. -/
def RationalCounterexample : Prop :=
  Module.IsTorsionFree ℤ ℚ ∧ ¬ Module.Free ℤ ℚ ∧ ¬ Module.Finite ℤ ℚ

/-- A free ideal in a commutative domain is principal. No finite generation
hypothesis is imposed on the ideal or its putative basis. -/
def FreeIdealPrincipal : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (I : Ideal R),
    Module.Free R I → ∃ a : R, I = Ideal.span {a}

/-- The specific ideal from Chapter 10 violates submodule freeness outside PIDs. -/
def NonprincipalIdealCounterexample : Prop :=
  ¬ Module.Free (Polynomial ℤ) (Ideal.span ({(2 : Polynomial ℤ), Polynomial.X} :
    Set (Polynomial ℤ)))

/-- The free summand cannot be omitted: the integer module cannot be a finite
direct sum of nonzero-annihilator cyclic quotients (in particular prime powers). -/
def IntegerNeedsFreePart : Prop :=
  ¬ Module.IsTorsion ℤ ℤ ∧
  ∀ (s : ℕ) (d : Fin s → ℤ), (∀ i, d i ≠ 0) →
    ¬ Nonempty (ℤ ≃ₗ[ℤ] (⨁ i : Fin s, ℤ ⧸ Ideal.span {d i}))

end Specs.D07.Ch16.StructureExistence
