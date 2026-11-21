import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Rat.Cast.Order

/-! Independent statements for the polynomial-existence stage of Theorem 7.6,
paper.tex 1247–1255. No dimension assertion is presupposed. In particular Q=0
and modules with nonzero annihilator are retained. -/
namespace P103.HilbertSamuelPolynomial
noncomputable section

variable {R : Type*} [CommRing R] (Q : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- The actual submodule Q^n M. -/
def powerSubmodule (n : ℕ) : Submodule R M := Q ^ n • (⊤ : Submodule R M)

/-- Q^(n+1) M, regarded as a submodule of Q^n M. -/
def successorSubmodule (n : ℕ) : Submodule R (powerSubmodule Q M n) :=
  (powerSubmodule Q M (n + 1)).comap (powerSubmodule Q M n).subtype

abbrev Layer (n : ℕ) := powerSubmodule Q M n ⧸ successorSubmodule Q M n
abbrev Quotient (n : ℕ) := M ⧸ powerSubmodule Q M (n + 1)

noncomputable def layerLength (n : ℕ) : ℕ := (Module.length R (Layer Q M n)).toNat
noncomputable def quotientLength (n : ℕ) : ℕ := (Module.length R (Quotient Q M n)).toNat

/-- Eventual polynomial agreement on the original natural-number indices. -/
def EventuallyPolynomial (f : ℕ → ℕ) (p : Polynomial ℚ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, (f n : ℚ) = p.eval (n : ℚ)

end
end P103.HilbertSamuelPolynomial

namespace Specs.P103.HilbertSamuelPolynomial
open _root_.P103.HilbertSamuelPolynomial

/-- Finiteness is asserted separately from the `toNat` length definitions. -/
def finiteLengthsType : Prop :=
  ∀ (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R), Q ≤ IsLocalRing.maximalIdeal R →
    IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))) →
    ∀ n : ℕ, IsFiniteLength R (Layer Q M n) ∧ IsFiniteLength R (Quotient Q M n)

def sumLayersType : Prop :=
  ∀ (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R), Q ≤ IsLocalRing.maximalIdeal R →
    IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))) →
    ∀ n : ℕ, quotientLength Q M n = ∑ j ∈ Finset.range (n + 1), layerLength Q M j

def layerPolynomialType : Prop :=
  ∀ (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R), Q ≤ IsLocalRing.maximalIdeal R →
    IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))) →
    ∃ p : Polynomial ℚ, EventuallyPolynomial (layerLength Q M) p

/-- The polynomial is nonzero even when it is constant. -/
def quotientPolynomialType : Prop :=
  ∀ (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R), Q ≤ IsLocalRing.maximalIdeal R →
    IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))) →
    ∃ p : Polynomial ℚ, EventuallyPolynomial (quotientLength Q M) p ∧ p ≠ 0 ∧
      (0 < p.natDegree → 0 < p.leadingCoeff)

/-- The surjective scalar map identifies the entire submodule lattices.
This applies to R/Ann(M) on M and to each subquotient of M. -/
def scalarLengthsType : Prop :=
  ∀ (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N],
    Function.Surjective (algebraMap R S) →
    Module.length R N = Module.length S N ∧
      (IsFiniteLength R N ↔ IsFiniteLength S N)

universe u v

/-- Complete result at this stage; no equality with dimension is included. -/
def polynomialExistenceType : Prop :=
  finiteLengthsType.{u,v} ∧ sumLayersType.{u,v} ∧ layerPolynomialType.{u,v} ∧
    quotientPolynomialType.{u,v} ∧ scalarLengthsType.{u,u,v}

end Specs.P103.HilbertSamuelPolynomial
