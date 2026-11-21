import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Recurrence.InitialValues
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Initial data for a linear recurrence

Source: `paper.tex`, Proposition p204:W13 (Chapter 2).
Coefficients are indexed in increasing order: c_j multiplies a_(n+j).
The definitions also allow order zero; the source theorem is stated for r ≥ 1.
-/

noncomputable section

open scoped BigOperators

universe u

namespace FiniteCombinatorics.Recurrence

/-- The recurrence of order r with coefficients c, with no restriction on c₀. -/
def recurrence {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) : LinearRecurrence R :=
  ⟨r, c⟩

/-- The equation a_(n+r) = ∑_{j<r} c_j a_(n+j) for every n ≥ 0. -/
def IsSolution {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (a : ℕ → R) : Prop :=
  (recurrence c).IsSolution a

/-- The R-module of all solutions of the recurrence. -/
def solutionSpace {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) : Submodule R (ℕ → R) :=
  (recurrence c).solSpace

/-- The canonical characteristic polynomial; its explicit formula is proved below. -/
def characteristicPolynomial {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) : Polynomial R :=
  (recurrence c).charPoly

/-- The sequence constructed recursively from the prescribed r initial entries. -/
def sequence {R : Type u} [CommRing R] {r : ℕ} (c init : Fin r → R) : ℕ → R :=
  (recurrence c).mkSol init

/-- Restriction to the first r entries, as a linear equivalence. -/
def initialValuesEquiv {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) : solutionSpace c ≃ₗ[R] (Fin r → R) :=
  (recurrence c).toInit

/-- The constructed sequence has the prescribed initial entries. -/
theorem sequence_initial {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (init : Fin r → R) (i : Fin r) :
    sequence c init i = init i := (recurrence c).mkSol_eq_init init i

/-- The constructed sequence satisfies the recurrence at every n ≥ 0. -/
theorem sequence_recurrence {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (init : Fin r → R) (n : ℕ) :
    sequence c init (n + r) = ∑ j : Fin r, c j * sequence c init (n + j) := (recurrence c).is_sol_mkSol init n

/-- Proposition p204:W13: for r ≥ 1 there exists exactly one sequence with these initial values and recurrence. -/
theorem existsUnique_solution {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (_hr : 1 ≤ r) (init : Fin r → R) :
    ∃! a : ℕ → R,
      (∀ i : Fin r, a i = init i) ∧
      (∀ n : ℕ, a (n + r) = ∑ j : Fin r, c j * a (n + j)) := by
  refine ⟨sequence c init, ⟨sequence_initial c init, sequence_recurrence c init⟩, ?_⟩
  intro a ha
  exact (recurrence c).eq_mk_of_is_sol_of_eq_init' ha.2 ha.1

/-- Membership in the solution module is precisely the recurrence predicate. -/
theorem mem_solutionSpace_iff {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (a : ℕ → R) :
    a ∈ solutionSpace c ↔ IsSolution c a := Iff.rfl

/-- The characteristic polynomial is χ(t) = t^r − ∑_{j<r} c_j t^j. -/
theorem characteristicPolynomial_eq {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) :
    characteristicPolynomial c =
      Polynomial.X ^ r - ∑ j : Fin r, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) := by
  simp only [characteristicPolynomial, LinearRecurrence.charPoly, recurrence,
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.monomial_one_right_eq_X_pow]
  rfl

/-- The forward equivalence sends a solution to its first r entries. -/
theorem initialValuesEquiv_apply {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (a : solutionSpace c) (i : Fin r) :
    initialValuesEquiv c a i = (a : ℕ → R) i := rfl

/-- The inverse equivalence constructs the unique sequence from its initial values. -/
theorem initialValuesEquiv_symm_apply {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (init : Fin r → R) (n : ℕ) :
    ((initialValuesEquiv c).symm init : ℕ → R) n = sequence c init n := rfl

/-- The solution module has a finite basis of r elements. -/
instance solutionSpace_finite {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) :
    Module.Finite R (solutionSpace c) := Module.Finite.of_basis (recurrence c).basis

/-- Over any field, the solution space has dimension r (cardinal dimension). -/
theorem solutionSpace_rank {K : Type u} [Field K] {r : ℕ} (c : Fin r → K) :
    Module.rank K (solutionSpace c) = (r : Cardinal) := (recurrence c).solSpace_rank

/-- Over any field, the finite dimension of the solution space is r. -/
theorem solutionSpace_finrank {K : Type u} [Field K] {r : ℕ} (c : Fin r → K) :
    Module.finrank K (solutionSpace c) = r := Module.finrank_eq_of_rank_eq (solutionSpace_rank c)

end FiniteCombinatorics.Recurrence
