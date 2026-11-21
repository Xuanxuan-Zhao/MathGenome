import Mathlib.Algebra.LinearRecurrence

/-!
# Initial data for a linear recurrence

Source: `paper.tex`, Proposition p204:W13 (Chapter 2).
Coefficients are indexed in increasing order: c_j multiplies a_(n+j).
The definitions also allow order zero; the source theorem is stated for r ≥ 1.
-/

noncomputable section

open scoped BigOperators

universe u

namespace Specs.FiniteCombinatorics.Recurrence

/-- Expected type of `FiniteCombinatorics.Recurrence.recurrence`. -/
def recurrenceType : Type (u + 1) :=
  ∀ {R : Type u} [CommRing R] {r : ℕ}, (Fin r → R) → LinearRecurrence R

/-- The recurrence of order r with coefficients c, with no restriction on c₀. -/
def recurrenceValue : recurrenceType :=
  fun {_} [_] {r} c => ⟨r, c⟩

/-- Expected type of `FiniteCombinatorics.Recurrence.IsSolution`. -/
def IsSolutionType : Type (u + 1) :=
  ∀ {R : Type u} [CommRing R] {r : ℕ}, (Fin r → R) → (ℕ → R) → Prop

/-- The equation a_(n+r) = ∑_{j<r} c_j a_(n+j) for every n ≥ 0. -/
def IsSolutionValue : IsSolutionType :=
  fun {_} [_] {r} c a => ∀ n, a (n + r) = ∑ j : Fin r, c j * a (n + j)

/-- Expected type of `FiniteCombinatorics.Recurrence.solutionSpace`. -/
def solutionSpaceType : Type (u + 1) :=
  ∀ {R : Type u} [CommRing R] {r : ℕ}, (Fin r → R) → Submodule R (ℕ → R)

/-- The R-module of all solutions of the recurrence. -/
def solutionSpaceValue : solutionSpaceType :=
  fun {_} [_] {_} c => (recurrenceValue c).solSpace

/-- Expected type of `FiniteCombinatorics.Recurrence.characteristicPolynomial`. -/
def characteristicPolynomialType : Type (u + 1) :=
  ∀ {R : Type u} [CommRing R] {r : ℕ}, (Fin r → R) → Polynomial R

/-- The canonical characteristic polynomial; its explicit formula is proved below. -/
def characteristicPolynomialValue : characteristicPolynomialType :=
  fun {_} [_] {_} c => (recurrenceValue c).charPoly

/-- Expected type of `FiniteCombinatorics.Recurrence.sequence`. -/
def sequenceType : Type (u + 1) :=
  ∀ {R : Type u} [CommRing R] {r : ℕ}, (Fin r → R) → (Fin r → R) → (ℕ → R)

/-- The sequence constructed recursively from the prescribed r initial entries. -/
def sequenceValue : sequenceType :=
  fun {_} [_] {_} c init => (recurrenceValue c).mkSol init

/-- Expected type of `FiniteCombinatorics.Recurrence.initialValuesEquiv`. -/
def initialValuesEquivType : Type (u + 1) :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R),
    solutionSpaceValue c ≃ₗ[R] (Fin r → R)

/-- Restriction to the first r entries, as a linear equivalence. -/
def initialValuesEquivValue : initialValuesEquivType :=
  fun {_} [_] {_} c => (recurrenceValue c).toInit

/-- The constructed sequence has the prescribed initial entries. -/
def sequence_initialType : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (init : Fin r → R) (i : Fin r),
    sequenceValue c init i = init i

/-- The constructed sequence satisfies the recurrence at every n ≥ 0. -/
def sequence_recurrenceType : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (init : Fin r → R) (n : ℕ),
    sequenceValue c init (n + r) = ∑ j : Fin r, c j * sequenceValue c init (n + j)

/-- Proposition p204:W13: for r ≥ 1 there exists exactly one sequence with these initial values and recurrence. -/
def existsUnique_solutionType : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (_hr : 1 ≤ r) (init : Fin r → R),
    ∃! a : ℕ → R,
      (∀ i : Fin r, a i = init i) ∧
      (∀ n : ℕ, a (n + r) = ∑ j : Fin r, c j * a (n + j))

/-- Membership in the solution module is precisely the recurrence predicate. -/
def mem_solutionSpace_iffType : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (a : ℕ → R),
    a ∈ solutionSpaceValue c ↔ IsSolutionValue c a

/-- The characteristic polynomial is χ(t) = t^r − ∑_{j<r} c_j t^j. -/
def characteristicPolynomial_eqType : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R),
    characteristicPolynomialValue c =
      Polynomial.X ^ r - ∑ j : Fin r, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)

/-- The forward equivalence sends a solution to its first r entries. -/
def initialValuesEquiv_applyType : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (a : solutionSpaceValue c) (i : Fin r),
    initialValuesEquivValue c a i = (a : ℕ → R) i

/-- The inverse equivalence constructs the unique sequence from its initial values. -/
def initialValuesEquiv_symm_applyType : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (init : Fin r → R) (n : ℕ),
    ((initialValuesEquivValue c).symm init : ℕ → R) n = sequenceValue c init n

/-- The solution module has a finite basis of r elements. -/
def solutionSpace_finiteType : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R),
    Module.Finite R (solutionSpaceValue c)

/-- Over any field, the solution space has dimension r (cardinal dimension). -/
def solutionSpace_rankType : Prop :=
  ∀ {K : Type u} [Field K] {r : ℕ} (c : Fin r → K),
    Module.rank K (solutionSpaceValue c) = (r : Cardinal)

/-- Over any field, the finite dimension of the solution space is r. -/
def solutionSpace_finrankType : Prop :=
  ∀ {K : Type u} [Field K] {r : ℕ} (c : Fin r → K),
    Module.finrank K (solutionSpaceValue c) = r

end Specs.FiniteCombinatorics.Recurrence
