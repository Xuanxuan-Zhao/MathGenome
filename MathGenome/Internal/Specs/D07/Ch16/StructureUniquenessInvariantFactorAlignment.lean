import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! The exponent-alignment part of paper.tex:3305–3327.
A finite product of modules is used for a finite direct sum. Prime
representatives need not be normalized, and unused representatives are allowed.
The elementary-divisor predicate records multiplicities at the representatives
and rules out all other prime classes. It does not assume any conclusion about
invariant factors or a module classification. -/

universe u
namespace Specs.D07.Ch16.StructureUniquenessInvariantFactorAlignment
open scoped BigOperators

noncomputable def width {R : Type u} (s : Finset R) (E : R → Multiset ℕ) : ℕ :=
  s.sup fun p => (E p).card

def padded (n : ℕ) (A : Multiset ℕ) : List ℕ :=
  List.replicate (n - A.card) 0 ++ A.sort (· ≤ ·)

noncomputable def exponent {R : Type u} (s : Finset R) (E : R → Multiset ℕ)
    (p : R) (i : Fin (width s E)) : ℕ :=
  (padded (width s E) (E p)).getD i.val 0

noncomputable def column {R : Type u} [CommRing R]
    (s : Finset R) (E : R → Multiset ℕ) (i : Fin (width s E)) : R :=
  ∏ p ∈ s, p ^ exponent s E p i

noncomputable def positiveMultiplicities {R : Type u} [CommRing R]
    (p : R) {n : ℕ} (d : Fin n → R) : Multiset ℕ :=
  ((List.ofFn fun i => multiplicity p (d i)).filter (· != 0) : List ℕ)

def PrimeData {R : Type u} [CommRing R] (s : Finset R) : Prop :=
  (∀ p ∈ s, Prime p) ∧ (s : Set R).Pairwise (fun p q => ¬Associated p q)

def PositiveData {R : Type u} (s : Finset R) (E : R → Multiset ℕ) : Prop :=
  ∀ p ∈ s, ∀ e ∈ E p, 0 < e

def HasElementaryDivisors {R : Type u} [CommRing R]
    (s : Finset R) (E : R → Multiset ℕ) {n : ℕ} (d : Fin n → R) : Prop :=
  (∀ p ∈ s, positiveMultiplicities p d = E p) ∧
  (∀ q : R, Prime q → (∀ p ∈ s, ¬Associated q p) →
    ∀ i, multiplicity q (d i) = 0)

abbrev Cyclic (R : Type u) [CommRing R] (a : R) := R ⧸ Ideal.span {a}

/-- Sorting and padding gives exactly the prescribed nonzero exponent multiset. -/
def ExponentAlignment : Prop :=
  ∀ (R : Type u) (s : Finset R) (E : R → Multiset ℕ), PositiveData s E →
    ∀ p ∈ s,
      Monotone (exponent s E p) ∧
      (((List.ofFn (exponent s E p)).filter (· != 0) : List ℕ) : Multiset ℕ) = E p

/-- Column products are nonzero nonunits in divisibility order, and have
exactly the input elementary divisors (including absence of other primes). -/
def ColumnProperties : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (s : Finset R) (E : R → Multiset ℕ), PrimeData s → PositiveData s E →
      (∀ i, column s E i ≠ 0 ∧ ¬IsUnit (column s E i)) ∧
      (∀ i j, i ≤ j → column s E i ∣ column s E j) ∧
      HasElementaryDivisors s E (column s E)

/-- The actual finite torsion modules, with zero-exponent quotients deleted,
are linearly isomorphic. The lists on the right are the sorted input multisets. -/
def Reconstruction : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (s : Finset R) (E : R → Multiset ℕ), PrimeData s → PositiveData s E →
      Nonempty (((i : Fin (width s E)) → Cyclic R (column s E i)) ≃ₗ[R]
        ((p : s) → (j : Fin (E p).card) →
          Cyclic R ((p : R) ^ ((E p).sort (· ≤ ·)).getD j.val 0)))

/-- Every nonzero nonunit divisibility-chain list with the given elementary
divisors has the constructed length and is associated column by column.
No factorization or alignment certificate for the candidate list is assumed. -/
def ChainUniqueness : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (s : Finset R) (E : R → Multiset ℕ), PrimeData s → PositiveData s E →
      ∀ (n : ℕ) (d : Fin n → R),
        (∀ i, d i ≠ 0 ∧ ¬IsUnit (d i)) →
        (∀ i j, i ≤ j → d i ∣ d j) → HasElementaryDivisors s E d →
        ∃ h : n = width s E, ∀ i, Associated (d i) (column s E (Fin.cast h i))

/-- Empty input produces the empty invariant-factor list, in both directions. -/
def EmptyCase : Prop :=
  ∀ (R : Type u) (s : Finset R) (E : R → Multiset ℕ),
    width s E = 0 ↔ ∀ p ∈ s, E p = 0

end Specs.D07.Ch16.StructureUniquenessInvariantFactorAlignment
