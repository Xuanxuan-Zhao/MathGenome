import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.RingTheory.Idempotents

/-!
Independent statements for the uniqueness and simple-ring assertions of
paper.tex, Theorem 3.4, lines 708–750. Rings and equivalences are unital;
division rings are not assumed commutative. Positive sizes exclude zero
matrix rings. The finite index sets can be empty, so the uniqueness
statements also include the zero-ring boundary.

The assumptions of the uniqueness assertions are actual ring isomorphisms
between decompositions, with no chosen identification of their centers or
simple modules. In particular no uniqueness certificate is assumed.
-/

universe u v w

namespace P103.Specs.Ch03.WedderburnUniqueness

/-- The two invariants of an individual full matrix ring. -/
def matrix_parametersType : Prop :=
  ∀ (D : Type u) (E : Type v) [DivisionRing D] [DivisionRing E]
    (n m : ℕ), 0 < n → 0 < m →
    Nonempty (Matrix (Fin n) (Fin n) D ≃+* Matrix (Fin m) (Fin m) E) →
    n = m ∧ Nonempty (D ≃+* E)

/-- The actual simple factors, before recovering their parameters. -/
def factor_permutationType : Prop :=
  ∀ (k l : ℕ) (D : Fin k → Type u) (E : Fin l → Type v)
    (n : Fin k → ℕ) (m : Fin l → ℕ)
    [∀ i, DivisionRing (D i)] [∀ j, DivisionRing (E j)],
    (∀ i, 0 < n i) → (∀ j, 0 < m j) →
    Nonempty ((Π i, Matrix (Fin (n i)) (Fin (n i)) (D i)) ≃+*
      (Π j, Matrix (Fin (m j)) (Fin (m j)) (E j))) →
    ∃ p : Fin k ≃ Fin l, ∀ i,
      Nonempty (Matrix (Fin (n i)) (Fin (n i)) (D i) ≃+*
        Matrix (Fin (m (p i))) (Fin (m (p i))) (E (p i)))

/-- Full uniqueness, for two representations of the same ring.
The permutation matches factors by actual ring equivalences and matches
both the positive sizes and the division rings. -/
def uniquenessType : Prop :=
  ∀ (R : Type w) [Ring R] (k l : ℕ)
    (D : Fin k → Type u) (E : Fin l → Type v)
    (n : Fin k → ℕ) (m : Fin l → ℕ)
    [∀ i, DivisionRing (D i)] [∀ j, DivisionRing (E j)],
    (∀ i, 0 < n i) → (∀ j, 0 < m j) →
    Nonempty (R ≃+* Π i, Matrix (Fin (n i)) (Fin (n i)) (D i)) →
    Nonempty (R ≃+* Π j, Matrix (Fin (m j)) (Fin (m j)) (E j)) →
    ∃ p : Fin k ≃ Fin l, ∀ i,
      Nonempty (Matrix (Fin (n i)) (Fin (n i)) (D i) ≃+*
        Matrix (Fin (m (p i))) (Fin (m (p i))) (E (p i))) ∧
      n i = m (p i) ∧ Nonempty (D i ≃+* E (p i))

/-- Every matrix decomposition of a simple ring has exactly one factor. -/
def simple_factor_countType : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R]
    (k : ℕ) (D : Fin k → Type v) (n : Fin k → ℕ)
    [∀ i, DivisionRing (D i)],
    (∀ i, 0 < n i) →
    Nonempty (R ≃+* Π i, Matrix (Fin (n i)) (Fin (n i)) (D i)) → k = 1

/-- Existence in the simple Artinian case, with no commutativity assumption. -/
def simple_artinianType : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsArtinianRing R],
    ∃ (n : ℕ) (D : Type u) (_ : DivisionRing D),
      0 < n ∧ Nonempty (R ≃+* Matrix (Fin n) (Fin n) D)

/-- Useful intrinsic characterization used to recover the factors. -/
def central_idempotentType : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] (z : R),
    z ∈ Subring.center R → IsIdempotentElem z → z = 0 ∨ z = 1

end P103.Specs.Ch03.WedderburnUniqueness
