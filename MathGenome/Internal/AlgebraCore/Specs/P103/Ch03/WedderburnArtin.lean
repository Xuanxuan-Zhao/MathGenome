import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.JacobsonRadical
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.Artinian.Defs

/-!
Independent statements for the classification equivalence in paper.tex,
Theorem 3.4, lines 708–750, under the conventions at line 47.
Uniqueness of factors and the simple-ring specialization belong to the
separately allocated `c03_wedderburn_unique` goal.

`IsSemisimpleModule R R` uses the LEFT regular action. `IsArtinianRing R`
is the descending chain condition on left ideals, and `radical` is the
intersection of maximal left ideals from the upstream interface.
Division rings here need not be commutative. Products are finite dependent
products, matrix sizes are strictly positive, and the empty product is
permitted precisely to account for the zero ring. The classification below
also holds for the zero ring; `nonempty_factorsType` explicitly rules out
an empty family when the original ring is nonzero.
-/

universe u

namespace P103.Specs.Ch03.WedderburnArtin

open P103.Specs.Ch03.JacobsonRadical (radical)

/-- A finite product of positive-size full matrix rings over division rings. -/
def MatrixDecomposition (R : Type u) [Ring R] : Prop :=
  ∃ (k : ℕ) (D : Fin k → Type u) (n : Fin k → ℕ) (_ : ∀ i, DivisionRing (D i)),
    (∀ i, 0 < n i) ∧
    Nonempty (R ≃+* Π i, Matrix (Fin (n i)) (Fin (n i)) (D i))

/-- All three conditions are equivalent, including at the zero-ring boundary. -/
def classificationType : Prop :=
  ∀ (R : Type u) [Ring R],
    (IsSemisimpleModule R R ↔ IsArtinianRing R ∧ radical R = ⊥) ∧
    (IsSemisimpleModule R R ↔ MatrixDecomposition R)

/-- Any such representation of a nonzero ring has at least one factor. -/
def nonempty_factorsType : Prop :=
  ∀ (R : Type u) [Ring R] [Nontrivial R]
    (k : ℕ) (D : Fin k → Type u) (n : Fin k → ℕ) [∀ i, DivisionRing (D i)],
    Nonempty (R ≃+* Π i, Matrix (Fin (n i)) (Fin (n i)) (D i)) → 0 < k

/-- The simple left ideals give the OPPOSITE endomorphism division rings. -/
def opposite_decompositionType : Prop :=
  ∀ (R : Type u) [Ring R] [IsSemisimpleModule R R],
    ∃ (k : ℕ) (S : Fin k → Ideal R) (n : Fin k → ℕ),
      (∀ i, IsSimpleModule R (S i)) ∧ (∀ i, 0 < n i) ∧
      Nonempty (R ≃+* Π i,
        Matrix (Fin (n i)) (Fin (n i)) (Module.End R (S i))ᵐᵒᵖ)

/-- Right multiplication identifies the regular endomorphism ring with Rᵐᵒᵖ. -/
def regular_endomorphismsType : Prop :=
  ∀ (R : Type u) [Ring R],
    ∃ e : Rᵐᵒᵖ ≃+* Module.End R R,
      ∀ r x : R, e (MulOpposite.op r) x = x * r

/-- Transpose is essential to the opposite-matrix identification. -/
def transpose_oppositeType : Prop :=
  ∀ (D : Type u) [DivisionRing D] (n : ℕ),
    ∃ e : (Matrix (Fin n) (Fin n) D)ᵐᵒᵖ ≃+*
        Matrix (Fin n) (Fin n) Dᵐᵒᵖ,
      ∀ (A : Matrix (Fin n) (Fin n) D) (i j : Fin n),
        e (MulOpposite.op A) i j = MulOpposite.op (A j i)

/-- Matrix regular modules are semisimple even over noncommutative division rings. -/
def matrix_regular_semisimpleType : Prop :=
  ∀ (D : Type u) [DivisionRing D] (n : ℕ),
    IsSemisimpleModule (Matrix (Fin n) (Fin n) D) (Matrix (Fin n) (Fin n) D)

/-- Finite products of matrix rings have semisimple left regular modules. -/
def product_regular_semisimpleType : Prop :=
  ∀ (k : ℕ) (D : Fin k → Type u) (n : Fin k → ℕ) [∀ i, DivisionRing (D i)],
    IsSemisimpleModule (Π i, Matrix (Fin (n i)) (Fin (n i)) (D i))
      (Π i, Matrix (Fin (n i)) (Fin (n i)) (D i))

/-- A zero ring satisfies the conditions and is explicitly the empty product. -/
def zero_ringType : Prop :=
  ∀ (R : Type u) [Ring R] [Subsingleton R],
    IsSemisimpleModule R R ∧ (IsArtinianRing R ∧ radical R = ⊥) ∧
    ∃ (D : Fin 0 → Type u) (_ : ∀ i, DivisionRing (D i)),
      Nonempty (R ≃+* Π i : Fin 0, Matrix (Fin 1) (Fin 1) (D i))

end P103.Specs.Ch03.WedderburnArtin
