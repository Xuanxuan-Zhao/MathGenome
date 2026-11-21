import MathGenome.Internal.Specs.D05.M05.Adjugate.RankMinors
import MathGenome.Internal.Specs.D05.M08.Minpoly
import Mathlib.FieldTheory.Separable

/-! Independent statements for the scalar-extension paragraph of K05.10.semisimple
(paper.tex:1577). Extension is the entrywise coefficient map for finite matrices.
No separability or characteristic restriction is imposed on matrix extension.
Characteristic zero is imposed only on the irreducible-polynomial statements.
Empty shapes and the zero-dimensional minimal polynomial are included. -/

namespace Specs.D05.M10.Semisimple.ScalarExtension

/-- Rank is preserved by any field extension, by the rank–minor criterion. -/
def rank_preserved : Prop :=
  ∀ {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    (A.map (algebraMap K L)).rank = A.rank

/-- Finite coordinate columns preserve independence over the extended field. -/
def columns_independent_extension : Prop :=
  ∀ {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    LinearIndependent L (A.map (algebraMap K L)).col ↔ LinearIndependent K A.col

/-- This includes the flattened finite list of the first d matrix powers. -/
def powers_independent_extension : Prop :=
  ∀ {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (d : ℕ),
    LinearIndependent L (fun i : Fin d => (A.map (algebraMap K L)) ^ i.val) ↔
      LinearIndependent K (fun i : Fin d => A ^ i.val)

/-- Equality of the full monic polynomial, not just its degree. -/
def minpoly_scalar_extension : Prop :=
  ∀ {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    minpoly L (A.map (algebraMap K L)) = (minpoly K A).map (algebraMap K L)

/-- The original and extended empty matrix both have minimal polynomial one. -/
def empty_minpoly : Prop :=
  ∀ {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : Matrix (Fin 0) (Fin 0) K),
    minpoly K A = 1 ∧ minpoly L (A.map (algebraMap K L)) = 1

/-- In characteristic zero the irreducible derivative is nonzero, has smaller
 degree, and is relatively prime to the original polynomial. -/
def irreducible_derivative : Prop :=
  ∀ {K : Type*} [Field K] [CharZero K] (p : Polynomial K), Irreducible p →
    p.derivative ≠ 0 ∧ p.derivative.natDegree < p.natDegree ∧
      IsCoprime p p.derivative

/-- The Bézout identity remains valid over every extension. -/
def irreducible_extension_separable : Prop :=
  ∀ {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K]
    (p : Polynomial K), Irreducible p →
    IsCoprime (p.map (algebraMap K L)) (p.map (algebraMap K L)).derivative

/-- Roots in any extension are simple; splitting of the polynomial is unnecessary. -/
def irreducible_extension_roots : Prop :=
  ∀ {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K]
    (p : Polynomial K), Irreducible p →
    (p.map (algebraMap K L)).roots.Nodup ∧
      ∀ a : L, (p.map (algebraMap K L)).IsRoot a →
        (p.map (algebraMap K L)).derivative.eval a ≠ 0

end Specs.D05.M10.Semisimple.ScalarExtension
