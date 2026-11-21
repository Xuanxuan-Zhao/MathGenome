import MathGenome.Internal.Specs.D05.M05.DetDefinition
import MathGenome.Internal.Specs.D05.M04.MatrixOfMap
import MathGenome.Internal.Specs.D05.M02.Examples
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
Independent specifications for K05.05.vandermonde, paper.tex:923–932.
Indices start at zero in `Fin n`, so column `j` has exponent `j.val`.
The determinant is the shared paper determinant, and `Ioi i` selects exactly
the pairs `i < j`, with factor `b j - b i`.

The determinant identity is stated over every commutative ring, a strengthening
of the real/complex assertion. Evaluation is stated over every field, on formal
polynomials of degree strictly less than `n`. `WithBot` degree includes the zero
polynomial even when `n = 0`; no positive-size or infinite-field assumption is
made. The isomorphism is required to be the actual evaluation map.
-/

noncomputable section

namespace Specs.D05.M05.Vandermonde

open scoped BigOperators

def evaluationMap_type :=
  ∀ {R : Type*} [CommRing R] {n : ℕ}, (Fin n → R) →
    (Polynomial.degreeLT R n →ₗ[R] (Fin n → R))

/-- Evaluation of formal polynomials at the indexed nodes. -/
def evaluationMap_value : evaluationMap_type := fun b =>
  { toFun := fun p i => (p : Polynomial _).eval (b i)
    map_add' := by intros; funext i; simp
    map_smul' := by intros; funext i; simp }

def degree_bound : Prop :=
  ∀ (R : Type*) [CommRing R] (n : ℕ) (p : Polynomial R),
    (p ∈ Polynomial.degreeLT R n ↔ p.degree < (n : WithBot ℕ)) ∧
      (0 : Polynomial R) ∈ Polynomial.degreeLT R n

/-- At size zero the polynomial domain consists exactly of zero. -/
def empty_domain : Prop :=
  ∀ (R : Type*) [CommRing R] (p : Polynomial.degreeLT R 0),
    (p : Polynomial R) = 0

def determinant_formula : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (b : Fin n → R),
    _root_.D05.M05.determinant (Matrix.of fun (i j : Fin n) => b i ^ (j : ℕ)) =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (b j - b i)

/-- Both base sizes give one, without conditions on their nodes. -/
def small_determinants : Prop :=
  ∀ (R : Type*) [CommRing R],
    (∀ b : Fin 0 → R,
      _root_.D05.M05.determinant (Matrix.of fun (i j : Fin 0) => b i ^ (j : ℕ)) = 1) ∧
    (∀ b : Fin 1 → R,
      _root_.D05.M05.determinant (Matrix.of fun (i j : Fin 1) => b i ^ (j : ℕ)) = 1)

/-- The monomial basis and the shared coordinate basis give precisely the
paper's matrix, with nodes indexing rows. -/
def evaluation_matrix : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (b : Fin n → R),
    Specs.D05.M04.MatrixOfMap.matrixOfMap_value
      (Polynomial.degreeLT.basis R n)
      (_root_.D05.Specs.FormalPolynomials.coordinateBasisValue R n)
      (evaluationMap_value b) = Matrix.of fun (i j : Fin n) => b i ^ (j : ℕ)

def evaluation_coordinates : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (b : Fin n → R)
    (p : Polynomial.degreeLT R n),
    evaluationMap_value b p = Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value
      (Matrix.of fun (i j : Fin n) => b i ^ (j : ℕ)) ((Polynomial.degreeLTEquiv R n) p)

def determinant_nonzero_iff : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (b : Fin n → K),
    _root_.D05.M05.determinant (Matrix.of fun (i j : Fin n) => b i ^ (j : ℕ)) ≠ 0 ↔
      Function.Injective b

def evaluation_bijective : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (b : Fin n → K),
    Function.Injective b → Function.Bijective (evaluationMap_value b)

/-- Existence and uniqueness of the linear isomorphism with exactly the
specified evaluation formula, including the unique map in dimension zero. -/
def evaluation_isomorphism : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (b : Fin n → K),
    Function.Injective b →
      ∃! e : Polynomial.degreeLT K n ≃ₗ[K] (Fin n → K),
        ∀ p i, e p i = (p : Polynomial K).eval (b i)

/-- The inverse of evaluation gives one and only one formal polynomial
of the required degree for every tuple of values. -/
def unique_interpolant : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (b : Fin n → K),
    Function.Injective b → ∀ y : Fin n → K,
      ∃! p : Polynomial K, p.degree < (n : WithBot ℕ) ∧
        ∀ i, p.eval (b i) = y i

end Specs.D05.M05.Vandermonde
