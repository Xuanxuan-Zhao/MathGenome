import MathGenome.Internal.Specs.D07.Ch11.PolynomialDefinition
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.Fin.Rev

/-!
K07.19.resultant_definition, paper.tex:5320–5343.
The indices are `Fin (n + m)`. Reversing the ascending list
`g, Xg, …, X^(n-1)g, f, Xf, …, X^(m-1)f` gives precisely
`X^(m-1)f, …, f, X^(n-1)g, …, g`. Columns are reversed monomials.
The definitions retain explicit bounds, including zero bounds and the zero ring.
-/

universe u
namespace Specs.D07.Ch19.ResultantDefinition
open Polynomial Module

/-- Row polynomials in the paper's order. -/
noncomputable def rowPolynomial {R : Type u} [CommRing R] (f g : R[X]) (n m : ℕ)
    (i : Fin (n + m)) : R[X] :=
  i.rev.addCases (fun k : Fin n => X ^ (k : ℕ) * g)
    (fun k : Fin m => X ^ (k : ℕ) * f)

/-- Literal descending-row, descending-column Sylvester matrix. -/
noncomputable def descendingSylvester {R : Type u} [CommRing R] (f g : R[X]) (n m : ℕ) :
    Matrix (Fin (n + m)) (Fin (n + m)) R :=
  fun i j => (rowPolynomial f g n m i).coeff (j.rev : ℕ)

/-- The fixed-bound determinant of the notes. -/
noncomputable def fixedResultant {R : Type u} [CommRing R]
    (f g : R[X]) (n m : ℕ) : R :=
  (descendingSylvester f g n m).det

/-- Intended for nonzero polynomials; zero inputs are allowed as a total extension. -/
noncomputable def ordinaryResultant {R : Type u} [CommRing R] (f g : R[X]) : R :=
  fixedResultant f g f.natDegree g.natDegree

/-- `(A,B) ↦ Af+Bg`, on the spaces of the stated strict degree bounds. -/
noncomputable def combinationMap {R : Type u} [CommRing R] (f g : R[X])
    {n m : ℕ} (hf : f.natDegree ≤ n) (hg : g.natDegree ≤ m) :
    R[X]_m × R[X]_n →ₗ[R] R[X]_(n + m) :=
  (Polynomial.sylvesterMap f g hf hg).comp
    (LinearEquiv.prodComm R R[X]_m R[X]_n).toLinearMap

/-- Descending monomial basis of the target. -/
noncomputable def targetBasis (R : Type u) [CommRing R] (n m : ℕ) :
    Basis (Fin (n + m)) R R[X]_(n + m) :=
  (degreeLT.basis R (n + m)).reindex Fin.revPerm

/-- Descending monomials of A, followed by descending monomials of B. -/
noncomputable def sourceBasis (R : Type u) [CommRing R] (n m : ℕ) :
    Basis (Fin (n + m)) R (R[X]_m × R[X]_n) :=
  ((degreeLT.basisProd R n m).reindex Fin.revPerm).map
    (LinearEquiv.prodComm R R[X]_n R[X]_m)

def RowBlocks : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R[X]) (n m : ℕ),
    (∀ i : Fin m, rowPolynomial f g n m ⟨i, by omega⟩ = X ^ (m - 1 - i.val) * f) ∧
    (∀ i : Fin n, rowPolynomial f g n m ⟨m + i.val, by omega⟩ =
      X ^ (n - 1 - i.val) * g)

def DeterminantDefinition : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R[X]) (n m : ℕ),
    fixedResultant f g n m = (descendingSylvester f g n m).det

def OrdinaryDefinition : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R[X]), f ≠ 0 → g ≠ 0 →
    ordinaryResultant f g = fixedResultant f g f.natDegree g.natDegree

def EmptyDeterminant : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R[X]), fixedResultant f g 0 0 = 1

/-- This is a matrix equality, not just an assertion of equal determinants. -/
def SylvesterBridge : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R[X]) (n m : ℕ),
    f.natDegree ≤ n → g.natDegree ≤ m →
    descendingSylvester f g n m =
      (Polynomial.sylvester f g n m).transpose.submatrix Fin.rev Fin.rev

def ResultantBridge : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R[X]) (n m : ℕ),
    f.natDegree ≤ n → g.natDegree ≤ m →
    fixedResultant f g n m = Polynomial.resultant f g n m

def CombinationFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R[X]) (n m : ℕ)
    (hf : f.natDegree ≤ n) (hg : g.natDegree ≤ m) (A : R[X]_m) (B : R[X]_n),
    (combinationMap f g hf hg (A, B) : R[X]) = (A : R[X]) * f + (B : R[X]) * g

def MatrixRepresentation : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R[X]) (n m : ℕ)
    (hf : f.natDegree ≤ n) (hg : g.natDegree ≤ m),
    (combinationMap f g hf hg).toMatrix (sourceBasis R n m) (targetBasis R n m) =
      (descendingSylvester f g n m).transpose

def SwapSign : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R[X]) (n m : ℕ),
    f.natDegree ≤ n → g.natDegree ≤ m →
    fixedResultant g f m n = (-1 : R) ^ (n * m) * fixedResultant f g n m

def ConstantResultant : Prop :=
  ∀ (R : Type u) [CommRing R] (f : R[X]) (c : R) (n : ℕ),
    f ≠ 0 → c ≠ 0 → f.natDegree = n → ordinaryResultant f (C c) = c ^ n

end Specs.D07.Ch19.ResultantDefinition
