import MathGenome.Internal.Specs.D05.M08.Charpoly
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.AlgebraTower
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Complex.Norm

/-! Independent interface for paper.tex:1377–1388. Realification uses the
existing real scalar action on a complex vector space, with its scalar tower.
Sum indices put all the real coordinates before all imaginary coordinates.
No invertibility, splitting, or positive dimension is required. -/
noncomputable section
open scoped BigOperators
namespace Specs.D05.M09.RealComplexBridge.Realification

/-- The grouped matrix of the same map after restricting scalars. -/
def realMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (A.map Complex.re) (-(A.map Complex.im))
    (A.map Complex.im) (A.map Complex.re)

/-- The change of coordinates `(x,y) ↦ (x+iy,x-iy)`, after complex scalar extension. -/
def splitMatrix (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks 1 (Complex.I • 1) 1 (-Complex.I • 1)

/-- Its inverse `(u,v) ↦ ((u+v)/2,(u-v)/(2i))`. -/
def unsplitMatrix (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks ((1/2 : ℂ) • 1) ((1/2 : ℂ) • 1)
    ((-Complex.I/2 : ℂ) • 1) ((Complex.I/2 : ℂ) • 1)

def grouped_basis : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (b : Module.Basis (Fin n) ℂ V),
    ∃ r : Module.Basis (Fin n ⊕ Fin n) ℝ V,
      (∀ j, r (.inl j) = b j) ∧ (∀ j, r (.inr j) = Complex.I • b j) ∧
      (∀ v j, r.repr v (.inl j) = (b.repr v j).re) ∧
      (∀ v j, r.repr v (.inr j) = (b.repr v j).im) ∧
      (∀ T : V →ₗ[ℂ] V, LinearMap.toMatrix r r (T.restrictScalars ℝ) =
        realMatrix (LinearMap.toMatrix b b T))

def real_dimension : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    Module.finrank ℝ V = 2 * Module.finrank ℂ V

def split_inverse : Prop :=
  ∀ n, splitMatrix n * unsplitMatrix n = 1 ∧ unsplitMatrix n * splitMatrix n = 1

def split_coordinates : Prop :=
  ∀ {n : ℕ} (x y : Fin n → ℂ),
    (splitMatrix n).mulVec (Sum.elim x y) =
      Sum.elim (fun j => x j + Complex.I * y j) (fun j => x j - Complex.I * y j)

def unsplit_coordinates : Prop :=
  ∀ {n : ℕ} (u v : Fin n → ℂ),
    (unsplitMatrix n).mulVec (Sum.elim u v) =
      Sum.elim (fun j => (u j + v j)/2) (fun j => (u j - v j)/(2*Complex.I))

def intertwining : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
    splitMatrix n * (realMatrix A).map (algebraMap ℝ ℂ) =
      Matrix.fromBlocks A 0 0 (A.map (starRingEnd ℂ)) * splitMatrix n

/-- Both sides are formal complex polynomials; the real polynomial is embedded
coefficientwise, and conjugation fixes the formal variable. -/
def matrix_charpoly : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
    (realMatrix A).charpoly.map (algebraMap ℝ ℂ) =
      A.charpoly * A.charpoly.map (starRingEnd ℂ)

def operator_charpoly : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V),
    (T.restrictScalars ℝ).charpoly.map (algebraMap ℝ ℂ) =
      T.charpoly * T.charpoly.map (starRingEnd ℂ)

def real_product : Prop :=
  ∀ p : Polynomial ℂ,
    (p * p.map (starRingEnd ℂ)).map (starRingEnd ℂ) = p * p.map (starRingEnd ℂ) ∧
    ∃ q : Polynomial ℝ, q.map (algebraMap ℝ ℂ) = p * p.map (starRingEnd ℂ)

def determinant : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V),
    LinearMap.det (T.restrictScalars ℝ) = ‖LinearMap.det T‖ ^ 2

def trace : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V),
    LinearMap.trace ℝ V (T.restrictScalars ℝ) = 2 * (LinearMap.trace ℂ V T).re

end Specs.D05.M09.RealComplexBridge.Realification
