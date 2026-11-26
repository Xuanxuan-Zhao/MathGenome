import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.AlgebraicGeometry.OpenImmersion

open AlgebraicGeometry

universe u v

namespace LinearAlgebraicGroups.Specs.MatrixOpenCell

open StandardGroups

noncomputable section

/-- The upper-left square submatrix with the first `m` rows and columns. -/
def leadingBlock {R : Type v} {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (m : ℕ) (hm : m ≤ n) : Matrix (Fin m) (Fin m) R :=
  A.submatrix (Fin.castLE hm) (Fin.castLE hm)

def leadingMinor {R : Type v} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (m : ℕ) (hm : m ≤ n) : R :=
  (leadingBlock A m hm).det

def HasUnitMinors {R : Type v} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ m (hm : m ≤ n), IsUnit (leadingMinor A m hm)

/-- The points of the two opposite unitriangular groups and the diagonal torus. -/
structure Factors (R : Type v) [CommRing R] (n : ℕ) where
  lower : Matrix (Fin n) (Fin n) R
  diagonal : Fin n → Rˣ
  upper : Matrix (Fin n) (Fin n) R
  lower_zero : ∀ i j, i < j → lower i j = 0
  lower_one : ∀ i, lower i i = 1
  upper_zero : ∀ i j, j < i → upper i j = 0
  upper_one : ∀ i, upper i i = 1

def Factors.product {R : Type v} [CommRing R] {n : ℕ} (f : Factors R n) :
    Matrix (Fin n) (Fin n) R :=
  f.lower * Matrix.diagonal (fun i => (f.diagonal i : R)) * f.upper

def Factorization : Prop :=
  ∀ (R : Type v) [CommRing R] (n : ℕ) (A : Matrix (Fin n) (Fin n) R),
    HasUnitMinors A ↔ ∃! f : Factors R n, f.product = A

def MinorFormula : Prop :=
  ∀ (R : Type v) [CommRing R] (n : ℕ) (f : Factors R n) (m : ℕ) (hm : m ≤ n),
    leadingMinor f.product m hm = ∏ i : Fin m, (f.diagonal (Fin.castLE hm i) : R)

/-- Universal matrix before inverting its determinant. The lifted index agrees
with the standard GL coordinates over a field, in every universe. -/
def genericMatrix (k : Type u) [CommRing k] (n : ℕ) :
    Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n))
      (MvPolynomial (ULift.{u} (Fin n) × ULift.{u} (Fin n)) k) :=
  fun i j => MvPolynomial.X (i, j)

abbrev MatrixGroupCoordinates (k : Type u) [CommRing k] (n : ℕ) :=
  Localization.Away (genericMatrix k n).det

def glMatrix (k : Type u) [CommRing k] (n : ℕ) :
    Matrix (Fin n) (Fin n) (MatrixGroupCoordinates k n) :=
  ((algebraMap _ (MatrixGroupCoordinates k n)).mapMatrix (genericMatrix k n)).submatrix
    ULift.up ULift.up

/-- One equation for the intersection of the principal opens in the GL coordinates. -/
def minorProduct (k : Type u) [CommRing k] (n : ℕ) : MatrixGroupCoordinates k n :=
  ∏ m : Fin (n + 1), leadingMinor (glMatrix k n) m.val (Nat.le_of_lt_succ m.isLt)

abbrev CellCoordinates (k : Type u) [CommRing k] (n : ℕ) :=
  Localization.Away (minorProduct k n)

def cellInclusion (k : Type u) [CommRing k] (n : ℕ) :
    Spec (CommRingCat.of (CellCoordinates k n)) ⟶
      Spec (CommRingCat.of (MatrixGroupCoordinates k n)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (MatrixGroupCoordinates k n) (CellCoordinates k n)))

def cellMatrix (k : Type u) [CommRing k] (n : ℕ) :
    Matrix (Fin n) (Fin n) (CellCoordinates k n) :=
  (algebraMap (MatrixGroupCoordinates k n) (CellCoordinates k n)).mapMatrix (glMatrix k n)

def Factors.map {R S : Type v} [CommRing R] [CommRing S] {n : ℕ}
    (g : R →+* S) (f : Factors R n) : Factors S n where
  lower := g.mapMatrix f.lower
  diagonal := fun i => Units.map g (f.diagonal i)
  upper := g.mapMatrix f.upper
  lower_zero := fun i j h => by simp [f.lower_zero i j h]
  lower_one := fun i => by simp [f.lower_one i]
  upper_zero := fun i j h => by simp [f.upper_zero i j h]
  upper_one := fun i => by simp [f.upper_one i]

/-- The regular inverse is given by the factors of the universal matrix over the
principal localization. Their evaluation gives the factors on every test algebra. -/
def RegularOpenCell : Prop :=
  ∀ (k : Type u) [CommRing k] (n : ℕ),
    IsOpenImmersion (cellInclusion k n) ∧
    Set.range (cellInclusion k n) =
      (PrimeSpectrum.basicOpen (minorProduct k n) : Set (PrimeSpectrum (MatrixGroupCoordinates k n))) ∧
    ∃ f : Factors (CellCoordinates k n) n, f.product = cellMatrix k n ∧
      (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
        (φ : CellCoordinates k n →ₐ[k] R) (ψ : R →ₐ[k] S),
        (f.map φ.toRingHom).map ψ.toRingHom = f.map (ψ.comp φ).toRingHom) ∧
      ∀ (R : Type u) [CommRing R] [Algebra k R],
        Function.Bijective (fun φ : CellCoordinates k n →ₐ[k] R => f.map φ.toRingHom) ∧
        (∀ φ : CellCoordinates k n →ₐ[k] R,
          (f.map φ.toRingHom).product = φ.toRingHom.mapMatrix (cellMatrix k n)) ∧
        ∀ A : Matrix.GeneralLinearGroup (Fin n) R,
          HasUnitMinors A.val ↔
            ∃! φ : CellCoordinates k n →ₐ[k] R, ∀ i j, φ (cellMatrix k n i j) = A.val i j

/-- The ambient coordinate algebra and universal matrix are the ones from A03
after relabeling the matrix indices by the canonical lift of `Fin n`. -/
def StandardGLComparison : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    ∃ e : MatrixGroupCoordinates k n ≃ₐ[k] GLCoordinates k (ULift.{u} (Fin n)),
      ∀ i j, e (glMatrix k n i j) = universalMatrix k (ULift.{u} (Fin n)) (ULift.up i) (ULift.up j)

def ZeroSize : Prop :=
  ∀ (k : Type u) [CommRing k],
    CategoryTheory.IsIso (cellInclusion k 0) ∧ Nonempty (MatrixGroupCoordinates k 0 ≃ₐ[k] k)

end

end LinearAlgebraicGroups.Specs.MatrixOpenCell
