import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.FaithfulLinearization
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeRank
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SpecialLinearDatum
import Mathlib.GroupTheory.Commensurable
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.Algebra.Order.Archimedean.Real.Basic

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.IntegralModels

open GeneralLinearStructure (MatrixPoints SpecialMatrixPoints)
open Unipotent (Index)

noncomputable section

/-- Rational points over the base field, with the scheme's group law. -/
abbrev RationalPoints {k : Type u} [Field k] (G : AffineAlgebraicGroup k) :=
  ((groupPointsFunctor k).obj G.val).obj (CommAlgCat.of k k)

/-- A closed faithful matrix realization, with its matrix interpretation on every test algebra. -/
structure MatrixRealization {k : Type u} [Field k] (G : AffineAlgebraicGroup k) where
  size : ℕ
  ambient : AffineAlgebraicGroup k
  matrix : MatrixPoints ambient size
  embedding : G.val ⟶ ambient.val
  closed : IsClosedImmersion embedding.hom.hom.left

def MatrixRealization.onPoints {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (i : MatrixRealization G) :
    RationalPoints G →* Matrix.GeneralLinearGroup (Index.{u} i.size) k :=
  (i.matrix.hom.app (CommAlgCat.of k k)).hom.comp
    (((groupPointsFunctor k).map i.embedding).app (CommAlgCat.of k k)).hom

/-- The inverse image of the integral general linear group in the indicated realization. -/
def integralSubgroup {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {G : AffineAlgebraicGroup k} (i : MatrixRealization G) : Subgroup (RationalPoints G) :=
  (Matrix.GeneralLinearGroup.map (algebraMap R k)).range.comap i.onPoints


/-- Arithmeticity is membership in the commensurability class of an integral realization. -/
def IsArithmetic {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {G : AffineAlgebraicGroup k} (H : Subgroup (RationalPoints G)) : Prop :=
  ∃ i : MatrixRealization G, Subgroup.Commensurable H (integralSubgroup (R := R) i)

/-- All infinite places are included. Only the finite places in the chosen set affect the ring. -/
abbrev SIntegers (K : Type u) [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :=
  (↑S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))).integer K

def RationalIndependence : Prop :=
  ∀ (G : AffineAlgebraicGroup ℚ) (i j : MatrixRealization G),
    Subgroup.Commensurable (integralSubgroup (R := ℤ) i) (integralSubgroup (R := ℤ) j)

def NumberFieldIndependence : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (G : AffineAlgebraicGroup K) (i j : MatrixRealization G),
    Subgroup.Commensurable (integralSubgroup (R := SIntegers K S) i)
      (integralSubgroup (R := SIntegers K S) j)

def ArithmeticClass : Prop :=
  ∀ (G : AffineAlgebraicGroup ℚ) (H : Subgroup (RationalPoints G)),
    Nonempty (MatrixRealization G) ∧
    (IsArithmetic (R := ℤ) H ↔
      ∀ i : MatrixRealization G, Subgroup.Commensurable H (integralSubgroup (R := ℤ) i))

/-- The principal congruence subgroup at a positive integer level. -/
def principalCongruence (n : ℕ) (m : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Index.{0} n) ℤ) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (Ideal.span {(m : ℤ)}))).ker

/-- Interpretation of integral determinant-one matrices in the given rational matrix scheme. -/
def specialLinearIntegralMap {n : ℕ} {G : AffineAlgebraicGroup ℚ}
    (s : SpecialMatrixPoints G n) :
    Matrix.SpecialLinearGroup (Index.{0} n) ℤ →* RationalPoints G :=
  (s.inv.app (CommAlgCat.of ℚ ℚ)).hom.comp
    (Matrix.SpecialLinearGroup.map (algebraMap ℤ ℚ))

def SpecialLinearArithmetic : Prop :=
  ∀ (n : ℕ) (G : AffineAlgebraicGroup ℚ) (s : SpecialMatrixPoints G n),
    IsArithmetic (R := ℤ) (specialLinearIntegralMap s).range ∧
    ∀ m : ℕ, 0 < m →
      (principalCongruence n m).FiniteIndex ∧
      IsArithmetic (R := ℤ) ((principalCongruence n m).map (specialLinearIntegralMap s))

def realPointMap (G : AffineAlgebraicGroup ℚ) :
    RationalPoints G →* ((groupPointsFunctor ℚ).obj G.val).obj (CommAlgCat.of ℚ ℝ) :=
  (((groupPointsFunctor ℚ).obj G.val).map
    (CommAlgCat.ofHom (Algebra.ofId ℚ ℝ))).hom

def RealEmbeddings : Prop :=
  (∀ G : AffineAlgebraicGroup ℚ, Function.Injective (realPointMap G)) ∧
  ∀ (n : ℕ) (G : AffineAlgebraicGroup ℚ) (s : SpecialMatrixPoints G n),
    Function.Injective ((realPointMap G).comp (specialLinearIntegralMap s)) ∧
    (s.hom.app (CommAlgCat.of ℚ ℝ)).hom.comp
      ((realPointMap G).comp (specialLinearIntegralMap s)) =
      Matrix.SpecialLinearGroup.map (algebraMap ℤ ℝ)

/-- In particular, over `ℚ` the relative rank is one less than the matrix size. -/
def SpecialLinearRank : Prop :=
  ∀ (k : Type u) [Field k] (r : ℕ) (G : AffineAlgebraicGroup k), SpecialMatrixPoints G (r + 1) →
    RelativeRank.relativeRank G = (r : WithBot ℕ∞)

/-- Result F11, including the arithmetic examples and the rational rank of the matrix group. -/
def ArithmeticIntegralModels : Prop :=
  RationalIndependence ∧ NumberFieldIndependence.{u} ∧ ArithmeticClass ∧
  SpecialLinearArithmetic ∧ RealEmbeddings ∧ SpecialLinearRank.{u}

end

end LinearAlgebraicGroups.Specs.IntegralModels
