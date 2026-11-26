import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators RestrictedProduct

namespace LinearAlgebraicGroups.Arithmetic.BracketLatticeCompactness

open AdelicGroups
open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.Unipotent (Index)

universe u

/-- The scalar-extended bilinear operation with the specified structure constants. -/
def bracket {I K L : Type*} [Fintype I] [CommRing K] [CommRing L]
    (c : I → I → I → K) (f : K →+* L) (x y : I → L) : I → L :=
  (Matrix.of (fun i j => ∑ k, x k * f (c k j i))).mulVec y

/-- A matrix is a bracket automorphism if its action on vectors preserves the bracket. -/
def PreservesBracket {I K L : Type*} [Fintype I] [DecidableEq I] [CommRing K] [CommRing L]
    (c : I → I → I → K) (f : K →+* L) (g : Matrix.GeneralLinearGroup I L) : Prop :=
  ∀ x y, bracket c f (g.val.mulVec x) (g.val.mulVec y) = g.val.mulVec (bracket c f x y)

/-- The full adelic group admits a compact set of representatives for right multiplication
by rational points. -/
def CompactRepresentatives {K : Type u} [Field K] (D : GlobalFieldData.{u, 0} K)
    {Q : AffineAlgebraicGroup K} (i : MatrixRealization Q) : Prop :=
  ∃ C : Set (Adeles D i ∅), IsCompact C ∧
    ∀ a : Adeles D i ∅, ∃ γ : RationalPoints Q, ∃ c ∈ C,
      ∀ w : Outside D ∅, c w = a w * localPoint D i w.1 γ

variable {K : Type u} [Field K] {Q : AffineAlgebraicGroup K}
  (D : GlobalFieldData.{u, 0} K) (i : MatrixRealization Q)

/-- Determinant one on every actual completion. -/
def LocalDeterminantOne : Prop :=
  ∀ w (g : LocalPoints D i w), (asMatrix i (D.Completion w) g).det = 1

/-- Bracket invariance on every actual completion. -/
def LocalBracketInvariant (c : Index.{u} i.size → Index.{u} i.size → Index.{u} i.size → K) : Prop :=
  ∀ w (g : LocalPoints D i w),
    PreservesBracket c (D.embedding w) (asMatrix i (D.Completion w) g)

/-- Polynomial invariance on every actual completion. -/
def LocalPolynomialInvariant (p : MvPolynomial (Index.{u} i.size) K) : Prop :=
  ∀ w (g : LocalPoints D i w) x,
    p.eval₂ (D.embedding w) ((asMatrix i (D.Completion w) g).val.mulVec x) =
      p.eval₂ (D.embedding w) x

end LinearAlgebraicGroups.Arithmetic.BracketLatticeCompactness

namespace LinearAlgebraicGroups.Specs.BracketLatticeCompactness

open Arithmetic Arithmetic.AdelicGroups Arithmetic.BracketLatticeCompactness
open IntegralModels (MatrixRealization)
open Unipotent (Index)

universe u v w

/-- Lattice comparison in a closed realization, with a finite family of invariant
polynomials and finitely many rational bracket-automorphism cosets. -/
def latticeComparison : Prop :=
  ∀ {K : Type u} [Field K] [hK : NumberField K]
    {Q : AffineAlgebraicGroup K} (i : MatrixRealization Q),
    let D := GlobalFieldData.number.{u, 0} hK
    let I := Index.{u} i.size
    ∀ (c : I → I → I → K) {P : Type v} {J : Type w} [Fintype P] [Fintype J]
      (p : P → MvPolynomial I K) (d : P → ℕ)
      (r : J → Matrix.GeneralLinearGroup I K),
      LocalDeterminantOne D i → LocalBracketInvariant D i c →
      (∀ b, 0 < d b ∧ (p b).IsHomogeneous (d b)) →
      (∀ b, LocalPolynomialInvariant D i (p b)) →
      (∀ x : I → K, x ≠ 0 → ∃ b, (p b).eval x ≠ 0) →
      (∀ A : Matrix.GeneralLinearGroup I K, PreservesBracket c (RingHom.id K) A →
        ∃ γ j, A = i.onPoints γ * r j) →
      CompactRepresentatives D i

end LinearAlgebraicGroups.Specs.BracketLatticeCompactness
