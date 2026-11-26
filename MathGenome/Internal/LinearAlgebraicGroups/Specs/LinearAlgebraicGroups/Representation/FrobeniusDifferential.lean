import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RelativeFrobenius
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.IdentityTangent

open CategoryTheory Opposite

universe u

namespace LinearAlgebraicGroups.Specs.FrobeniusDifferential

open RelativeFrobenius (twistCoordinates PullbackFormula scalarTensor)
open StandardGroups (SLCoordinates determinantOneIdeal universalMatrix
  specialLinearPoints generalLinearPoints multiplicativePoints)

noncomputable section

/-- The identity tangent map of relative Frobenius in the dual-number model. -/
def RelativeFrobeniusDifferential : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : HopfAlgebraCategory k) (f : twistCoordinates k p A ⟶ A),
    PullbackFormula k p A f → mapPointKernel (specGroupMap f) = 0

/-- The standard two-element basis index in the universe of the base field. -/
abbrev SL2Index := ULift.{u} (Fin 2)

variable {k : Type u} [Field k]

/-- The two-dimensional natural module, in the standard basis. -/
def naturalModule : specialLinearPoints k SL2Index.{u} ⟶ generalLinearPoints k SL2Index.{u} where
  app R := GrpCat.ofHom (Matrix.SpecialLinearGroup.toGL (R := R))
  naturality _ _ _ := by
    apply GrpCat.ext
    intro g
    apply Units.ext
    rfl

/-- The two characters of the standard diagonal torus on the Frobenius pullback
are compared as maps of group functors on all commutative test algebras. -/
def torusCharacter (n : ℤ) : multiplicativePoints k ⟶ multiplicativePoints k where
  app R := GrpCat.ofHom (zpowGroupHom n)
  naturality _ _ a := by
    apply GrpCat.ext
    intro t
    exact (map_zpow (Units.map a.hom.toMonoidHom) t n).symm

/-- The two components of a vector in the standard basis. -/
def diagonalEntries {R : Type u} (a b : R) : SL2Index.{u} → R :=
  fun i ↦ ![a, b] i.down

/-- The matrix of the standard diagonal torus point with parameter `t`. -/
def diagonalMatrix {R : Type u} [CommRing R] (t : Rˣ) : Matrix SL2Index.{u} SL2Index.{u} R :=
  Matrix.diagonal (diagonalEntries (t : R) (↑t⁻¹ : R))

def diagonalPoint {R : Type u} [CommRing R] (t : Rˣ) :
    Matrix.SpecialLinearGroup SL2Index.{u} R :=
  ⟨diagonalMatrix t, by
    rw [diagonalMatrix, Matrix.det_diagonal]
    exact (Fintype.prod_equiv (Equiv.ulift : SL2Index.{u} ≃ Fin 2)
      (diagonalEntries (↑t : R) (↑t⁻¹ : R))
      (![↑t, ↑t⁻¹] : Fin 2 → R) (fun _ ↦ rfl)).trans (by simp [Fin.prod_univ_two])⟩

/-- The matrix of coordinate entries on the standard determinant-one quotient. -/
def sl2Matrix (k : Type u) [Field k] : Matrix SL2Index.{u} SL2Index.{u} (SLCoordinates k SL2Index.{u}) :=
  (Ideal.Quotient.mkₐ k (determinantOneIdeal k SL2Index.{u})).mapMatrix
    (universalMatrix k SL2Index.{u})

/-- In a matrix point identification, the specified matrix entries evaluate to the
entries of the corresponding special linear matrix. -/
def IsMatrixIdentification (A : HopfAlgebraCategory k) (X : Matrix SL2Index.{u} SL2Index.{u} A)
    (e : (groupPointsFunctor k).obj (specGroup A) ≅ specialLinearPoints k SL2Index.{u}) : Prop :=
  ∀ (R : TestAlgebra k) (g : A →ₐ[k] R),
    (e.hom.app R ((testSpec k).map (CommAlgCat.ofHom g).op) :
      Matrix.SpecialLinearGroup SL2Index.{u} R).val = g.mapMatrix X

/-- In the standard split model of SL₂, the natural module pulled back
from the Frobenius twist has zero differential and a nontrivial rational action.
The two diagonal characters are `t ↦ t ^ p` and `t ↦ t ^ (-p)`. -/
def SplitSL2Example : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
    ∃ h : HopfAlgebra k (SLCoordinates k SL2Index.{u}), letI := h
    let A := CommHopfAlgCat.of k (SLCoordinates k SL2Index.{u})
    ∃ (f : twistCoordinates k p A ⟶ A)
      (e : (groupPointsFunctor k).obj (specGroup A) ≅ specialLinearPoints k SL2Index.{u})
      (eTwist : (groupPointsFunctor k).obj (specGroup (twistCoordinates k p A)) ≅
        specialLinearPoints k SL2Index.{u}),
    PullbackFormula k p A f ∧
    IsMatrixIdentification A (sl2Matrix k) e ∧
    IsMatrixIdentification (twistCoordinates k p A)
      (fun i j ↦ scalarTensor (frobenius k p) A 1 (sl2Matrix k i j)) eTwist ∧
    let ρ := (groupPointsFunctor k).map (specGroupMap f) ≫ eTwist.hom ≫ naturalModule
    mapDualKernel ρ = 0 ∧
    (∃ (R : TestAlgebra k) (g : ((groupPointsFunctor k).obj (specGroup A)).obj R),
      ρ.app R g ≠ 1) ∧
    (torusCharacter (k := k) (p : ℤ) ≠ torusCharacter (- (p : ℤ))) ∧
    ∀ (R : TestAlgebra k) (t : Rˣ),
      (ρ.app R (e.inv.app R (diagonalPoint t)) : Matrix.GeneralLinearGroup SL2Index.{u} R).val =
        Matrix.diagonal (diagonalEntries
          ((torusCharacter (k := k) (p : ℤ)).app R t : Rˣ).val
          ((torusCharacter (k := k) (- (p : ℤ))).app R t : Rˣ).val)

end

end LinearAlgebraicGroups.Specs.FrobeniusDifferential
