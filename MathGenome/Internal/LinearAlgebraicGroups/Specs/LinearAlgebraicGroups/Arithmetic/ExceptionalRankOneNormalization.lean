import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RootGroups
import Mathlib.FieldTheory.IsSepClosed

open AlgebraicGeometry CategoryTheory
open scoped Matrix

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalRankOneNormalization

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Cocharacter)
open GeometricRadicals (IsTorus)
open RootGroups (AdditiveLine rootPoint)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

noncomputable section

/-- The standard matrix functor in size two, indexed by `Fin 2`. -/
def matrixPoints (k : Type u) [Field k] : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Matrix.SpecialLinearGroup (Fin 2) R)
  map a := GrpCat.ofHom (Matrix.SpecialLinearGroup.map a.hom.toRingHom)
  map_id _ := by apply GrpCat.ext; intro x; ext i j; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; ext i j; rfl

abbrev SL₂ (R : Type u) [CommRing R] := Matrix.SpecialLinearGroup (Fin 2) R

def upper {R : Type u} [CommRing R] (a : R) : SL₂ R :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

def lower {R : Type u} [CommRing R] (a : R) : SL₂ R :=
  ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩

def diagonal {R : Type u} [CommRing R] (t : Rˣ) : SL₂ R :=
  ⟨!![(t : R), 0; 0, (↑t⁻¹ : R)], by simp [Matrix.det_fin_two]⟩

def antiDiagonal (R : Type u) [CommRing R] : SL₂ R :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

/-- The entries of conjugation by the invertible matrix `diag(t,1)`. -/
def diagonalConjugate {R : Type u} [CommRing R] (t : Rˣ) (m : SL₂ R) : SL₂ R :=
  ⟨!![m.val 0 0, (t : R) * m.val 0 1; (↑t⁻¹ : R) * m.val 1 0, m.val 1 1], by
    have h := m.property
    rw [Matrix.det_fin_two] at h ⊢
    change m.val 0 0 * m.val 1 1 - (t : R) * m.val 0 1 * ((↑t⁻¹ : R) * m.val 1 0) = 1
    rwa [show (t : R) * m.val 0 1 * ((↑t⁻¹ : R) * m.val 1 0) =
      m.val 0 1 * m.val 1 0 by
        calc
          _ = ((t : R) * (↑t⁻¹ : R)) * (m.val 0 1 * m.val 1 0) := by ring
          _ = _ := by simp]⟩

abbrev matrixMap {K : Type u} [Field K] {S : AffineAlgebraicGroup K} {H : GroupScheme K}
    (m : (groupPointsFunctor K).obj S.val ≅ matrixPoints K) (j : S.val ⟶ H)
    (R : TestAlgebra K) : SL₂ R →* GroupPoints H R :=
  (((groupPointsFunctor K).map j).app R).hom.comp (m.inv.app R).hom

/-- Rescale a closed geometric rank-one embedding so that both elementary
sections are defined over the original field. The matrix comparison represents
the standard special linear group naturally on all commutative test algebras. -/
def NormalizeRootCoordinates : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [IsSepClosure F K]
    (G : AffineAlgebraicGroup F) (T U V : ClosedSubgroup G.val),
    IsTorus T.group →
    ∀ (A : AdditiveLine F) (B : AdditiveLine K)
      (x : A.group ≅ U.group) (y : A.group ≅ V.group),
    let E := groupBaseChange F K
    ∀ (xK : B.group ≅ E.obj U.group) (yK : B.group ≅ E.obj V.group)
      (S : AffineAlgebraicGroup K)
      (m : (groupPointsFunctor K).obj S.val ≅ matrixPoints K)
      (j : S.val ⟶ E.obj G.val),
      IsClosedImmersion j.hom.hom.left →
      (∀ (R : TestAlgebra K) (a : R),
        matrixMap m j R (upper a) = rootPoint (xK.hom ≫ E.map U.inclusion) R a) →
      (∀ (R : TestAlgebra K) (a : R),
        matrixMap m j R (lower a) = rootPoint (yK.hom ≫ E.map V.inclusion) R a) →
      (∃ d : Cocharacter (E.obj T.group), ∀ (R : TestAlgebra K) (t : Rˣ),
        matrixMap m j R (diagonal t) = cocharacterPoint d R t ≫
          (E.map T.inclusion).hom.hom) →
      matrixMap m j (CommAlgCat.of K K) (antiDiagonal K) ∈
        Subgroup.normalizer
          (((groupPointsFunctor K).map (E.map T.inclusion)).app (CommAlgCat.of K K)).hom.range →
      ∃ (c : Kˣ) (j' : S.val ⟶ E.obj G.val)
        (x' : A.group ≅ U.group) (y' : A.group ≅ V.group),
        IsClosedImmersion j'.hom.hom.left ∧
        (∀ (R : TestAlgebra K) (g : SL₂ R),
          matrixMap m j' R g = matrixMap m j R
            (diagonalConjugate (Units.map (algebraMap K R) c) g)) ∧
        (∀ (R : TestAlgebra K) (t : Rˣ),
          matrixMap m j' R (diagonal t) = matrixMap m j R (diagonal t)) ∧
        (∀ (R : TestAlgebra K) (a : R),
          baseChangePoint F K G.val.X R (matrixMap m j' R (upper a)) =
            rootPoint (x'.hom ≫ U.inclusion) ((restrictTestAlgebra F K).obj R) a) ∧
        (∀ (R : TestAlgebra K) (a : R),
          baseChangePoint F K G.val.X R (matrixMap m j' R (lower a)) =
            rootPoint (y'.hom ≫ V.inclusion) ((restrictTestAlgebra F K).obj R) a)

end

end LinearAlgebraicGroups.Specs.ExceptionalRankOneNormalization
