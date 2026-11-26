import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped Polynomial

universe u

namespace LinearAlgebraicGroups.Specs.GeneralLinearCentralIsogeny

open CentralDerived CentralTorus
open GeneralLinearStructure (MatrixPoints SpecialMatrixPoints)
open GeometricRadicals (IsSplitReductive)
open SchemeDerivedGroup (IsDerivedSubgroup)
open SmoothnessAndIsogenies (rootsOfUnityCoordinates)
open DiagonalizableGroups (rootsOfUnityPoints)
open Unipotent (Index)

noncomputable section

variable {k : Type u} [Field k]

abbrev pointMap {G H : GroupScheme k} (f : G ⟶ H) (R : TestAlgebra k) :=
  ((groupPointsFunctor k).map f).app R

/-- The test algebra obtained by adjoining a root of an invertible determinant. -/
abbrev determinantRootAlgebra (R : TestAlgebra k) (n : ℕ) (d : Rˣ) :=
  AdjoinRoot (Polynomial.X ^ n - Polynomial.C (d : R))

abbrev determinantRootTestAlgebra (R : TestAlgebra k) (n : ℕ) (d : Rˣ) : TestAlgebra k :=
  CommAlgCat.of k (determinantRootAlgebra R n d)

def determinantRootMap (R : TestAlgebra k) (n : ℕ) (d : Rˣ) :
    R ⟶ determinantRootTestAlgebra R n d :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (determinantRootAlgebra R n d))

/-- The central isogeny for the affine groups representing the standard matrix and unit functors. -/
def GeneralLinearCentralIsogeny : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 0 < n →
    ∀ (G S M : AffineAlgebraicGroup k) (g : MatrixPoints G n) (s : SpecialMatrixPoints S n)
      (a : (groupPointsFunctor k).obj M.val ≅ StandardGroups.multiplicativePoints k),
      IsSplitReductive G ∧
      ∃ (Z : ClosedSubgroup G.val) (i : M.val ≅ Z.group) (T : ClosedSubgroup Z.group)
        (f : S.val ⟶ G.val) (hf : IsClosedImmersion f.hom.hom.left),
        let D : ClosedSubgroup G.val := ⟨S.val, f, hf⟩
        let t := T.inclusion ≫ i.inv
        IsSchemeCentre Z ∧ IsLargestTorus T ∧ IsIso T.inclusion ∧ IsDerivedSubgroup D ∧
        (∀ (R : TestAlgebra k) (x : Points M.val.X R),
          g.hom.app R (pointMap (i.hom ≫ Z.inclusion) R x) =
            Matrix.GeneralLinearGroup.scalar (Index.{u} n) (a.hom.app R x)) ∧
        (∀ (R : TestAlgebra k) (x : Points S.val.X R),
          g.hom.app R (pointMap f R x) = Matrix.SpecialLinearGroup.toGL (s.hom.app R x)) ∧
        ∃ m : (T.group ⊗ S.val) ⟶ G.val,
          IsCentralProduct T D m ∧ Flat m.hom.hom.left ∧ Surjective m.hom.hom.left ∧
          (∀ (R : TestAlgebra k) (x : Points (T.group ⊗ S.val).X R),
            g.hom.app R (pointMap m R x) =
              Matrix.GeneralLinearGroup.scalar (Index.{u} n)
                (a.hom.app R (pointMap (firstProjection T.group S.val ≫ t) R x)) *
                Matrix.SpecialLinearGroup.toGL
                  (s.hom.app R (pointMap (secondProjection T.group S.val) R x))) ∧
          (∀ (R : TestAlgebra k) (x : Points G.val.X R),
            let d := Matrix.GeneralLinearGroup.det (g.hom.app R x)
            let A := determinantRootTestAlgebra R n d
            let b := determinantRootMap R n d
            Module.Finite R (determinantRootAlgebra R n d) ∧
            Module.FaithfullyFlat R (determinantRootAlgebra R n d) ∧
            ∃ (z : Aˣ) (y : Points (T.group ⊗ S.val).X A),
              (z : A) = AdjoinRoot.root (Polynomial.X ^ n - Polynomial.C (d : R)) ∧
              z ^ n = Units.map b.hom.toMonoidHom d ∧
              a.hom.app A (pointMap (firstProjection T.group S.val ≫ t) A y) = z ∧
              Matrix.SpecialLinearGroup.toGL
                (s.hom.app A (pointMap (secondProjection T.group S.val) A y)) =
                  Matrix.GeneralLinearGroup.scalar (Index.{u} n) z⁻¹ *
                    Matrix.GeneralLinearGroup.map b.hom.toRingHom (g.hom.app R x) ∧
              pointMap m A y = mapPoints b x) ∧
          ∃ (J : ClosedSubgroup (T.group ⊗ S.val))
            (e : J.group ≅ specGroup (rootsOfUnityCoordinates k n))
            (r : (groupPointsFunctor k).obj (specGroup (rootsOfUnityCoordinates k n)) ≅
              rootsOfUnityPoints k n),
            let c := (groupPointsFunctor k).mapIso e ≪≫ r
            IsSchemeKernel m J ∧ IsFinite J.group.X.hom ∧
            (∀ (Y : SchemeOver k) (x : Y ⟶ (T.group ⊗ S.val).X),
              Centralizes J.inclusion x) ∧
            (∀ (R : TestAlgebra k)
              (φ : MonoidAlgebra k (ULift.{u} (Multiplicative (ZMod n))) →ₐ[k] R)
              (x : Points (specGroup (rootsOfUnityCoordinates k n)).X R),
              x.left = Spec.map (CommRingCat.ofHom φ.toRingHom) →
              ((r.hom.app R x).val : R) = φ (MonoidAlgebra.single ⟨Multiplicative.ofAdd 1⟩ 1)) ∧
            (∀ (R : TestAlgebra k) (x : Points J.group.X R),
              let z : rootsOfUnity n R := c.hom.app R x
              a.hom.app R (pointMap (J.inclusion ≫ firstProjection T.group S.val ≫ t) R x) =
                z.val ∧
              Matrix.SpecialLinearGroup.toGL
                (s.hom.app R (pointMap (J.inclusion ≫ secondProjection T.group S.val) R x)) =
                  Matrix.GeneralLinearGroup.scalar (Index.{u} n) z.val⁻¹) ∧
            ∀ (p : ℕ) [CharP k p], 0 < p → p ∣ n → ¬ Etale J.group.X.hom

end

end LinearAlgebraicGroups.Specs.GeneralLinearCentralIsogeny
