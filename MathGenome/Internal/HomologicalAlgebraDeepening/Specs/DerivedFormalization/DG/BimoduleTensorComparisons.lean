import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.BimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ShiftCone

open CategoryTheory

universe u v w z

namespace Specs.DerivedFormalization.DG.BimoduleTensorComparisons

open _root_.DerivedFormalization (DGCategoryModel RightDGModuleModel)
open BalancedTensor (bimodule tmul)
open BimoduleAdjunction (TensorModel ordinaryTensor)
open ShiftCone (shift shiftMap cone coneInclusion coneProjection)

/-- Balanced tensor commutes with signed cochain shifts in its first factor
and carries the strict cone sequence to the cone sequence of the tensor map. -/
def TensorComparisons : Prop :=
  ∀ {k : Type u} [CommRing k]
    (A : DGCategoryModel.{u,max v w z,w} k) (B : DGCategoryModel.{u,max v w z,z} k)
    (T : bimodule A B) (L : TensorModel T),
    let F := ordinaryTensor.{u,v,w,z} L
    ∃ (S : ∀ (M : RightDGModuleModel A) (s : ℤ), F.obj (shift M s) ≅ shift (F.obj M) s)
      (C : ∀ {M N : RightDGModuleModel A} (f : M ⟶ N), F.obj (cone f) ≅ cone (F.map f)),
      (∀ {M N : RightDGModuleModel A} (f : M ⟶ N) (s : ℤ),
        F.map (shiftMap s f) ≫ (S N s).hom = (S M s).hom ≫ shiftMap s (F.map f)) ∧
      (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
        F.map (coneInclusion f) ≫ (C f).hom = coneInclusion (F.map f)) ∧
      (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
        F.map (coneProjection f) ≫ (S M 1).hom = (C f).hom ≫ coneProjection (F.map f)) ∧
      (∀ (M : RightDGModuleModel A) (s : ℤ) (a : A.Obj) (b : B.Obj)
        (i j n : ℤ) (h : i + j = n) (x : ((shift M s).complex a).X i)
        (y : ((T.obj a).complex b).X j),
        (((S M s).hom.app b).f n)
          (L.degree (shift M s) b n (tmul T (shift M s) b a i j n h x y)) =
        L.degree M b (n + s) (tmul T M b a (i + s) j (n + s) (by omega) x y)) ∧
      (∀ {M N : RightDGModuleModel A} (f : M ⟶ N) (a : A.Obj) (b : B.Obj)
        (i j n : ℤ) (h : i + j = n) (x : ((cone f).complex a).X i)
        (y : ((T.obj a).complex b).X j),
        (((C f).hom.app b).f n)
          (L.degree (cone f) b n (tmul T (cone f) b a i j n h x y)) =
        (L.degree N b n (tmul T N b a i j n h x.1 y),
          L.degree M b (n + 1) (tmul T M b a (i + 1) j (n + 1) (by omega) x.2 y)))

end Specs.DerivedFormalization.DG.BimoduleTensorComparisons
