import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.BimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedTriangles
import Mathlib.CategoryTheory.Shift.Adjunction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w z vA

namespace Specs.DerivedFormalization.DG.LocalizedBimoduleExactness

open _root_.DerivedFormalization
open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance)
open KProjective (isKProjective)
open HomComplex (homotopyClass)
open ShiftCone (shift shiftMap cone coneInclusion coneProjection)
open BalancedTensor (bimodule tmul)
open BimoduleAdjunction
  (TensorModel InternalHomModel OrdinaryCurryFamily StrictLaws ordinaryTensor ordinaryHom)

noncomputable section

set_option maxHeartbeats 1200000

variable {k : Type u} [CommRing k]

local notation "K" => HomComplex.homotopyCategory
local notation "D" => Derived.derivedCategory
local notation "Q" => Derived.quotient

/-- The class of a strict map in the fixed category, with its category instance explicit. -/
abbrev classOfMap {A : DGCategoryModel.{u,v,w} k} (_h : HomotopyCategoryLaws A)
    {M N : RightDGModuleModel A} (f : M ⟶ N) :
    @Quiver.Hom (K A) (Derived.homotopyCategoryStruct A).toQuiver M N :=
  homotopyClass f

/-- G08's cone triangulations on the fixed homotopy category and localization. -/
structure ConeLocalization (A : DGCategoryModel.{u,v,w} k) (h : HomotopyCategoryLaws A) where
  shiftK : letI := Derived.homotopyCategory A h; HasShift (K A) ℤ
  addK : letI := Derived.homotopyCategory A h; Preadditive (K A)
  zeroK : letI := Derived.homotopyCategory A h; HasZeroObject (K A)
  addShiftK :
    letI := Derived.homotopyCategory A h
    letI := shiftK
    letI := addK
    ∀ n : ℤ, (shiftFunctor (K A) n).Additive
  shiftObj (M : RightDGModuleModel A) (n : ℤ) :
    letI := Derived.homotopyCategory A h
    letI := shiftK
    (shiftFunctor (K A) n).obj M = shift M n
  shiftMap {M N : RightDGModuleModel A} (f : M ⟶ N) (n : ℤ) :
    letI := Derived.homotopyCategory A h
    letI := shiftK
    HEq ((shiftFunctor (K A) n).map (classOfMap h f)) (classOfMap h (ShiftCone.shiftMap n f))
  homGroup :
    ∀ X Y : K A,
      HEq (addK.homGroup X Y)
        (inferInstance : AddCommGroup (Basic.h0Hom (HomComplex.homComplex X Y)))
  trianglesK :
    letI := Derived.homotopyCategory A h
    letI := shiftK
    letI := addK
    letI := zeroK
    letI := addShiftK
    Pretriangulated (K A)
  isTriangulatedK :
    letI := Derived.homotopyCategory A h
    letI := shiftK
    letI := addK
    letI := zeroK
    letI := addShiftK
    letI := trianglesK
    IsTriangulated (K A)
  shiftD : letI := derivedCategoryInstance A h; HasShift (D A h) ℤ
  addD : letI := derivedCategoryInstance A h; Preadditive (D A h)
  zeroD : letI := derivedCategoryInstance A h; HasZeroObject (D A h)
  addShiftD :
    letI := derivedCategoryInstance A h
    letI := shiftD
    letI := addD
    ∀ n : ℤ, (shiftFunctor (D A h) n).Additive
  quotientShift :
    letI := Derived.homotopyCategory A h
    letI := derivedCategoryInstance A h
    letI := shiftK
    letI := shiftD
    let QA : K A ⥤ D A h := Q A h
    QA.CommShift ℤ
  trianglesD :
    letI := derivedCategoryInstance A h
    letI := shiftD
    letI := addD
    letI := zeroD
    letI := addShiftD
    Pretriangulated (D A h)
  isTriangulated :
    letI := derivedCategoryInstance A h
    letI := shiftD
    letI := addD
    letI := zeroD
    letI := addShiftD
    letI := trianglesD
    IsTriangulated (D A h)
  quotientTriangulated :
    letI := Derived.homotopyCategory A h
    letI := derivedCategoryInstance A h
    letI := shiftK
    letI := addK
    letI := zeroK
    letI := addShiftK
    letI := trianglesK
    letI := shiftD
    letI := addD
    letI := zeroD
    letI := addShiftD
    letI := trianglesD
    let QA : K A ⥤ D A h := Q A h
    letI : QA.CommShift ℤ := quotientShift
    QA.IsTriangulated
  coneTriangles :
    letI := Derived.homotopyCategory A h
    letI := shiftK
    letI := addK
    letI := zeroK
    letI := addShiftK
    letI := trianglesK
    ∀ T : Triangle (K A), T ∈ distTriang (K A) ↔
      ∃ (M N : RightDGModuleModel A) (f : M ⟶ N),
        Nonempty (T ≅ DerivedTriangles.coneTriangle h shiftK (shiftObj M 1) f)
  localizedConeTriangles :
    letI := Derived.homotopyCategory A h
    letI := derivedCategoryInstance A h
    letI := shiftK
    letI := shiftD
    letI := addD
    letI := zeroD
    letI := addShiftD
    let QA : K A ⥤ D A h := Q A h
    letI : QA.CommShift ℤ := quotientShift
    letI := trianglesD
    (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
      QA.mapTriangle.obj (DerivedTriangles.coneTriangle h shiftK (shiftObj M 1) f) ∈
        distTriang (D A h)) ∧
    (∀ T : Triangle (D A h), T ∈ distTriang (D A h) →
      ∃ (M N : RightDGModuleModel A) (_ : isKProjective M) (_ : isKProjective N) (f : M ⟶ N),
        Nonempty (T ≅ QA.mapTriangle.obj (DerivedTriangles.coneTriangle h shiftK (shiftObj M 1) f)))

/-- The localization's shift comparison with the actual signed strict shift. -/
def ConeLocalization.onShift {A : DGCategoryModel.{u,v,w} k}
    {h : HomotopyCategoryLaws A} (c : ConeLocalization A h) (X : RightDGModuleModel A) (n : ℤ) :
    letI := Derived.homotopyCategory A h
    letI := derivedCategoryInstance A h
    letI := c.shiftD
    (Q A h).obj (shift X n) ≅ (shiftFunctor (D A h) n).obj ((Q A h).obj X) := by
  letI := Derived.homotopyCategory A h
  letI := derivedCategoryInstance A h
  letI := c.shiftK
  letI := c.shiftD
  let QA : K A ⥤ D A h := Q A h
  letI : QA.CommShift ℤ := c.quotientShift
  exact eqToIso (congrArg QA.obj (c.shiftObj X n).symm) ≪≫ (QA.commShiftIso n).app X

/-- Strict shift and cone isomorphisms respecting the two cone maps. In
particular the negative of the positive projection gives the last arrow
with the sign of the G04 and G08 triangles. -/
structure ShiftConeComparisons
    {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}
    (F : RightDGModuleModel A ⥤ RightDGModuleModel B) where
  shiftIso (M : RightDGModuleModel A) (n : ℤ) : F.obj (shift M n) ≅ shift (F.obj M) n
  coneIso {M N : RightDGModuleModel A} (f : M ⟶ N) : F.obj (cone f) ≅ cone (F.map f)
  shiftNaturality {M N : RightDGModuleModel A} (f : M ⟶ N) (n : ℤ) :
    F.map (ShiftCone.shiftMap n f) ≫ (shiftIso N n).hom =
      (shiftIso M n).hom ≫ ShiftCone.shiftMap n (F.map f)
  inclusion {M N : RightDGModuleModel A} (f : M ⟶ N) :
    F.map (coneInclusion f) ≫ (coneIso f).hom = coneInclusion (F.map f)
  projection {M N : RightDGModuleModel A} (f : M ⟶ N) :
    F.map (coneProjection f) ≫ (shiftIso M 1).hom = (coneIso f).hom ≫ coneProjection (F.map f)

section Models
open HomComplex (component gradedHom)

variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
variable {T : bimodule A B} {L : TensorModel T} {G : InternalHomModel T}

/-- The tensor comparisons are determined on homogeneous pure tensors. -/
def TensorComparisonLaws (S : ShiftConeComparisons (ordinaryTensor.{u,v,w,z} L)) : Prop :=
  (∀ (M : RightDGModuleModel A) (s : ℤ) (a : A.Obj) (b : B.Obj) (i j r : ℤ)
    (h : i+j=r) (x : ((shift M s).complex a).X i) (y : ((T.obj a).complex b).X j),
    (((S.shiftIso M s).hom.app b).f r)
      (L.degree (shift M s) b r (tmul T (shift M s) b a i j r h x y)) =
        L.degree M b (r+s) (tmul T M b a (i+s) j (r+s) (by omega) x y)) ∧
  ∀ {M N : RightDGModuleModel A} (f : M ⟶ N) (a : A.Obj) (b : B.Obj) (i j r : ℤ)
    (h : i+j=r) (x : ((cone f).complex a).X i) (y : ((T.obj a).complex b).X j),
    (((S.coneIso f).hom.app b).f r)
      (L.degree (cone f) b r (tmul T (cone f) b a i j r h x y)) =
      (L.degree N b r (tmul T N b a i j r h x.1 y),
        L.degree M b (r+1) (tmul T M b a (i+1) j (r+1) (by omega) x.2 y))

/-- The Hom comparisons only reindex component maps and split the two target
coordinates of a cone. -/
def HomComparisonLaws (S : ShiftConeComparisons (ordinaryHom.{u,v,w,z} G)) : Prop :=
  (∀ (N : RightDGModuleModel B) (s : ℤ) (a : A.Obj) (r : ℤ)
    (g : gradedHom (T.obj a) N (r+s)) (b : B.Obj) (i j : ℤ) (h : i+r=j),
    component ((G.objectwise (shift N s) a).inv.f r
      (((S.shiftIso N s).inv.app a).f r ((G.objectwise N a).hom.f (r+s) g))) b i j h =
        component g b i (j+s) (by omega)) ∧
  ∀ {M N : RightDGModuleModel B} (f : M ⟶ N) (a : A.Obj) (r : ℤ)
    (g : gradedHom (T.obj a) (cone f) r) (b : B.Obj) (i j : ℤ) (h : i+r=j)
    (x : ((T.obj a).complex b).X i),
    let y := ((S.coneIso f).hom.app a).f r ((G.objectwise (cone f) a).hom.f r g)
    component ((G.objectwise N a).inv.f r y.1) b i j h x = (component g b i j h x).1 ∧
    component ((G.objectwise M a).inv.f (r+1) y.2) b i (j+1) (by omega) x =
      (component g b i j h x).2

end Models

section Descent

variable {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}
variable (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B)

/-- A lift to the fixed category of homotopy classes with the specified action
on strict objects and maps. -/
structure ClassLift (F : RightDGModuleModel A ⥤ RightDGModuleModel B) where
  functor : @Functor (K A) (Derived.homotopyCategory A hA) (K B) (Derived.homotopyCategory B hB)
  obj (X : RightDGModuleModel A) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    functor.obj (X : K A) = F.obj X
  map {X Y : RightDGModuleModel A} (f : X ⟶ Y) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    functor.map (classOfMap hA f) ≫ eqToHom (obj Y) =
      eqToHom (obj X) ≫ classOfMap hB (F.map f)

variable (F : RightDGModuleModel A ⥤ RightDGModuleModel B)
  (H : RightDGModuleModel B ⥤ RightDGModuleModel A) (a : F ⊣ H)

/-- The named homotopy and derived functors, and the compatibility of their
adjunctions with the strict unit, counit and localization comparison. -/
structure DescentData where
  FK : ClassLift hA hB F
  HK : ClassLift hB hA H
  aK :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    FK.functor ⊣ HK.functor
  unitK (X : RightDGModuleModel A) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    aK.unit.app (X : K A) ≫ HK.functor.map (eqToHom (FK.obj X)) ≫ eqToHom (HK.obj (F.obj X)) =
      classOfMap hA (a.unit.app X)
  counitK (Y : RightDGModuleModel B) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    aK.counit.app (Y : K B) =
      FK.functor.map (eqToHom (HK.obj Y)) ≫ eqToHom (FK.obj (H.obj Y)) ≫
        classOfMap hB (a.counit.app Y)
  J :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    D A hA ⥤ K A
  aJ :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    J ⊣ Q A hA
  projective (X : D A hA) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    isKProjective (J.obj X)
  HD :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    D B hB ⥤ D A hA
  b :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    Q B hB ⋙ HD ≅ HK.functor ⋙ Q A hA
  aD :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    (J ⋙ FK.functor) ⋙ Q B hB ⊣ HD
  unitD (X : D A hA) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    aD.unit.app X =
      aJ.unit.app X ≫ (Q A hA).map (aK.unit.app (J.obj X)) ≫ b.inv.app (FK.functor.obj (J.obj X))
  counitD (Y : K B) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    aD.counit.app ((Q B hB).obj Y) =
      ((J ⋙ FK.functor) ⋙ Q B hB).map (b.hom.app Y) ≫
        (Q B hB).map (FK.functor.map (aJ.counit.app (HK.functor.obj Y))) ≫
        (Q B hB).map (aK.counit.app Y)

variable {hA hB F H a} (d : DescentData hA hB F H a)

/-- The left derived functor applies the homotopy tensor after resolution. -/
abbrev DescentData.LD :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    D A hA ⥤ D B hB :=
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  (d.J ⋙ d.FK.functor) ⋙ Q B hB

/-- Comparison of the right derived functor on any represented module. -/
abbrev DescentData.homRepresentative (N : RightDGModuleModel B) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    d.HD.obj ((Q B hB).obj (N : K B)) ≅ (Q A hA).obj (H.obj N : K A) :=
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  d.b.app N ≪≫ (Q A hA).mapIso (eqToIso (d.HK.obj N))

/-- The resolution counit defines the comparison of the left derived functor
on representatives. This map is an isomorphism on K-projective modules. -/
abbrev DescentData.tensorRepresentative (P : RightDGModuleModel A) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    d.LD.obj ((Q A hA).obj (P : K A)) ⟶ (Q B hB).obj (F.obj P : K B) :=
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  (Q B hB).map (d.FK.functor.map (d.aJ.counit.app (P : K A)) ≫ eqToHom (d.FK.obj P))

/-- Exactness for the specified derived adjunction, with shift comparisons
agreeing with the signed strict comparisons after localization. -/
def DescentData.IsExact (S : ShiftConeComparisons F) (R : ShiftConeComparisons H) : Prop :=
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  let QA : K A ⥤ D A hA := Q A hA
  let QB : K B ⥤ D B hB := Q B hB
  let adj : d.LD ⊣ d.HD := d.aD
  ∃ (cA : ConeLocalization A hA) (cB : ConeLocalization B hB),
    letI := cA.shiftD
    letI := cA.addD
    letI := cA.zeroD
    letI := cA.addShiftD
    letI := cA.trianglesD
    letI := cB.shiftD
    letI := cB.addD
    letI := cB.zeroD
    letI := cB.addShiftD
    letI := cB.trianglesD
    ∃ (fS : d.LD.CommShift ℤ) (gS : d.HD.CommShift ℤ),
      letI := fS
      letI := gS
      d.LD.IsTriangulated ∧ d.HD.IsTriangulated ∧ adj.CommShift ℤ ∧
      (∀ P : RightDGModuleModel A, isKProjective P → IsIso (d.tensorRepresentative P)) ∧
      (∀ (N : RightDGModuleModel B) (s : ℤ),
        d.HD.map (cB.onShift N s).hom ≫ (d.HD.commShiftIso s).hom.app (QB.obj N) ≫
          (shiftFunctor (D A hA) s).map (d.homRepresentative N).hom =
        (d.homRepresentative (shift N s)).hom ≫ QA.map (classOfMap hA (R.shiftIso N s).hom) ≫
          (cA.onShift (H.obj N) s).hom) ∧
      ∀ (P : RightDGModuleModel A) (s : ℤ),
        isKProjective P → isKProjective (shift P s) →
        d.LD.map (cA.onShift P s).hom ≫ (d.LD.commShiftIso s).hom.app (QA.obj P) ≫
          (shiftFunctor (D B hB) s).map (d.tensorRepresentative P) =
        d.tensorRepresentative (shift P s) ≫ QB.map (classOfMap hB (S.shiftIso P s).hom) ≫
          (cB.onShift (F.obj P) s).hom

end Descent

/-- At a common adequate coefficient bound, the signed strict tensor and Hom
form an exact derived adjunction with the specified comparisons on modules. -/
def LocalizedExactness : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w z,w} k}
    {B : DGCategoryModel.{u,max v w z,z} k} {T : bimodule A B}
    (L : TensorModel T) (G : InternalHomModel T)
    (E : OrdinaryCurryFamily.{u,v,w,z} L G)
    (a : ordinaryTensor.{u,v,w,z} L ⊣ ordinaryHom.{u,v,w,z} G),
    StrictLaws.{u,v,w,z} L G E a →
    (∀ o : A.Obj, isKProjective (T.obj o)) →
    ∀ (S : ShiftConeComparisons (ordinaryTensor.{u,v,w,z} L))
      (R : ShiftConeComparisons (ordinaryHom.{u,v,w,z} G)),
      TensorComparisonLaws.{u,v,w,z} S → HomComparisonLaws.{u,v,w,z} R →
      ∀ (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B)
        (d : DescentData hA hB (ordinaryTensor.{u,v,w,z} L) (ordinaryHom.{u,v,w,z} G) a),
        d.IsExact S R

end

end Specs.DerivedFormalization.DG.LocalizedBimoduleExactness
