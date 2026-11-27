import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.BimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedCoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedTriangles
import Mathlib.CategoryTheory.Shift.Adjunction

open CategoryTheory
open _root_.DerivedFormalization

universe u v w vA z t p

namespace Specs.DerivedFormalization.DG.DerivedBimoduleAdjunction

open BalancedTensor (RightModule bimodule)
open BimoduleAdjunction (InternalHomModel TensorModel ordinaryTensor ordinaryHom OrdinaryCurryFamily)
open CoefficientLift (liftCategory)
open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance)
open KProjective (isKProjective)

noncomputable section

variable {k : Type u} [CommRing k]

/-- Descent of a strict functor, allowing independent object universes. -/
structure LocalizedFunctor
    {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}
    (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B)
    (F : RightDGModuleModel A ⥤ RightDGModuleModel B) where
  homotopy : @Functor _ (Derived.homotopyCategory A hA) _ (Derived.homotopyCategory B hB)
  derived : @Functor _ (derivedCategoryInstance A hA) _ (derivedCategoryInstance B hB)
  obj (X : RightDGModuleModel A) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    homotopy.obj X = F.obj X
  map {X Y : RightDGModuleModel A} (f : X ⟶ Y) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    HEq (homotopy.map (HomComplex.homotopyClass f)) (HomComplex.homotopyClass (F.map f))
  square :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    Derived.quotient A hA ⋙ derived ≅ homotopy ⋙ Derived.quotient B hB
  preservesQuasiIsomorphisms {X Y : RightDGModuleModel A} (f : X ⟶ Y) :
    Module.quasiIsomorphism f → Module.quasiIsomorphism (F.map f)

section Native

variable {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}
variable {T : bimodule A B}

/-- Put a mixed-output module over the coefficient lift of its arrow category.
Each arrow acts through its original value and each term is lifted by `ULift`. -/
@[reducible] def placeHom :
    RightModule.{u,vA,w,p} A ⥤ RightDGModuleModel (liftCategory.{u,vA,w,p} A) where
  obj M :=
    { complex := fun a => Yoneda.liftComplex.{u,p,vA} (M.complex a)
      act := fun i j n h =>
        ((M.act i j n h).compl₁₂ ULift.moduleEquiv.toLinearMap ULift.moduleEquiv.toLinearMap)
          |>.compr₂ ULift.moduleEquiv.symm.toLinearMap
      act_id := fun a i x => ULift.ext (M.act_id a i x.down)
      act_assoc := fun i j l x f g => ULift.ext (M.act_assoc i j l x.down f.down g.down)
      leibniz := fun i j n h x f => ULift.ext (M.leibniz i j n h x.down f.down) }
  map f :=
    { app := fun a =>
        ((ModuleCat.uliftFunctor.{vA,p} k).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (f.app a)
      comm_act := fun i j n h x f' => ULift.ext (f.comm_act i j n h x.down f'.down) }
  map_id M := RightDGModuleModel.hom_ext fun a =>
    ((ModuleCat.uliftFunctor.{vA,p} k).mapHomologicalComplex (ComplexShape.up ℤ)).map_id
      (M.complex a)
  map_comp f g := RightDGModuleModel.hom_ext fun a =>
    ((ModuleCat.uliftFunctor.{vA,p} k).mapHomologicalComplex (ComplexShape.up ℤ)).map_comp
      (f.app a) (g.app a)

/-- A quasi-isomorphism induces quasi-isomorphisms on the actual mixed Hom
complexes before the output terms are transported. -/
def NativeHomPreservesQuasiIsomorphisms : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}
    {T : bimodule A B} (G : InternalHomModel T),
    (∀ a, isKProjective (T.obj a)) →
    ∀ {N N' : RightDGModuleModel B} (f : N ⟶ N'), Module.quasiIsomorphism f →
      ∀ a, QuasiIso ((G.functor.map f).app a)

/-- Descend the mixed Hom output, with its transported action, from the
original B localization. No enlargement of the domain is needed. -/
def NativeHomDescent : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}
    {T : bimodule A B} (G : InternalHomModel T),
    (∀ a, isKProjective (T.obj a)) →
    ∀ (hB : HomotopyCategoryLaws B) (hA : HomotopyCategoryLaws (liftCategory.{u,vA,w,max v z} A)),
      Nonempty (LocalizedFunctor hB hA (G.functor ⋙ placeHom.{u,w,vA,max v z}))

end Native

/-- The projectivity argument uses the full module categories at one
adequate bound. The ordinary tensor and Hom are the models in G13Adjunction. -/
def TensorPreservesKProjectives : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w z,w} k}
    {B : DGCategoryModel.{u,max v w z,z} k} {T : bimodule A B}
    (L : TensorModel T) (G : InternalHomModel T)
    (_E : OrdinaryCurryFamily.{u,v,w,z} L G),
    (∀ a, isKProjective (T.obj a)) →
    ∀ P, isKProjective P → isKProjective ((ordinaryTensor.{u,v,w,z} L).obj P)

section DerivedData

open DerivedKProjective (kProjectiveObjects restrictedLocalization replacementIso)

local notation "K" => HomComplex.homotopyCategory
local notation "D" => Derived.derivedCategory
local notation "Q" => Derived.quotient

variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
variable {T : bimodule A B} (L : TensorModel T) (G : InternalHomModel T)
variable (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B)

/-- The functors, adjunctions and comparison on projective representatives. -/
structure DerivedAdjunctionData where
  tensorH : @Functor (K A) (Derived.homotopyCategory A hA)
    (K B) (Derived.homotopyCategory B hB)
  hom : LocalizedFunctor hB hA (ordinaryHom.{u,v,w,z} G)
  resolution : @Functor (D A hA) (derivedCategoryInstance A hA)
    (K A) (Derived.homotopyCategory A hA)
  resolutionAdjunction :
    letI := Derived.homotopyCategory A hA
    letI := derivedCategoryInstance A hA
    resolution ⊣ Q A hA
  homotopyAdjunction :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    tensorH ⊣ hom.homotopy
  adjunction :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    (resolution ⋙ tensorH) ⋙ Q B hB ⊣ hom.derived
  tensorObj (P : RightDGModuleModel A) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    tensorH.obj P = (ordinaryTensor.{u,v,w,z} L).obj P
  tensorSquare :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    (kProjectiveObjects A).ι ⋙ Q A hA ⋙ ((resolution ⋙ tensorH) ⋙ Q B hB) ≅
      (kProjectiveObjects A).ι ⋙ tensorH ⋙ Q B hB

variable {L G hA hB} (d : DerivedAdjunctionData.{u,v,w,z} L G hA hB)

/-- The left functor computed on the chosen resolution. -/
abbrev DerivedAdjunctionData.tensor :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    D A hA ⥤ D B hB := by
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  exact (d.resolution ⋙ d.tensorH) ⋙ Q B hB

/-- The comparison at any K-projective strict module. -/
def DerivedAdjunctionData.onProjective (P : RightDGModuleModel A) (hp : isKProjective P) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    d.tensor.obj ((Q A hA).obj P) ≅ (Q B hB).obj ((ordinaryTensor.{u,v,w,z} L).obj P) := by
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  exact d.tensorSquare.app ⟨P, hp⟩ ≪≫ eqToIso (congrArg (Q B hB).obj (d.tensorObj P))

/-- A replacement augments the tensor comparison by the inverse of its
localized image. -/
def DerivedAdjunctionData.onReplacement {P X : RightDGModuleModel A}
    (p : P ⟶ X) (hP : isKProjective P) (hp : Module.quasiIsomorphism p) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    d.tensor.obj ((Q A hA).obj X) ≅ (Q B hB).obj ((ordinaryTensor.{u,v,w,z} L).obj P) := by
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  exact (d.tensor.mapIso (replacementIso hA p hp)).symm ≪≫ d.onProjective P hP

/-- The comparison on all represented inputs to descended Hom. -/
def DerivedAdjunctionData.onInput (M : RightDGModuleModel B) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    d.hom.derived.obj ((Q B hB).obj M) ≅ (Q A hA).obj ((ordinaryHom.{u,v,w,z} G).obj M) := by
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  exact d.hom.square.app M ≪≫ eqToIso (congrArg (Q A hA).obj (d.hom.obj M))

/-- The adjunction on homotopy classes uses the original evaluation unit and
counit. The derived adjunction uses the specified resolution and descent. -/
def DerivedAdjunctionData.Realizes
    (adj : ordinaryTensor.{u,v,w,z} L ⊣ ordinaryHom.{u,v,w,z} G) : Prop :=
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  let QA := Q A hA
  let QB := Q B hB
  (∀ X : D A hA, isKProjective (d.resolution.obj X)) ∧
  (∀ {X Y : RightDGModuleModel A} (f : X ⟶ Y),
    HEq (d.tensorH.map (HomComplex.homotopyClass f))
      (HomComplex.homotopyClass ((ordinaryTensor.{u,v,w,z} L).map f))) ∧
  (∀ X : RightDGModuleModel A,
    HEq (d.homotopyAdjunction.unit.app X) (HomComplex.homotopyClass (adj.unit.app X))) ∧
  (∀ Y : RightDGModuleModel B,
    HEq (d.homotopyAdjunction.counit.app Y) (HomComplex.homotopyClass (adj.counit.app Y))) ∧
  (∀ X : D A hA,
    d.adjunction.unit.app X = d.resolutionAdjunction.unit.app X ≫
      QA.map (d.homotopyAdjunction.unit.app (d.resolution.obj X)) ≫
      d.hom.square.inv.app (d.tensorH.obj (d.resolution.obj X))) ∧
  (∀ Y : K B,
    d.adjunction.counit.app (QB.obj Y) =
      d.tensor.map (d.hom.square.hom.app Y) ≫
        QB.map (d.tensorH.map (d.resolutionAdjunction.counit.app (d.hom.homotopy.obj Y))) ≫
        QB.map (d.homotopyAdjunction.counit.app Y)) ∧
  ∀ a : A.Obj, Nonempty (d.tensor.obj (QA.obj (Yoneda.representable a)) ≅ QB.obj (T.obj a))

end DerivedData

/-- The adjunction of the given underived models at a common adequate bound. -/
def DerivedAdjunctionFor
    {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
    {T : bimodule A B} (L : TensorModel T) (G : InternalHomModel T)
    (adj : ordinaryTensor.{u,v,w,z} L ⊣ ordinaryHom.{u,v,w,z} G) : Prop :=
  ∀ (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B),
    ∃ d : DerivedAdjunctionData.{u,v,w,z} L G hA hB, d.Realizes adj

/-- The adjunction at a common adequate bound. Its right adjoint descends
the ordinary Hom functor, and each strict K-projective replacement computes
the left adjoint. The comparison at K-projective objects is natural on the
full homotopy subcategory. -/
def DerivedAdjunctionAt : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w z,w} k}
    {B : DGCategoryModel.{u,max v w z,z} k} {T : bimodule A B}
    (L : TensorModel T) (G : InternalHomModel T)
    (E : OrdinaryCurryFamily.{u,v,w,z} L G)
    (adj : ordinaryTensor.{u,v,w,z} L ⊣ ordinaryHom.{u,v,w,z} G),
    BimoduleAdjunction.StrictLaws.{u,v,w,z} L G E adj →
    (∀ a, isKProjective (T.obj a)) →
    DerivedAdjunctionFor.{u,v,w,z} L G adj

section CommonBound

universe s

open AmbientDerived (category strictInput)
open BimoduleAdjunction (asMixed BimoduleLiftLaws ModuleEquiv restrictLifted)

/-- Apply the derived construction to the representation of the original
bimodule, using the common coefficient bound of the signed adjunction. -/
def AmbientDerivedAdjunction : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,vA,w} k)
    (B : DGCategoryModel.{u,v,z} k) (T : bimodule A B),
    let A' := category.{u,vA,w,max v z t} A
    let B' := category.{u,v,z,max vA w t} B
    ∃ (S : bimodule A' B')
      (comparison : ∀ a, ModuleEquiv (asMixed (T.obj a))
        (restrictLifted.{u,v,z,max vA v w z t,max vA w z t} (asMixed (S.obj a))))
      (L : TensorModel S) (G : InternalHomModel S)
      (E : OrdinaryCurryFamily.{u,max vA v t,w,z} L G)
      (adj : ordinaryTensor.{u,max vA v t,w,z} L ⊣ ordinaryHom.{u,max vA v t,w,z} G),
      BimoduleLiftLaws.{u,v,w,vA,z,t} comparison ∧
      BimoduleAdjunction.StrictLaws.{u,max vA v t,w,z} L G E adj ∧
      ((∀ a, isKProjective (S.obj a)) → DerivedAdjunctionFor.{u,max vA v t,w,z} L G adj)

/-- At a common adequate bound the projectivity of the represented bimodule
is preserved by any further coefficient enlargement. -/
def AmbientProjectivityTransition : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,vA,w} k}
    {B : DGCategoryModel.{u,v,z} k} (T : bimodule A B),
    (∀ a, isKProjective ((strictInput.{u,v,z,max vA w t} B).obj (T.obj a))) →
    ∀ a, isKProjective ((strictInput.{u,v,z,max vA w t s} B).obj (T.obj a))

/-- A native premise also transports if the original B coefficient universe
already contains the B objects. -/
def AdequateNativeProjectivityTransition : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,vA,w} k}
    {B : DGCategoryModel.{u,max v z,z} k} (T : bimodule A B),
    (∀ a, isKProjective (T.obj a)) →
    ∀ a, isKProjective ((strictInput.{u,max v z,z,max vA w t} B).obj (T.obj a))

end CommonBound


/-- Internal Hom commutes with the signed shifts and cones. The shift
compares the same homogeneous components at their reindexed degrees, and
the cone comparison respects the inclusion and the positive projection. -/
def HomShiftConeComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w z,w} k}
    {B : DGCategoryModel.{u,max v w z,z} k} {T : bimodule A B} (G : InternalHomModel T),
    let H := ordinaryHom.{u,v,w,z} G
    ∃ (S : ∀ (N : RightDGModuleModel B) (s : ℤ),
        ShiftCone.shift (H.obj N) s ≅ H.obj (ShiftCone.shift N s))
      (C : ∀ {M N : RightDGModuleModel B} (f : M ⟶ N),
        H.obj (ShiftCone.cone f) ≅ ShiftCone.cone (H.map f)),
      (∀ (N : RightDGModuleModel B) (s : ℤ) (a : A.Obj) (r : ℤ)
        (g : HomComplex.gradedHom (T.obj a) N (r+s))
        (b : B.Obj) (i j : ℤ) (h : i+r=j),
        HomComplex.component ((G.objectwise (ShiftCone.shift N s) a).inv.f r
          (((S N s).hom.app a).f r ((G.objectwise N a).hom.f (r+s) g))) b i j h =
            HomComplex.component g b i (j+s) (by omega)) ∧
      (∀ {N N' : RightDGModuleModel B} (f : N ⟶ N') (s : ℤ),
        ShiftCone.shiftMap s (H.map f) ≫ (S N' s).hom =
          (S N s).hom ≫ H.map (ShiftCone.shiftMap s f)) ∧
      ∀ {M N : RightDGModuleModel B} (f : M ⟶ N),
        H.map (ShiftCone.coneInclusion f) ≫ (C f).hom = ShiftCone.coneInclusion (H.map f) ∧
        (C f).hom ≫ ShiftCone.coneProjection (H.map f) ≫ (S M 1).hom =
          H.map (ShiftCone.coneProjection f)


section Exactness

open CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomComplex (homotopyClass)
open ShiftCone (shift shiftMap cone coneInclusion coneProjection)

local notation "K" => HomComplex.homotopyCategory
local notation "D" => Derived.derivedCategory
local notation "Q" => Derived.quotient

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
    HEq ((shiftFunctor (K A) n).map (homotopyClass f)) (ShiftCone.shiftMap n f |> homotopyClass)
  trianglesK :
    letI := Derived.homotopyCategory A h
    letI := shiftK
    letI := addK
    letI := zeroK
    letI := addShiftK
    Pretriangulated (K A)
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

open BalancedTensor (tmul)
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

variable {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
variable (d : DerivedAdjunctionData.{u,v,w,z} L G hA hB)

/-- Natural shift comparisons and exactness of the two functors of the
same derived adjunction. The shift maps on representatives are the
localized strict comparisons. -/
def DerivedAdjunctionData.IsExact : Prop :=
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  let QA := Q A hA
  let QB := Q B hB
  let FD : D A hA ⥤ D B hB := d.tensor
  let GD : D B hB ⥤ D A hA := d.hom.derived
  let adj : FD ⊣ GD := d.adjunction
  let F := ordinaryTensor.{u,v,w,z} L
  let G₀ := ordinaryHom.{u,v,w,z} G
  ∃ (cA : ConeLocalization A hA) (cB : ConeLocalization B hB)
    (S : ShiftConeComparisons F) (R : ShiftConeComparisons G₀),
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
    TensorComparisonLaws.{u,v,w,z} S ∧ HomComparisonLaws.{u,v,w,z} R ∧
    ∃ (fS : FD.CommShift ℤ) (gS : GD.CommShift ℤ),
      letI := fS
      letI := gS
      FD.IsTriangulated ∧ GD.IsTriangulated ∧ adj.CommShift ℤ ∧
      (∀ (N : RightDGModuleModel B) (n : ℤ),
        GD.map (cB.onShift N n).hom ≫ (GD.commShiftIso n).hom.app (QB.obj N) ≫
          (shiftFunctor (D A hA) n).map (d.onInput N).hom =
        (d.onInput (shift N n)).hom ≫ QA.map (homotopyClass (R.shiftIso N n).hom) ≫
          (cA.onShift (G₀.obj N) n).hom) ∧
      ∀ (P : RightDGModuleModel A) (n : ℤ) (hP : isKProjective P)
        (hPn : isKProjective (shift P n)),
        FD.map (cA.onShift P n).hom ≫ (FD.commShiftIso n).hom.app (QA.obj P) ≫
          (shiftFunctor (D B hB) n).map (d.onProjective P hP).hom =
        (d.onProjective (shift P n) hPn).hom ≫ QB.map (homotopyClass (S.shiftIso P n).hom) ≫
          (cB.onShift (F.obj P) n).hom

end Models
end Exactness

section CommonModels

open BalancedTensor (left tmul)
open BimoduleAdjunction
  (StrictLaws restrictLifted asMixed ModuleEquiv BimoduleLiftLaws)

local notation "K" => HomComplex.homotopyCategory
local notation "D" => Derived.derivedCategory
local notation "Q" => Derived.quotient

/-- Specified signed tensor and Hom on two full module categories at a common
adequate coefficient bound. -/
structure SignedModels
    {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
    (T : bimodule A B) where
  tensor : TensorModel T
  hom : InternalHomModel T
  curry : OrdinaryCurryFamily.{u,v,w,z} tensor hom
  adjunction : ordinaryTensor.{u,v,w,z} tensor ⊣ ordinaryHom.{u,v,w,z} hom
  laws : StrictLaws.{u,v,w,z} tensor hom curry adjunction

section Representables

variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
variable {T : bimodule A B} {L : TensorModel T} {G : InternalHomModel T}
variable {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
variable (d : DerivedAdjunctionData.{u,v,w,z} L G hA hB)

/-- The projective calculation uses the resolution augmentation. On a
representable, its strict evaluation sends `f ⊗ x` to the left action of `f`. -/
def DerivedAdjunctionData.ComputesRepresentatives : Prop :=
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  let QB := Q B hB
  (∀ (P : RightDGModuleModel A) (hp : isKProjective P),
    d.tensorSquare.hom.app ⟨P, hp⟩ = QB.map (d.tensorH.map (d.resolutionAdjunction.counit.app P))) ∧
  ∀ a : A.Obj,
    let h := Yoneda.representable (A := A) a
    ∃ (e : (ordinaryTensor.{u,v,w,z} L).obj h ≅ T.obj a),
      (∀ (b : B.Obj) (c : A.Obj) (i j n : ℤ) (he : i+j=n)
        (f : (A.hom c a).X i) (x : ((T.obj c).complex b).X j),
        (e.hom.app b).f n (L.degree h b n (tmul T h b c i j n he f x)) = left T b i j n he f x) ∧
      ∀ (b : B.Obj) (n : ℤ) (x : ((T.obj a).complex b).X n),
        (e.inv.app b).f n x = L.degree h b n (tmul T h b a 0 n n (zero_add n) (A.id a) x)

end Representables

/-- Both functors of the derived adjunction are exact with the given
signed strict comparisons. -/
def ExactDerivedAdjunctionAt : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w z,w} k}
    {B : DGCategoryModel.{u,max v w z,z} k} {T : bimodule A B}
    (m : SignedModels.{u,v,w,z} T),
    (∀ a, isKProjective (T.obj a)) →
    ∀ (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B),
      ∃ d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB,
        d.Realizes m.adjunction ∧ d.ComputesRepresentatives ∧ d.IsExact

section Ambient

variable {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}

/-- The representation of the given bimodule at a common adequate bound,
including the transport of its homogeneous left action. -/
structure AmbientSignedModels (T : bimodule A B) where
  bimodule : BalancedTensor.bimodule
    (AmbientDerived.category.{u,vA,w,max v z t} A)
    (AmbientDerived.category.{u,v,z,max vA w t} B)
  comparison (a : A.Obj) :
    ModuleEquiv (asMixed (T.obj a))
      (restrictLifted.{u,v,z,max vA v w z t,max vA w z t} (asMixed (bimodule.obj a)))
  comparisonLaws : BimoduleLiftLaws.{u,v,w,vA,z,t} comparison
  models : SignedModels.{u,max vA v t,w,z} bimodule

end Ambient

/-- The exact derived adjunction for the represented original bimodule.
The K-projectivity tests range over the whole ambient B-module category. -/
def AmbientExactDerivedAdjunction : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,vA,w} k}
    {B : DGCategoryModel.{u,v,z} k} (T : bimodule A B),
    ∃ m : AmbientSignedModels.{u,v,w,vA,z,t} T,
      (∀ a, isKProjective (m.bimodule.obj a)) →
      ∀ (hA : HomotopyCategoryLaws (AmbientDerived.category.{u,vA,w,max v z t} A))
        (hB : HomotopyCategoryLaws (AmbientDerived.category.{u,v,z,max vA w t} B)),
        ∃ d : DerivedAdjunctionData.{u,max vA v t,w,z} m.models.tensor m.models.hom hA hB,
          d.Realizes m.models.adjunction ∧ d.ComputesRepresentatives ∧ d.IsExact

end CommonModels

section AdjunctionComparison

/-- A square of signed adjunctions. The two comparison isomorphisms
intertwine both the unit and counit. -/
structure AdjunctionComparison
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (a' : F' ⊣ G') (I : C ⥤ C') (J : D ⥤ D') where
  tensor : F ⋙ J ≅ I ⋙ F'
  hom : G ⋙ I ≅ J ⋙ G'
  unit (X : C) :
    I.map (a.unit.app X) ≫ hom.hom.app (F.obj X) ≫ G'.map (tensor.hom.app X) =
      a'.unit.app (I.obj X)
  counit (Y : D) :
    F'.map (hom.inv.app Y) ≫ tensor.inv.app (G.obj Y) ≫ J.map (a.counit.app Y) =
      a'.counit.app (J.obj Y)

end AdjunctionComparison

section ComparingModels

universe s

open BalancedTensor (tmul)
open HomComplex (component gradedHom homotopyClass)
open DerivedCoefficientLift (Descent)

local notation "K" => HomComplex.homotopyCategory
local notation "D" => Derived.derivedCategory
local notation "Q" => Derived.quotient

variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
variable {A' : DGCategoryModel.{u,max s w z,w} k} {B' : DGCategoryModel.{u,max s w z,z} k}
variable {T : bimodule A B} {T' : bimodule A' B'}
variable {m : SignedModels.{u,v,w,z} T} {m' : SignedModels.{u,s,w,z} T'}
variable {I : RightDGModuleModel A ⥤ RightDGModuleModel A'}
variable {J : RightDGModuleModel B ⥤ RightDGModuleModel B'}

/-- The square of the actual strict functors is the one on balanced
generators and homogeneous right-linear maps. `a'` and `b'` identify the
unchanged index sets, and the term comparisons identify their coefficients. -/
def StrictComparisonLaws
    (e : AdjunctionComparison m.adjunction m'.adjunction I J)
    (a' : A.Obj ≃ A'.Obj) (b' : B.Obj ≃ B'.Obj)
    (upA : ∀ (X : RightDGModuleModel A) (a : A.Obj) (n : ℤ),
      (X.complex a).X n ≃ₗ[k] ((I.obj X).complex (a' a)).X n)
    (upB : ∀ (Y : RightDGModuleModel B) (b : B.Obj) (n : ℤ),
      (Y.complex b).X n ≃ₗ[k] ((J.obj Y).complex (b' b)).X n)
    (eT : ∀ a : A.Obj, J.obj (T.obj a) ≅ T'.obj (a' a)) : Prop :=
  (∀ (X : RightDGModuleModel A) (a : A.Obj) (b : B.Obj) (i j n : ℤ)
    (h : i+j=n) (x : (X.complex a).X i) (y : ((T.obj a).complex b).X j),
    ((e.tensor.hom.app X).app (b' b)).f n
      (upB ((ordinaryTensor.{u,v,w,z} m.tensor).obj X) b n
        (m.tensor.degree X b n (tmul T X b a i j n h x y))) =
      m'.tensor.degree (I.obj X) (b' b) n
        (tmul T' (I.obj X) (b' b) (a' a) i j n h (upA X a i x)
          (((eT a).hom.app (b' b)).f j (upB (T.obj a) b j y)))) ∧
  ∀ (Y : RightDGModuleModel B) (a : A.Obj) (b : B.Obj) (r i n : ℤ)
    (h : i+r=n) (g : gradedHom (T.obj a) Y r) (x : ((T.obj a).complex b).X i),
    component ((m'.hom.objectwise (J.obj Y) (a' a)).inv.f r
      (((e.hom.hom.app Y).app (a' a)).f r
        (upA ((ordinaryHom.{u,v,w,z} m.hom).obj Y) a r ((m.hom.objectwise Y a).hom.f r g))))
        (b' b) i n h (((eT a).hom.app (b' b)).f i (upB (T.obj a) b i x)) =
      upB Y b n (component g b i n h x)

variable {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
variable {hA' : HomotopyCategoryLaws A'} {hB' : HomotopyCategoryLaws B'}
variable (d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB)
variable (d' : DerivedAdjunctionData.{u,s,w,z} m'.tensor m'.hom hA' hB')
variable (dI : Descent hA hA' I) (dJ : Descent hB hB' J)

/-- The comparisons of the derived adjunctions on represented inputs
are the localization of the strict squares. The tensor equation holds for
every choice of strict K-projective replacement. -/
def ComparisonOnRepresentedInputs
    (e : AdjunctionComparison m.adjunction m'.adjunction I J)
    (ed :
      letI := Derived.homotopyCategory A hA
      letI := Derived.homotopyCategory B hB
      letI := Derived.homotopyCategory A' hA'
      letI := Derived.homotopyCategory B' hB'
      letI := derivedCategoryInstance A hA
      letI := derivedCategoryInstance B hB
      letI := derivedCategoryInstance A' hA'
      letI := derivedCategoryInstance B' hB'
      AdjunctionComparison d.adjunction d'.adjunction dI.D dJ.D) : Prop :=
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := Derived.homotopyCategory A' hA'
  letI := Derived.homotopyCategory B' hB'
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  letI := derivedCategoryInstance A' hA'
  letI := derivedCategoryInstance B' hB'
  let QA := Q A hA
  let QB := Q B hB
  let QA' := Q A' hA'
  let QB' := Q B' hB'
  (∀ N : RightDGModuleModel B,
    ed.hom.hom.app (QB.obj N) ≫ d'.hom.derived.map (dJ.representedIso N).hom ≫
      (d'.onInput (J.obj N)).hom =
    dI.D.map (d.onInput N).hom ≫
      (dI.representedIso ((ordinaryHom.{u,v,w,z} m.hom).obj N)).hom ≫
      QA'.map (homotopyClass (e.hom.hom.app N))) ∧
  ∀ {P M : RightDGModuleModel A} (p : P ⟶ M)
    (hP : isKProjective P) (hp : Module.quasiIsomorphism p),
    ∃ (hP' : isKProjective (I.obj P)) (hp' : Module.quasiIsomorphism (I.map p)),
      ed.tensor.hom.app (QA.obj M) ≫ d'.tensor.map (dI.representedIso M).hom ≫
        (d'.onReplacement (I.map p) hP' hp').hom =
      dJ.D.map (d.onReplacement p hP hp).hom ≫
        (dJ.representedIso ((ordinaryTensor.{u,v,w,z} m.tensor).obj P)).hom ≫
        QB'.map (homotopyClass (e.tensor.hom.app P))

/-- The strict and derived squares for specified module functors inducing
coefficient comparisons. The same exact derived adjunctions occur in the
two functor comparisons and in the unit and counit equations. -/
def DerivedAdjunctionComparison
    (e : AdjunctionComparison m.adjunction m'.adjunction I J) : Prop :=
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := Derived.homotopyCategory A' hA'
  letI := Derived.homotopyCategory B' hB'
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  letI := derivedCategoryInstance A' hA'
  letI := derivedCategoryInstance B' hB'
  ∃ ed : AdjunctionComparison d.adjunction d'.adjunction dI.D dJ.D,
    ComparisonOnRepresentedInputs d d' dI dJ e ed

end ComparingModels

section CoefficientComparisons

universe s

open AmbientDerived (category transportToAmbient)
open DerivedCoefficientLift (Descent strictTransition)

/-- Compatibility of the derived adjunctions at the lower and higher
common bounds. The coordinate identifications are the one-step versus
two-step coefficient lifts, including on the represented bimodule. -/
def AmbientDerivedAdjunctionComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,vA,w} k}
    {B : DGCategoryModel.{u,v,z} k} (T : bimodule A B)
    (m : AmbientSignedModels.{u,v,w,vA,z,t} T)
    (m' : AmbientSignedModels.{u,v,w,vA,z,max t s} T),
    (∀ a, isKProjective (m.bimodule.obj a)) →
    let A₀ := category.{u,vA,w,max v z t} A
    let B₀ := category.{u,v,z,max vA w t} B
    let A₁ := category.{u,vA,w,max v z t s} A
    let B₁ := category.{u,v,z,max vA w t s} B
    let I := strictTransition.{u,vA,w,max v z t,s} A
    let J := strictTransition.{u,v,z,max vA w t,s} B
    (∀ a, isKProjective (m'.bimodule.obj a)) ∧
    ∀ (hA : HomotopyCategoryLaws A₀) (hB : HomotopyCategoryLaws B₀)
      (hA' : HomotopyCategoryLaws A₁) (hB' : HomotopyCategoryLaws B₁),
      ∃ (dI : Descent hA hA' I) (dJ : Descent hB hB' J)
        (e : AdjunctionComparison m.models.adjunction m'.models.adjunction I J)
        (eT : ∀ a : A.Obj, J.obj (m.bimodule.obj a) ≅ m'.bimodule.obj a),
        dI.FullyFaithful ∧ dJ.FullyFaithful ∧
        (∀ (a : A.Obj) (b : B.Obj) (n : ℤ) (x : ((T.obj a).complex b).X n),
          ((eT a).hom.app b).f n (ULift.up ((m.comparison a).degree b n x)) =
            (m'.comparison a).degree b n x) ∧
        StrictComparisonLaws.{u,max vA v t,w,z,max vA v t s} e
          (Equiv.refl _) (Equiv.refl _)
          (fun _ _ _ => ULift.moduleEquiv.symm) (fun _ _ _ => ULift.moduleEquiv.symm) eT ∧
        ∃ (d : DerivedAdjunctionData.{u,max vA v t,w,z} m.models.tensor m.models.hom hA hB)
          (d' : DerivedAdjunctionData.{u,max vA v t s,w,z} m'.models.tensor m'.models.hom hA' hB'),
          d.Realizes m.models.adjunction ∧ d.ComputesRepresentatives ∧ d.IsExact ∧
          d'.Realizes m'.models.adjunction ∧ d'.ComputesRepresentatives ∧ d'.IsExact ∧
          DerivedAdjunctionComparison d d' dI dJ e

/-- At a common native coefficient bound, the arrow-action equivalences
identify the native adjunction and the ambient adjunction at that same
bound. This includes the native one-object models of dg algebras. -/
def NativeDerivedAdjunctionCompatibility : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w z,w} k}
    {B : DGCategoryModel.{u,max v w z,z} k} (T : bimodule A B)
    (m : SignedModels.{u,v,w,z} T)
    (m' : AmbientSignedModels.{u,max v w z,w,max v w z,z,0} T),
    (∀ a, isKProjective (T.obj a)) →
    let A₁ := category.{u,max v w z,w,max v w z} A
    let B₁ := category.{u,max v w z,z,max v w z} B
    let I := transportToAmbient.{u,v,w,max v w z} A
    let J := transportToAmbient.{u,v,z,max v w z} B
    (∀ a, isKProjective (m'.bimodule.obj a)) ∧
    ∀ (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B)
      (hA' : HomotopyCategoryLaws A₁) (hB' : HomotopyCategoryLaws B₁),
      letI := Derived.homotopyCategory A hA
      letI := Derived.homotopyCategory B hB
      letI := Derived.homotopyCategory A₁ hA'
      letI := Derived.homotopyCategory B₁ hB'
      letI := derivedCategoryInstance A hA
      letI := derivedCategoryInstance B hB
      letI := derivedCategoryInstance A₁ hA'
      letI := derivedCategoryInstance B₁ hB'
      ∃ (dI : Descent hA hA' I) (dJ : Descent hB hB' J)
        (e : AdjunctionComparison m.adjunction m'.models.adjunction I J)
        (eT : ∀ a : A.Obj, J.obj (T.obj a) ≅ m'.bimodule.obj a),
        dI.H.IsEquivalence ∧ dI.D.IsEquivalence ∧ dJ.H.IsEquivalence ∧ dJ.D.IsEquivalence ∧
        (∀ (a : A.Obj) (b : B.Obj) (n : ℤ) (x : ((T.obj a).complex b).X n),
          ((eT a).hom.app b).f n x = (m'.comparison a).degree b n x) ∧
        StrictComparisonLaws.{u,v,w,z,max v w z} e (Equiv.refl _) (Equiv.refl _)
          (fun _ _ _ => LinearEquiv.refl _ _) (fun _ _ _ => LinearEquiv.refl _ _) eT ∧
        ∃ (d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB)
          (d' : DerivedAdjunctionData.{u,max v w z,w,z} m'.models.tensor m'.models.hom hA' hB'),
          d.Realizes m.adjunction ∧ d.ComputesRepresentatives ∧ d.IsExact ∧
          d'.Realizes m'.models.adjunction ∧ d'.ComputesRepresentatives ∧ d'.IsExact ∧
          DerivedAdjunctionComparison d d' dI dJ e

end CoefficientComparisons


end

end Specs.DerivedFormalization.DG.DerivedBimoduleAdjunction
