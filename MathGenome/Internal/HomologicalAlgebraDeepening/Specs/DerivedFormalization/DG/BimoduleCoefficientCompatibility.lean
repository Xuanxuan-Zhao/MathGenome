import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.BimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedCoefficientLift

open CategoryTheory
open _root_.DerivedFormalization

universe u v w z vA t s

set_option autoImplicit false

namespace Specs.DerivedFormalization.DG.BimoduleCoefficientCompatibility

open BalancedTensor (bimodule tmul)
open BimoduleAdjunction
  (InternalHomModel TensorModel ordinaryTensor ordinaryHom OrdinaryCurryFamily StrictLaws
    restrictLifted asMixed ModuleEquiv BimoduleLiftLaws)
open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance kProjectiveObjects replacementIso)
open DerivedCoefficientLift (Descent strictTransition)
open AmbientDerived (category transportToAmbient)
open HomComplex (component gradedHom homotopyClass)
open KProjective (isKProjective)

noncomputable section

variable {k : Type u} [CommRing k]

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

section Strict

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

end Strict

/-- Compare two adequate representations of the same bimodule along a further lift. -/
def AmbientStrictComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,vA,w} k}
    {B : DGCategoryModel.{u,v,z} k} {T : bimodule A B}
    (m : AmbientSignedModels.{u,v,w,z,vA,t} T)
    (m' : AmbientSignedModels.{u,v,w,z,vA,max t s} T),
    let I := strictTransition.{u,vA,w,max v z t,s} A
    let J := strictTransition.{u,v,z,max vA w t,s} B
    ∃ (eT : ∀ a : A.Obj, J.obj (m.bimodule.obj a) ≅ m'.bimodule.obj a)
      (e : AdjunctionComparison m.models.adjunction m'.models.adjunction I J),
      (∀ (a : A.Obj) (b : B.Obj) (n : ℤ) (x : ((T.obj a).complex b).X n),
        ((eT a).hom.app b).f n (ULift.up ((m.comparison a).degree b n x)) =
          (m'.comparison a).degree b n x) ∧
      StrictComparisonLaws.{u,max vA v t,w,z,max vA v t s}
        (m := m.models) (m' := m'.models) (I := I) (J := J) e
        (Equiv.refl _) (Equiv.refl _)
        (fun _ _ _ => ULift.moduleEquiv.symm) (fun _ _ _ => ULift.moduleEquiv.symm) eT

/-- Compare an adequate native bimodule with its representation at the same bound. -/
def NativeStrictComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w z,w} k}
    {B : DGCategoryModel.{u,max v w z,z} k} {T : bimodule A B}
    (m : SignedModels.{u,v,w,z} T)
    (m' : AmbientSignedModels.{u,max v w z,w,z,max v w z,0} T),
    let I := transportToAmbient.{u,v,w,max v w z} A
    let J := transportToAmbient.{u,v,z,max v w z} B
    ∃ (eT : ∀ a : A.Obj, J.obj (T.obj a) ≅ m'.bimodule.obj a)
      (e : AdjunctionComparison m.adjunction m'.models.adjunction I J),
      (∀ (a : A.Obj) (b : B.Obj) (n : ℤ) (x : ((T.obj a).complex b).X n),
        ((eT a).hom.app b).f n x = (m'.comparison a).degree b n x) ∧
      StrictComparisonLaws.{u,v,w,z,max v w z}
        (m := m) (m' := m'.models) (I := I) (J := J) e (Equiv.refl _) (Equiv.refl _)
        (fun _ _ _ => LinearEquiv.refl _ _) (fun _ _ _ => LinearEquiv.refl _ _) eT

local notation "K" => HomComplex.homotopyCategory
local notation "D" => Derived.derivedCategory
local notation "Q" => Derived.quotient

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

section DerivedData

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
  ∀ (P : RightDGModuleModel A) (hp : isKProjective P),
    d.tensorSquare.hom.app ⟨P, hp⟩ =
      QB.map (d.tensorH.map (d.resolutionAdjunction.counit.app P))

end DerivedData

/-- Objectwise quasi-isomorphism preservation by a strict transition. -/
def PreservesQuasiIsomorphisms {A : DGCategoryModel.{u,v,w} k}
    {A' : DGCategoryModel.{u,s,w} k}
    (I : RightDGModuleModel A ⥤ RightDGModuleModel A') : Prop :=
  ∀ {X Y : RightDGModuleModel A} (f : X ⟶ Y),
    Module.quasiIsomorphism f → Module.quasiIsomorphism (I.map f)

/-- Preservation of K-projectivity against all acyclic modules of the target. -/
def PreservesKProjectives {A : DGCategoryModel.{u,v,w} k}
    {A' : DGCategoryModel.{u,s,w} k}
    (I : RightDGModuleModel A ⥤ RightDGModuleModel A') : Prop :=
  ∀ X : RightDGModuleModel A, isKProjective X → isKProjective (I.obj X)

section Descent

variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
variable {A' : DGCategoryModel.{u,max s w z,w} k} {B' : DGCategoryModel.{u,max s w z,z} k}
variable {T : bimodule A B} {T' : bimodule A' B'}
variable {m : SignedModels.{u,v,w,z} T} {m' : SignedModels.{u,s,w,z} T'}
variable {I : RightDGModuleModel A ⥤ RightDGModuleModel A'}
variable {J : RightDGModuleModel B ⥤ RightDGModuleModel B'}

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
    (hI : PreservesQuasiIsomorphisms I) (hIP : PreservesKProjectives I)
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
    ed.tensor.hom.app (QA.obj M) ≫ d'.tensor.map (dI.representedIso M).hom ≫
      (d'.onReplacement (I.map p) (hIP P hP) (hI p hp)).hom =
      dJ.D.map (d.onReplacement p hP hp).hom ≫
        (dJ.representedIso ((ordinaryTensor.{u,v,w,z} m.tensor).obj P)).hom ≫
        QB'.map (homotopyClass (e.tensor.hom.app P))

end Descent

/-- Descent of a strict comparison, with both mate equations and the formulas
on represented Hom inputs and on each strict K-projective replacement. -/
def DerivedComparison : Prop :=
  ∀ {k : Type u} [CommRing k]
    {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
    {A' : DGCategoryModel.{u,max s w z,w} k} {B' : DGCategoryModel.{u,max s w z,z} k}
    {T : bimodule A B} {T' : bimodule A' B'}
    (m : SignedModels.{u,v,w,z} T) (m' : SignedModels.{u,s,w,z} T')
    (I : RightDGModuleModel A ⥤ RightDGModuleModel A')
    (J : RightDGModuleModel B ⥤ RightDGModuleModel B')
    (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B)
    (hA' : HomotopyCategoryLaws A') (hB' : HomotopyCategoryLaws B')
    (dI : Descent hA hA' I) (dJ : Descent hB hB' J)
    (d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB)
    (d' : DerivedAdjunctionData.{u,s,w,z} m'.tensor m'.hom hA' hB')
    (e : AdjunctionComparison m.adjunction m'.adjunction I J)
    (hI : PreservesQuasiIsomorphisms I) (_hJ : PreservesQuasiIsomorphisms J)
    (hIP : PreservesKProjectives I),
    d.Realizes m.adjunction → d'.Realizes m'.adjunction →
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := Derived.homotopyCategory A' hA'
    letI := Derived.homotopyCategory B' hB'
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    letI := derivedCategoryInstance A' hA'
    letI := derivedCategoryInstance B' hB'
    ∃ ed : AdjunctionComparison d.adjunction d'.adjunction dI.D dJ.D,
      ComparisonOnRepresentedInputs d d' dI dJ e hI hIP ed

end

end Specs.DerivedFormalization.DG.BimoduleCoefficientCompatibility
