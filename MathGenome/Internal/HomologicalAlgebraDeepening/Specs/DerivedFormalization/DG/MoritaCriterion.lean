import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.MoritaUnit

open CategoryTheory CategoryTheory.Limits
open _root_.DerivedFormalization

universe u v w z vA t

namespace Specs.DerivedFormalization.DG.MoritaCriterion

open BalancedTensor (CochainMap bimodule)
open CoefficientLiftComparison (CUp)
open CompactFiniteCells (CompactAt)
open CompactRepresentables (LocalizationMapAdditive)
open Derived (HomotopyCategoryLaws)
open DerivedBimoduleAdjunction (SignedModels DerivedAdjunctionData AmbientSignedModels)
open DerivedKProjective (derivedCategoryInstance)
open HomComplex (component gradedHom homComplex)
open KProjective (isKProjective)
open MoritaUnit (MorphismQuasiIsomorphisms toComplexHom)

noncomputable section

variable {k : Type u} [CommRing k]

/-- The localizations of the strict shifts of the represented bimodule detect zero.
The cone localization's shift comparison identifies these with the derived shifts. -/
def ShiftedImagesDetectZero
    {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
    (T : bimodule A B) (hB : HomotopyCategoryLaws B) : Prop :=
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance B hB
  let Q := Derived.quotient B hB
  ∀ Y : Derived.derivedCategory B hB,
    (∀ (a : A.Obj) (n : ℤ), Subsingleton (Q.obj (ShiftCone.shift (T.obj a) n) ⟶ Y)) →
      IsZero Y

/-- The criterion for the given exact derived tensor–Hom adjunction at a common
adequate bound. This applies to native models and to the ambient signed models
with independently sized original coefficient and object universes. -/
def MoritaCriterionAt : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w z,w} k}
    {B : DGCategoryModel.{u,max v w z,z} k} {T : bimodule A B}
    (m : SignedModels.{u,v,w,z} T)
    (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B),
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    ∀ (S : Preadditive (Derived.derivedCategory B hB))
      (d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB),
      LocalizationMapAdditive hB S →
      d.Realizes m.adjunction → d.ComputesRepresentatives → d.IsExact →
      (∀ a, isKProjective (T.obj a)) →
      (d.tensor.IsEquivalence ↔
        (∀ a, CompactAt.{u,z,max v w z,max v w z} hB S ((Derived.quotient B hB).obj (T.obj a))) ∧
        MorphismQuasiIsomorphisms.{u,v,w,z} T ∧
        ShiftedImagesDetectZero.{u,v,w,z} T hB)

/-- Place a cochain map between independently sized complexes in one coefficient
category by the degreewise up and down identifications. -/
def liftCochainMap.{base, src, dst, extra} {R : Type base} [CommRing R]
    {C : ModuleCochain.{base,src} R} {E : ModuleCochain.{base,dst} R}
    (f : CochainMap C E) :
    CUp.{base,src,max dst extra} C ⟶ CUp.{base,dst,max src extra} E :=
  toComplexHom
    { f := fun n =>
        ULift.moduleEquiv.symm.toLinearMap.comp
          ((f.f n).comp ULift.moduleEquiv.toLinearMap)
      comm := fun n x => ULift.ext (f.comm n x.down) }

/-- Under conjugation by the coefficient identifications, the morphism-complex
map of the represented bimodule is the lift of the original morphism-complex
map. Quasi-isomorphy of the original map compares at this same bound. -/
def AmbientMorphismQuasiIsomorphisms : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,vA,w} k}
    {B : DGCategoryModel.{u,v,z} k} (T : bimodule A B)
    (m : AmbientSignedModels.{u,v,w,vA,z,t} T) (a b : A.Obj),
    let f := liftCochainMap.{u,vA,max v z,max w t}
      (C := A.hom a b) (E := homComplex (T.obj a) (T.obj b)) (T.map a b)
    let f' : CUp.{u,vA,max v w z t} (A.hom a b) ⟶
        homComplex (m.bimodule.obj a) (m.bimodule.obj b) :=
      toComplexHom (m.bimodule.map a b)
    ∃ e : CUp.{u,max v z,max vA w t} (homComplex (T.obj a) (T.obj b)) ≅
        homComplex (m.bimodule.obj a) (m.bimodule.obj b),
      (∀ (r : ℤ) (g : gradedHom (T.obj a) (T.obj b) r)
        (c : B.Obj) (i j : ℤ) (h : i+r=j) (x : ((T.obj a).complex c).X i),
        component (e.hom.f r (ULift.up g)) c i j h ((m.comparison a).degree c i x) =
          (m.comparison b).degree c j (component g c i j h x)) ∧
      f ≫ e.hom = f' ∧
      (QuasiIso f ↔ QuasiIso f')

end

end Specs.DerivedFormalization.DG.MoritaCriterion
