import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedCoproducts
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedTriangles

open CategoryTheory CategoryTheory.Limits

universe u v w j t s

namespace Specs.DerivedFormalization.DG.DerivedByResolutions

open _root_.DerivedFormalization
open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance)
open DerivedCoproducts (ResolutionSum derivedCofan)
open IndexedSemiFree (StrictSum)
open AmbientDerived (category)
open DerivedCoefficientLift (Descent strictTransition)

noncomputable section

/-- All modules at the adequate bound have K-projective replacements there. -/
def AmbientResolutions : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (M : RightDGModuleModel (category.{u,v,w,t} A)),
    ∃ (P : RightDGModuleModel (category.{u,v,w,t} A)) (p : P ⟶ M),
      IndexedSemiFree.semiFree P ∧ KProjective.isKProjective P ∧
      Module.degreewiseSurjective p ∧ Module.quasiIsomorphism p

/-- The canonical Hom comparison is additive for the group laws on the
localization, in particular for those of the cone triangulation. -/
def AmbientHomGroups : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A)),
    let B := category.{u,v,w,t} A
    letI := Derived.homotopyCategory B h
    letI := derivedCategoryInstance B h
    let Q : HomComplex.homotopyCategory B ⥤ Derived.derivedCategory B h :=
      AmbientDerived.quotient.{u,v,w,t} A h
    ∀ AD : Preadditive (Derived.derivedCategory B h),
      letI := AD
      ∀ {P M N : AmbientDerived.homotopyCategory.{u,v,w,t} A}
        (p : RightDGModuleHomModel P M) (hp : Module.quasiIsomorphism p),
        KProjective.isKProjective P →
        ∃ e : Basic.h0Hom (HomComplex.homComplex P N) ≃+ (Q.obj M ⟶ Q.obj N),
          ∀ g, e g = DerivedKProjective.homComparisonMap (N := N) h p hp g

/-- For every family in the localization at a bound containing the index,
a strict sum of representatives gives a coproduct with the localized
inclusion maps. The representatives are the objects of the localization model. -/
def CoproductsAtAdequateIndex : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w j,w} k}
    (h : HomotopyCategoryLaws A) {I : Type j},
    letI := Derived.homotopyCategory A h
    letI := derivedCategoryInstance A h
    ∀ X : I → Derived.derivedCategory A h,
      let F := fun i => (Localization.Construction.objEquiv (Derived.quasiIsomorphisms A)).symm (X i)
      ∃ (S : RightDGModuleModel A) (b : StrictSum F S),
        ResolutionSum b ∧ Nonempty (IsColimit (derivedCofan h b)) ∧ HasCoproduct X

/-- One descent implements the fully faithful transition on a pair of adequate
bounds and compares the derived inclusions and descents for every realized sum. -/
def CoproductTransitionCompatibility : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A))
    (h' : HomotopyCategoryLaws (category.{u,v,w,max t s} A)),
    let B := category.{u,v,w,t} A
    let C := category.{u,v,w,max t s} A
    let T := strictTransition.{u,v,w,t,s} A
    letI := derivedCategoryInstance B h
    letI := derivedCategoryInstance C h'
    ∃ d : Descent h h' T,
      d.FullyFaithful ∧ d.LinearOnClasses ∧ d.ReplacementCompatible ∧
      ∀ {I : Type j} {F : I → RightDGModuleModel B} {S : RightDGModuleModel B}
        (b : StrictSum F S),
        ∃ c : StrictSum (fun i => T.obj (F i)) (T.obj S),
          (∀ i, c.inclusion i = T.map (b.inclusion i)) ∧
          (∀ a n x i, (c.coordinates a n x i).down = b.coordinates a n x.down i) ∧
          Nonempty (IsColimit (derivedCofan h b)) ∧
          Nonempty (IsColimit (derivedCofan h' c)) ∧ DerivedCoproducts.TransitionMaps d b c

/-- G08 in the adequate localization, including its Hom groups, inherited cone
triangulation, pointwise coproducts, and the comparisons with original inputs,
the adequate native model, and larger bounds. -/
def ComputingDerivedByResolutions : Prop :=
  AmbientDerived.IsLocalization.{u,v,w,t} ∧
  AmbientResolutions.{u,v,w,t} ∧
  DerivedKProjective.AmbientLocalizationEquivalence.{u,v,w,t} ∧
  DerivedKProjective.AmbientHomComparison.{u,v,w,t} ∧
  AmbientHomGroups.{u,v,w,t} ∧
  DerivedKProjective.AmbientReplacementComparison.{u,v,w,t} ∧
  DerivedKProjective.AmbientHomComparisonSourceNaturality.{u,v,w,t} ∧
  DerivedTriangles.AmbientTriangulation.{u,v,w,t} ∧
  DerivedTriangles.LiftedConeTriangleComparison.{u,v,w,t} ∧
  AmbientDerived.InputCoefficients.{u,v,w,t} ∧
  AmbientDerived.InputLocalization.{u,v,w,t} ∧
  DerivedKProjective.OriginalInputComparison.{u,v,w,t} ∧
  AmbientDerived.NativeStrictComparison.{u,v,w,t} ∧
  AmbientDerived.NativeLocalizationComparison.{u,v,w,t} ∧
  DerivedKProjective.AdequateNativeComparison.{u,v,w,t} ∧
  DerivedTriangles.NativeTriangulation.{u,v,w} ∧
  CoproductsAtAdequateIndex.{u,v,w,j} ∧
  DerivedCoproducts.OriginalDerivedCoproduct.{u,v,w,j,t} ∧
  DerivedCoproducts.OriginalExistingDerivedCoproduct.{u,v,w,j,t} ∧
  DerivedCoproducts.NativeExistingDerivedCoproduct.{u,v,w,j} ∧
  DerivedCoproducts.G02SumComparison.{u,v,w} ∧
  CoproductTransitionCompatibility.{u,v,w,j,t,s} ∧
  DerivedCoefficientLift.OriginalInputCompatibility.{u,v,w,t,s} ∧
  DerivedCoefficientLift.KProjectiveTransition.{u,v,w,t,s}

end

end Specs.DerivedFormalization.DG.DerivedByResolutions
