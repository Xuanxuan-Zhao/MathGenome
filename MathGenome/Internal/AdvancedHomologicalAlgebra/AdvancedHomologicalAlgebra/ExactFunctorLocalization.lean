import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExactFunctorLocalization
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedCategory
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty

/-!
HA-R10 (notes/002/advanced-homological-algebra.tex, 2041–2057).
The exact-functor localization in Mathlib gives the unbounded termwise descent
and its triangulated structure. The natural kernel/image/quotient comparison
on complexes descends because precomposition with a localization is fully
faithful. It shows that both cohomological bounds are preserved, so the same
functor restricts to D⁺ and D⁻. Their comparisons are the restrictions of the
unbounded factorization. Since these comparisons are invertible, full
faithfulness of precomposition proves both universal properties. HA-R05 then
gives the unique comparison-preserving identifications with any RF and LF.
-/

set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v u' v' w w' u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.ExactFunctorLocalization

namespace AdvancedHomologicalAlgebra.ExactFunctorLocalization

section
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

noncomputable def descended : descendedType (A := A) (B := B) := descendedValue F
noncomputable def factors : factorsType F := factorsValue F

theorem exact : exactType F := ⟨inferInstance, inferInstance⟩

/-- The usual kernel/image/quotient comparison is natural already on complexes. -/
noncomputable def complexCohomologyIso (n : ℤ) :
    F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) n ≅
      HomologicalComplex.homologyFunctor A (.up ℤ) n ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso F)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor A (.up ℤ) n).map f) F)

noncomputable def cohomologyIso (n : ℤ) :
    descendedValue F ⋙ _root_.DerivedCategory.homologyFunctor B n ≅
      _root_.DerivedCategory.homologyFunctor A n ⋙ F :=
  (Localization.fullyFaithfulWhiskeringLeft _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) B).preimageIso
      ((associator _ _ _).symm ≪≫
        isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫ associator _ _ _ ≪≫
        isoWhiskerLeft _ (_root_.DerivedCategory.homologyFunctorFactors B n) ≪≫
        complexCohomologyIso F n ≪≫
        isoWhiskerRight (_root_.DerivedCategory.homologyFunctorFactors A n).symm F ≪≫
        associator _ _ _)

theorem cohomology : cohomologyType F := fun n => ⟨cohomologyIso F n⟩

/-- Cohomological bounds are retained without any injective/projective hypothesis. -/
lemma preservesGE (X : _root_.DerivedCategory A) (a : ℤ) (h : X.IsGE a) :
    ((descendedValue F).obj X).IsGE a := by
  rw [_root_.DerivedCategory.isGE_iff]
  intro i hi
  exact (F.map_isZero ((_root_.DerivedCategory.isGE_iff X a).mp h i hi)).of_iso
    ((cohomologyIso F i).app X)

lemma preservesLE (X : _root_.DerivedCategory A) (b : ℤ) (h : X.IsLE b) :
    ((descendedValue F).obj X).IsLE b := by
  rw [_root_.DerivedCategory.isLE_iff]
  intro i hi
  exact (F.map_isZero ((_root_.DerivedCategory.isLE_iff X b).mp h i hi)).of_iso
    ((cohomologyIso F i).app X)

noncomputable def plusFunctor : _root_.DerivedCategory.Plus A ⥤ _root_.DerivedCategory.Plus B :=
  _root_.DerivedCategory.TStructure.t.plus.lift
    (_root_.DerivedCategory.Plus.ι ⋙ descendedValue F)
    (fun ⟨X, a, ha⟩ => ⟨a, preservesGE F X a ha⟩)

noncomputable def minusFunctor : _root_.DerivedCategory.Minus A ⥤ _root_.DerivedCategory.Minus B :=
  _root_.DerivedCategory.TStructure.t.minus.lift
    (_root_.DerivedCategory.Minus.ι ⋙ descendedValue F)
    (fun ⟨X, b, hb⟩ => ⟨b, preservesLE F X b hb⟩)

noncomputable instance : (plusFunctor F).CommShift ℤ := ObjectProperty.commShiftLift ..
noncomputable instance : (minusFunctor F).CommShift ℤ := ObjectProperty.commShiftLift ..
instance : (plusFunctor F).IsTriangulated := by dsimp [plusFunctor]; infer_instance
instance : (minusFunctor F).IsTriangulated := by dsimp [minusFunctor]; infer_instance

noncomputable def plusRestriction : plusFunctor F ⋙ _root_.DerivedCategory.Plus.ι ≅
    _root_.DerivedCategory.Plus.ι ⋙ descendedValue F := Iso.refl _
noncomputable def minusRestriction : minusFunctor F ⋙ _root_.DerivedCategory.Minus.ι ≅
    _root_.DerivedCategory.Minus.ι ⋙ descendedValue F := Iso.refl _

noncomputable def plusComparison : _root_.DerivedCategory.Plus.Qh ⋙ plusFunctor F ≅ plusUValue F :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _ (F.mapDerivedCategoryFactorsh.app X.obj))
    (by intro X Y f; ext : 1; exact F.mapDerivedCategoryFactorsh.hom.naturality f.hom)

noncomputable def minusComparison : QMinus A ⋙ minusFunctor F ≅ minusUValue F :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _ (F.mapDerivedCategoryFactorsh.app X.obj))
    (by intro X Y f; ext : 1; exact F.mapDerivedCategoryFactorsh.hom.naturality f.hom)
end

section Universal
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
  (U : C ⥤ E) (G : D ⥤ E)

/-- An invertible comparison along a localization gives both universal properties. -/
noncomputable def rightDataOfIso (e : U ≅ Q ⋙ G) : RightData Q U where
  functor := G
  unit := e.hom
  universal H := by
    let ff := Localization.fullyFaithfulWhiskeringLeft Q W E
    constructor
    · intro α β h
      apply ff.map_injective
      exact (cancel_epi e.hom).mp h
    · intro τ
      obtain ⟨α, hα⟩ := ff.map_surjective (e.inv ≫ τ)
      refine ⟨α, ?_⟩
      change e.hom ≫ whiskerLeft Q α = τ
      rw [show whiskerLeft Q α = _ from hα]
      simp

noncomputable def leftDataOfIso (e : Q ⋙ G ≅ U) : LeftData Q U where
  functor := G
  counit := e.hom
  universal H := by
    let ff := Localization.fullyFaithfulWhiskeringLeft Q W E
    constructor
    · intro α β h
      apply ff.map_injective
      exact (cancel_mono e.hom).mp h
    · intro τ
      obtain ⟨α, hα⟩ := ff.map_surjective (τ ≫ e.inv)
      refine ⟨α, ?_⟩
      change whiskerLeft Q α ≫ e.hom = τ
      rw [show whiskerLeft Q α = _ from hα]
      simp
end Universal

section
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

noncomputable def boundedDescent : BoundedDescent F where
  right := rightDataOfIso _ (HomotopyCategory.Plus.quasiIso A) _ _ (plusComparison F).symm
  rightRestriction := plusRestriction F
  rightShift := inferInstanceAs ((plusFunctor F).CommShift ℤ)
  rightExact := inferInstanceAs ((plusFunctor F).IsTriangulated)
  rightCompatibility X := by
    change F.mapDerivedCategoryFactorsh.inv.app X.obj ≫ 𝟙 _ = _
    simp
  rightComparison := inferInstanceAs (IsIso (plusComparison F).inv)
  rightIdentification R := TotalDerivedUniversalProperty.rightUnique _ _ _ _ _ R _
  left := leftDataOfIso _ (WMinus A) _ _ (minusComparison F)
  leftRestriction := minusRestriction F
  leftShift := inferInstanceAs ((minusFunctor F).CommShift ℤ)
  leftExact := inferInstanceAs ((minusFunctor F).IsTriangulated)
  leftCompatibility X := by
    change 𝟙 _ ≫ F.mapDerivedCategoryFactorsh.hom.app X.obj = _
    simp
  leftComparison := inferInstanceAs (IsIso (minusComparison F).hom)
  leftIdentification R := TotalDerivedUniversalProperty.leftUnique _ _ _ _ _ R _

theorem bounded : boundedType F := ⟨boundedDescent F⟩
end
end AdvancedHomologicalAlgebra.ExactFunctorLocalization
