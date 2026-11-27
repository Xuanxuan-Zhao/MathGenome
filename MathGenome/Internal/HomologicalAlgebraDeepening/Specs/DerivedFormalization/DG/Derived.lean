import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.HomComplex
import Mathlib.CategoryTheory.Localization.Predicate

open CategoryTheory

universe u v w

namespace Specs.DerivedFormalization.DG.Derived

open _root_.DerivedFormalization

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}

set_option linter.checkUnivs false

noncomputable abbrev homotopyCategoryStruct (A : DGCategoryModel.{u,v,w} k) :
    CategoryStruct.{max v w} (HomComplex.homotopyCategory A) :=
  Basic.h0CategoryStruct (HomComplex.dgModuleCategory A)

/-- The morphisms to invert in the degree-zero cohomology category. -/
def quasiIsomorphisms (A : DGCategoryModel.{u,v,w} k) :
    @MorphismProperty (HomComplex.homotopyCategory A) (homotopyCategoryStruct A) :=
  fun M N g => ∃ f : RightDGModuleHomModel M N,
    HomComplex.homotopyClass f = g ∧ Module.quasiIsomorphism f

def QuasiIsomorphismsType :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    @MorphismProperty (HomComplex.homotopyCategory A) (homotopyCategoryStruct A)

/-- On strict representatives, the localized class is precisely the objectwise
quasi-isomorphisms. In particular the test is independent of the representative. -/
def QuasiIsomorphismsOnClasses : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (f : RightDGModuleHomModel M N),
    quasiIsomorphisms A (HomComplex.homotopyClass f) ↔ Module.quasiIsomorphism f

/-- The local form of the upstream theorem `HomComplex.HomotopyCategoryStructure`. -/
abbrev HomotopyCategoryLaws (A : DGCategoryModel.{u,v,w} k) : Prop :=
  ∃ C : Category.{max v w} (HomComplex.homotopyCategory A),
    C.toCategoryStruct = homotopyCategoryStruct A

/-- Use the upstream laws with the fixed degree-zero cohomology operations. -/
@[instance_reducible]
noncomputable def homotopyCategory (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws A) :
    Category.{max v w} (HomComplex.homotopyCategory A) where
  toCategoryStruct := homotopyCategoryStruct A
  id_comp := by
    obtain ⟨C, e⟩ := h
    cases C with
    | mk hid _ _ =>
      cases e
      exact hid
  comp_id := by
    obtain ⟨C, e⟩ := h
    cases C with
    | mk _ hid _ =>
      cases e
      exact hid
  assoc := by
    obtain ⟨C, e⟩ := h
    cases C with
    | mk _ _ hassoc =>
      cases e
      exact hassoc

/-- The canonical localization, using the upstream category laws. -/
def derivedCategory (A : DGCategoryModel.{u,v,w} k) (h : HomotopyCategoryLaws A) :=
  @MorphismProperty.Localization _ (homotopyCategory A h) (quasiIsomorphisms A)

def DerivedCategoryType :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k), HomotopyCategoryLaws A →
    Type (max u w (v+1))

/-- The canonical functor to the localization at the specified class. -/
noncomputable def quotient (A : DGCategoryModel.{u,v,w} k) (h : HomotopyCategoryLaws A) :=
  @MorphismProperty.Q _ (homotopyCategory A h) (quasiIsomorphisms A)

def QuotientType :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k) (h : HomotopyCategoryLaws A),
    letI C := homotopyCategory A h
    let D := @MorphismProperty.Localization _ C (quasiIsomorphisms A)
    letI : Category D := inferInstanceAs
      (Category (@MorphismProperty.Localization _ C (quasiIsomorphisms A)))
    HomComplex.homotopyCategory A ⥤ D

def IsLocalization : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k) (h : HomotopyCategoryLaws A),
    letI := homotopyCategory A h
    (quotient A h).IsLocalization (quasiIsomorphisms A)

end Specs.DerivedFormalization.DG.Derived
