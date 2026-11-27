import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Homotopy
import Mathlib.AlgebraicTopology.ModelCategory.BifibrantObjectHomotopy

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra

universe v u v' u'

namespace DerivedFormalization.Model

/-- Functorial cofibrant and fibrant replacements with their comparison maps. -/
structure Replacement (C : Type u) [Category.{v} C] [ModelCategory C] where
  Q : C ⥤ C
  R : C ⥤ C
  p : Q ⟶ 𝟭 C
  i : 𝟭 C ⟶ R
  cofibrant (X : C) : IsCofibrant (Q.obj X)
  fibrant (X : C) : IsFibrant (R.obj X)
  trivialFibration (X : C) : trivialFibrations C (p.app X)
  trivialCofibration (X : C) : trivialCofibrations C (i.app X)

end DerivedFormalization.Model

namespace DerivedFormalization.Specs.ModelLocalization

open DerivedFormalization.Model

/-- The category with bifibrant objects and homotopy classes as morphisms. -/
abbrev homotopyCategoryValue (C : Type u) [Category.{v} C] [ModelCategory C] :=
  BifibrantObject.HoCat C

set_option linter.checkUnivs false in
def homotopyCategoryType :=
  ∀ (C : Type u) [Category.{v} C] [ModelCategory C], Type u

set_option linter.checkUnivs false in
def homotopyClassFunctorType :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C],
    BifibrantObject C ⥤ homotopyCategoryValue C

abbrev homotopyClassFunctorValue : homotopyClassFunctorType.{v, u} :=
  fun {_} [_] [_] => BifibrantObject.toHoCat

/-- Equality of classes is precisely the common homotopy relation of Q03. -/
def homotopyClassMapEqType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C]
    {X Y : BifibrantObject C} (f g : X ⟶ Y),
      homotopyClassFunctorValue.map f = homotopyClassFunctorValue.map g ↔
        ModelHomotopy.leftHomotopicValue f.hom g.hom

def replacementExistsType : Prop :=
  ∀ (C : Type u) [Category.{v} C] [FunctorialModelCategory C], Nonempty (Replacement C)

set_option linter.checkUnivs false in
def toBifibrantType :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C],
    Replacement C → (C ⥤ BifibrantObject C)

/-- The strict composite RQ viewed as a functor to the bifibrant subcategory. -/
def toBifibrantValue : toBifibrantType.{v, u} :=
  fun {C} [_] [_] r => (bifibrantObjects C).lift (r.Q ⋙ r.R) (fun X => by
    have : IsCofibrant ((𝟭 C).obj (r.Q.obj X)) := r.cofibrant X
    have : Cofibration (r.i.app (r.Q.obj X)) :=
      (cofibration_iff _).2 (r.trivialCofibration _).1
    exact ⟨isCofibrant_of_cofibration (r.i.app (r.Q.obj X)), r.fibrant _⟩)

set_option linter.checkUnivs false in
def localizationFunctorType :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C],
    Replacement C → (C ⥤ homotopyCategoryValue C)

/-- Apply the two functorial replacements and pass to homotopy classes. -/
abbrev localizationFunctorValue : localizationFunctorType.{v, u} :=
  fun {_} [_] [_] r => toBifibrantValue r ⋙ homotopyClassFunctorValue

def replacementWeakEquivalencesType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] (r : Replacement C)
    {X Y : C} (f : X ⟶ Y),
      (weakEquivalences C (r.Q.map f) ↔ weakEquivalences C f) ∧
      (weakEquivalences C (r.R.map f) ↔ weakEquivalences C f)

def localizationType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [FunctorialModelCategory C] (r : Replacement C),
    (localizationFunctorValue r).IsLocalization (weakEquivalences C)

/-- Precomposition is an equivalence onto the full category of functors
inverting weak equivalences, with natural transformations as morphisms. -/
def universalPropertyType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [FunctorialModelCategory C] (r : Replacement C),
    ∃ h : (weakEquivalences C).IsInvertedBy (localizationFunctorValue r),
      ∀ (D : Type u') [Category.{v'} D],
        ((show ObjectProperty (C ⥤ D) from fun F => (weakEquivalences C).IsInvertedBy F).lift
          ((Functor.whiskeringLeft C (homotopyCategoryValue C) D).obj
            (localizationFunctorValue r))
          (IsInvertedBy.of_comp _ _ h)).IsEquivalence

def isIsoType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [FunctorialModelCategory C] (r : Replacement C)
    {X Y : C} (f : X ⟶ Y),
      IsIso ((localizationFunctorValue r).map f) ↔ weakEquivalences C f

/-- The isomorphism criterion is invariant under the choice of localization. -/
def isIsoAnyLocalizationType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [FunctorialModelCategory C]
    {D : Type u'} [Category.{v'} D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {X Y : C} (f : X ⟶ Y), IsIso (L.map f) ↔ weakEquivalences C f

end DerivedFormalization.Specs.ModelLocalization
