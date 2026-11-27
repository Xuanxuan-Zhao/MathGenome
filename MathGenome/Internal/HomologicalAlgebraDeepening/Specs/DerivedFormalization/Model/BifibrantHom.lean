import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Localization
import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma

open CategoryTheory HomotopicalAlgebra

universe v u v' u'

namespace DerivedFormalization.Specs.ModelBifibrantHom

/-- Mathlib's quotient presents the common homotopy relation of Q03. -/
def classEqType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A B : C}
    [IsCofibrant A] [IsFibrant B] (f g : A ⟶ B),
    LeftHomotopyClass.mk f = LeftHomotopyClass.mk g ↔
      ModelHomotopy.leftHomotopicValue f g

set_option linter.checkUnivs false in
def precompType :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A' A B : C}
    [IsFibrant B], (A' ⟶ A) → LeftHomotopyClass A B → LeftHomotopyClass A' B

/-- Precomposition on classes is induced by precomposition on maps. -/
def precompValue : precompType.{v, u} :=
  fun {_} [_] [_] {_ _ _} [_] k =>
    Quot.lift (fun f => LeftHomotopyClass.mk (k ≫ f))
      (fun _ _ h => LeftHomotopyClass.sound (LeftHomotopyRel.precomp h k))

set_option linter.checkUnivs false in
def comparisonType :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C]
    {D : Type u'} [Category.{v'} D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {A B : C}, LeftHomotopyClass A B → (L.obj A ⟶ L.obj B)

/-- The canonical map is the descent of the localization functor's map on arrows. -/
abbrev comparisonValue : comparisonType.{v, u, v', u'} :=
  fun {_} [_] [_] {_} [_] L [_] {_ _} => leftHomotopyClassToHom L

def comparisonMkType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C]
    {D : Type u'} [Category.{v'} D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {A B : C} (f : A ⟶ B),
    comparisonValue L (LeftHomotopyClass.mk f) = L.map f

def comparisonBijectiveType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C]
    {D : Type u'} [Category.{v'} D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    (A B : C) [IsCofibrant A] [IsFibrant B],
    Function.Bijective (comparisonValue L (A := A) (B := B))

def comparisonPrecompType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C]
    {D : Type u'} [Category.{v'} D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {A' A B : C} [IsCofibrant A'] [IsCofibrant A] [IsFibrant B]
    (k : A' ⟶ A) (h : LeftHomotopyClass A B),
    comparisonValue L (precompValue k h) = L.map k ≫ comparisonValue L h

def comparisonPostcompType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C]
    {D : Type u'} [Category.{v'} D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {A B B' : C} [IsCofibrant A] [IsFibrant B] [IsFibrant B']
    (k : B ⟶ B') (h : LeftHomotopyClass A B),
    comparisonValue L (h.postcomp k) = comparisonValue L h ≫ L.map k

/-- For the Q05 model of the localization, the bijection sends each class
to the image of its representative under the specified replacement functor. -/
def replacementComparisonType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [FunctorialModelCategory C]
    (r : Model.Replacement C) (A B : C) [IsCofibrant A] [IsFibrant B],
    ∃ φ : LeftHomotopyClass A B →
        ((ModelLocalization.localizationFunctorValue r).obj A ⟶
          (ModelLocalization.localizationFunctorValue r).obj B),
      Function.Bijective φ ∧
        ∀ f : A ⟶ B, φ (LeftHomotopyClass.mk f) = (ModelLocalization.localizationFunctorValue r).map f

end DerivedFormalization.Specs.ModelBifibrantHom
