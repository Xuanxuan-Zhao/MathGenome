import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Basic
import Mathlib.AlgebraicTopology.ModelCategory.PathObject

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe v u

namespace DerivedFormalization.Specs.ModelCylinderPath

set_option linter.checkUnivs false in
def cylinderType :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C], C → Type (max u v)

/-- A cylinder in the paper has a cofibration from the binary coproduct. -/
abbrev cylinderValue : cylinderType.{v, u} :=
  fun {_} [_] [_] A => {P : Cylinder A // P.IsGood}

set_option linter.checkUnivs false in
def pathObjectType :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C], C → Type (max u v)

/-- A path object in the paper has a fibration to the binary product. -/
abbrev pathObjectValue : pathObjectType.{v, u} :=
  fun {_} [_] [_] B => {P : PathObject B // P.IsGood}

set_option linter.checkUnivs false in
def goodCylinderType :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A : C}, cylinderValue A → Prop

/-- A good cylinder has a trivial fibration as its collapse. -/
abbrev goodCylinderValue : goodCylinderType.{v, u} :=
  fun {_} [_] [_] {_} P => P.val.IsVeryGood

set_option linter.checkUnivs false in
def goodPathObjectType :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {B : C}, pathObjectValue B → Prop

/-- A good path object has a trivial cofibration as its section. -/
abbrev goodPathObjectValue : goodPathObjectType.{v, u} :=
  fun {_} [_] [_] {_} P => P.val.IsVeryGood

def cylinderFoldType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A : C} (P : cylinderValue A),
    P.val.i ≫ P.val.π = codiag A

def pathObjectDiagonalType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {B : C} (P : pathObjectValue B),
    P.val.ι ≫ P.val.p = diag B

/-- The two endpoints and the collapse are natural in the object. -/
def functorialGoodCylinderType : Prop :=
  ∀ (C : Type u) [Category.{v} C] [FunctorialModelCategory C],
    ∃ (F : C ⥤ C) (j₀ j₁ : 𝟭 C ⟶ F) (r : F ⟶ 𝟭 C),
      ∀ A : C,
        j₀.app A ≫ r.app A = 𝟙 A ∧
        j₁.app A ≫ r.app A = 𝟙 A ∧
        cofibrations C (coprod.desc (j₀.app A) (j₁.app A)) ∧
        trivialFibrations C (r.app A)

/-- The section and the two evaluations are natural in the object. -/
def functorialGoodPathObjectType : Prop :=
  ∀ (C : Type u) [Category.{v} C] [FunctorialModelCategory C],
    ∃ (F : C ⥤ C) (s : 𝟭 C ⟶ F) (e₀ e₁ : F ⟶ 𝟭 C),
      ∀ B : C,
        s.app B ≫ e₀.app B = 𝟙 B ∧
        s.app B ≫ e₁.app B = 𝟙 B ∧
        trivialCofibrations C (s.app B) ∧
        fibrations C (prod.lift (e₀.app B) (e₁.app B))

def cylinderEndpointsType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A : C} [IsCofibrant A]
    (P : cylinderValue A),
    trivialCofibrations C P.val.i₀ ∧ trivialCofibrations C P.val.i₁

def pathObjectEvaluationsType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {B : C} [IsFibrant B]
    (P : pathObjectValue B),
    trivialFibrations C P.val.p₀ ∧ trivialFibrations C P.val.p₁

end DerivedFormalization.Specs.ModelCylinderPath
