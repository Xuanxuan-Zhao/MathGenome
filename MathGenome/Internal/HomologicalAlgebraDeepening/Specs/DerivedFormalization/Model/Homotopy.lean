import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.CylinderPath
import Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy

open CategoryTheory HomotopicalAlgebra

universe v u

namespace DerivedFormalization.Specs.ModelHomotopy

open ModelCylinderPath

set_option linter.checkUnivs false in
def homotopyRelationType :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A B : C},
    (A ⟶ B) → (A ⟶ B) → Prop

/-- Left homotopy is realized on a cylinder of Q02. -/
abbrev leftHomotopicValue : homotopyRelationType.{v, u} :=
  fun {_} [_] [_] {A} {B} f g =>
    ∃ (P : cylinderValue A) (H : P.val.I ⟶ B),
      P.val.i₀ ≫ H = f ∧ P.val.i₁ ≫ H = g

/-- Right homotopy is realized on a path object of Q02. -/
abbrev rightHomotopicValue : homotopyRelationType.{v, u} :=
  fun {_} [_] [_] {A} {B} f g =>
    ∃ (P : pathObjectValue B) (K : A ⟶ P.val.P),
      K ≫ P.val.p₀ = f ∧ K ≫ P.val.p₁ = g

/-- Comparison with the Mathlib relation used to form left homotopy classes. -/
def leftHomotopyRelType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A B : C} (f g : A ⟶ B),
    leftHomotopicValue f g ↔ LeftHomotopyRel f g

/-- Comparison with the Mathlib relation used to form right homotopy classes. -/
def rightHomotopyRelType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A B : C} (f g : A ⟶ B),
    rightHomotopicValue f g ↔ RightHomotopyRel f g

def leftIffRightType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A B : C}
    [IsCofibrant A] [IsFibrant B] (f g : A ⟶ B),
    leftHomotopicValue f g ↔ rightHomotopicValue f g

def homotopyEquivalenceType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] (A B : C)
    [IsCofibrant A] [IsFibrant B],
    Equivalence (leftHomotopicValue (A := A) (B := B)) ∧
      Equivalence (rightHomotopicValue (A := A) (B := B))

def fixedCylinderType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A B : C}
    [IsCofibrant A] [IsFibrant B] (P : cylinderValue A) (f g : A ⟶ B),
    leftHomotopicValue f g ↔
      ∃ H : P.val.I ⟶ B, P.val.i₀ ≫ H = f ∧ P.val.i₁ ≫ H = g

def fixedPathObjectType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A B : C}
    [IsCofibrant A] [IsFibrant B] (P : pathObjectValue B) (f g : A ⟶ B),
    rightHomotopicValue f g ↔
      ∃ K : A ⟶ P.val.P, K ≫ P.val.p₀ = f ∧ K ≫ P.val.p₁ = g

def precompType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A' A B : C}
    [IsCofibrant A'] [IsCofibrant A] [IsFibrant B] {f g : A ⟶ B},
    leftHomotopicValue f g → ∀ k : A' ⟶ A, leftHomotopicValue (k ≫ f) (k ≫ g)

def postcompType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A B B' : C}
    [IsCofibrant A] [IsFibrant B] [IsFibrant B'] {f g : A ⟶ B},
    leftHomotopicValue f g → ∀ k : B ⟶ B', leftHomotopicValue (f ≫ k) (g ≫ k)

def weakEquivalenceType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] {A B : C}
    [IsCofibrant A] [IsFibrant B] {f g : A ⟶ B},
    leftHomotopicValue f g → (weakEquivalences C f ↔ weakEquivalences C g)

end DerivedFormalization.Specs.ModelHomotopy
