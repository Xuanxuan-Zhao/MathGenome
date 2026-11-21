import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison

/-! HA-R12, notes/002/advanced-homological-algebra.tex:2092–2118.
The chapter convention requires additive functors between abelian categories.
Only A and B require enough injectives. The fixed functors and comparisons are
those of HA-R06; acyclicity is exactly the stalk comparison of HA-R08.
Composition is written in Lean's diagrammatic order, so `F ⋙ G` denotes GF.
-/
noncomputable section
set_option linter.checkUnivs false
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison

namespace Specs.AdvancedHomologicalAlgebra.RightDerivedComposition

section
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- The comparison before localization: first η_G on F_K, then RG(η_F).
The first two factors identify termwise composition with (GF)_K. -/
def inputComparisonValue : (F ⋙ G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
    DerivedCategory.Plus.Qh ⋙ (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) :=
  whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv
      DerivedCategory.Plus.Qh ≫
    (associator F.mapHomotopyCategoryPlus G.mapHomotopyCategoryPlus
      DerivedCategory.Plus.Qh).hom ≫
    whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnith ≫
    (associator F.mapHomotopyCategoryPlus DerivedCategory.Plus.Qh
      G.rightDerivedFunctorPlus).inv ≫
    whiskerRight F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlus ≫
    (associator DerivedCategory.Plus.Qh F.rightDerivedFunctorPlus
      G.rightDerivedFunctorPlus).hom

/-- The canonical map is induced by the total right derived universal property,
without any acyclicity assumption. -/
def comparisonValue : (F ⋙ G).rightDerivedFunctorPlus ⟶
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  (F ⋙ G).rightDerivedFunctorPlus.rightDerivedDesc
    (F ⋙ G).rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso A)
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) (inputComparisonValue F G)
end

def comparisonDeclarationType :=
  ∀ {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
    [Category.{v₃} C] [Abelian C]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive],
    (F ⋙ G).rightDerivedFunctorPlus ⟶
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus

noncomputable def comparisonDeclarationValue : comparisonDeclarationType := @comparisonValue

/-- Characterization by HA-R05, including uniqueness among all transformations. -/
def comparisonUniversalType : Prop :=
  ∀ (A : Type u₁) (B : Type u₂) (C : Type u₃)
    [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
    [Category.{v₃} C] [Abelian C]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive],
    (F ⋙ G).rightDerivedFunctorPlusUnith ≫
        whiskerLeft DerivedCategory.Plus.Qh (comparisonValue F G) = inputComparisonValue F G ∧
    ∀ α : (F ⋙ G).rightDerivedFunctorPlus ⟶
        F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus,
      (F ⋙ G).rightDerivedFunctorPlusUnith ≫
        whiskerLeft DerivedCategory.Plus.Qh α = inputComparisonValue F G →
      α = comparisonValue F G

/-- The full equivalence of HA-R12. The left side quantifies over every object
of D⁺(A), and the right over every injective object of A. -/
def comparisonIsoIffType : Prop :=
  ∀ (A : Type u₁) (B : Type u₂) (C : Type u₃)
    [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
    [Category.{v₃} C] [Abelian C]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G],
    (∀ X : DerivedCategory.Plus A, IsIso ((comparisonValue F G).app X)) ↔
      ∀ I : A, Injective I → rightAcyclicValue G (F.obj I)

end Specs.AdvancedHomologicalAlgebra.RightDerivedComposition
