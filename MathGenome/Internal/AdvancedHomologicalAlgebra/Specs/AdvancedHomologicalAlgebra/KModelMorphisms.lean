import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.BoundedKModels
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedCategory

/-!
HA-R04, notes/002/advanced-homological-algebra.tex:1852–1880.
The abelian and universe conventions are at 1433–1438. The K-properties
are exactly the null-homotopy predicates of HA-R03, tested on all acyclic
integer cochain complexes. There are no boundedness or resolution hypotheses.
The arbitrary argument is allowed to be any object of K(A). Naturality is
stated as the commuting squares for pre- and postcomposition simultaneously,
including morphisms between K-models. The homotopy inverse conclusions concern
the specified cochain map, not just equivalence of the two objects.
As in HA-D03, the standard derived-category choice exists for every abelian A.
-/

set_option linter.checkUnivs false
universe w v u
open CategoryTheory
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
open Specs.AdvancedHomologicalAlgebra.BoundedKModels
open Specs.AdvancedHomologicalAlgebra.DerivedCategory

namespace Specs.AdvancedHomologicalAlgebra.KModelMorphisms

/-- Localization computes maps into every K-injective, with arbitrary source. -/
def kInjective_map_bijectiveType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X : K A) (I : CochainComplex A ℤ), KInjective I →
    Function.Bijective ((localizationQ A).map :
      (X ⟶ (Q A).obj I) → ((localizationQ A).obj X ⟶
        (localizationQ A).obj ((Q A).obj I)))

/-- Localization computes maps from every K-projective, with arbitrary target. -/
def kProjective_map_bijectiveType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (P : CochainComplex A ℤ) (X : K A), KProjective P →
    Function.Bijective ((localizationQ A).map :
      ((Q A).obj P ⟶ X) → ((localizationQ A).obj ((Q A).obj P) ⟶
        (localizationQ A).obj X))

/-- Both-variable naturality of the displayed K-injective bijections. -/
def kInjective_map_naturalType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X₁ X₂ : K A) (I₁ I₂ : CochainComplex A ℤ),
    KInjective I₁ → KInjective I₂ →
    ∀ (a : X₂ ⟶ X₁) (f : X₁ ⟶ (Q A).obj I₁)
      (b : (Q A).obj I₁ ⟶ (Q A).obj I₂),
    (localizationQ A).map (a ≫ f ≫ b) =
      (localizationQ A).map a ≫ (localizationQ A).map f ≫ (localizationQ A).map b

/-- Both-variable naturality of the displayed K-projective bijections. -/
def kProjective_map_naturalType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (P₁ P₂ : CochainComplex A ℤ) (X₁ X₂ : K A),
    KProjective P₁ → KProjective P₂ →
    ∀ (a : (Q A).obj P₂ ⟶ (Q A).obj P₁) (f : (Q A).obj P₁ ⟶ X₁)
      (b : X₁ ⟶ X₂),
    (localizationQ A).map (a ≫ f ≫ b) =
      (localizationQ A).map a ≫ (localizationQ A).map f ≫ (localizationQ A).map b

/-- A quasi-isomorphism between K-injectives has a two-sided homotopy inverse. -/
def kInjective_homotopyInverseType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (I J : CochainComplex A ℤ) (f : I ⟶ J),
    KInjective I → KInjective J → QuasiIso f →
    ∃ g : J ⟶ I, Nonempty (Homotopy (f ≫ g) (𝟙 I)) ∧
      Nonempty (Homotopy (g ≫ f) (𝟙 J))

/-- A quasi-isomorphism between K-projectives has a two-sided homotopy inverse. -/
def kProjective_homotopyInverseType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (P R : CochainComplex A ℤ) (f : P ⟶ R),
    KProjective P → KProjective R → QuasiIso f →
    ∃ g : R ⟶ P, Nonempty (Homotopy (f ≫ g) (𝟙 P)) ∧
      Nonempty (Homotopy (g ≫ f) (𝟙 R))

end Specs.AdvancedHomologicalAlgebra.KModelMorphisms
