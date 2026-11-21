import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! HA-R09, source lines 2001–2040. The systems below use precisely the
resolution-computed values and derived-triangle boundaries of HA-R09-Values.
All exactness and universality assertions are propositions, not certificates
assumed as part of the definition of the derived system. -/
noncomputable section
set_option linter.checkUnivs false
set_option linter.unusedVariables false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

namespace Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors

variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B]

/-- Exactness of a pair, including the assertion that its composite is zero. -/
structure ExactPair {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop where
  zero : f ≫ g = 0
  exact : (ShortComplex.mk f g zero).Exact

/-- A nonnegative cohomological system; its axioms are stated separately. -/
structure CohomologicalSystem (A : Type u) (B : Type u')
    [Category.{v} A] [Abelian A] [Category.{v'} B] [Abelian B] where
  value : ℕ → A ⥤ B
  δ : ∀ {S : ShortComplex A}, S.ShortExact → ∀ n : ℕ,
    (value n).obj S.X₃ ⟶ (value (n + 1)).obj S.X₁

structure IsCohomological (T : CohomologicalSystem A B) : Prop where
  additive : ∀ n, (T.value n).Additive
  naturality : ∀ {S S' : ShortComplex A} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (f : S ⟶ S') (n : ℕ),
    (T.value n).map f.τ₃ ≫ T.δ hS' n = T.δ hS n ≫ (T.value (n + 1)).map f.τ₁
  exact₁ : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    ExactPair (T.δ hS n) ((T.value (n + 1)).map S.f)
  exact₂ : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    ExactPair ((T.value n).map S.f) ((T.value n).map S.g)
  exact₃ : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    ExactPair ((T.value n).map S.g) (T.δ hS n)
  mono_zero : ∀ {S : ShortComplex A}, S.ShortExact → Mono ((T.value 0).map S.f)

structure CohomologicalMorphism (T U : CohomologicalSystem A B) where
  component : ∀ n, T.value n ⟶ U.value n
  comm : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    T.δ hS n ≫ (component (n + 1)).app S.X₁ =
      (component n).app S.X₃ ≫ U.δ hS n

def IsUniversalCohomological (T : CohomologicalSystem A B) : Prop :=
  ∀ (U : CohomologicalSystem A B), IsCohomological U →
    ∀ α : T.value 0 ⟶ U.value 0,
      ∃! φ : CohomologicalMorphism T U, φ.component 0 = α

/-- The homological direction is covariant, with boundary from degree n+1
on the quotient to degree n on the subobject. -/
structure HomologicalSystem (A : Type u) (B : Type u')
    [Category.{v} A] [Abelian A] [Category.{v'} B] [Abelian B] where
  value : ℕ → A ⥤ B
  δ : ∀ {S : ShortComplex A}, S.ShortExact → ∀ n : ℕ,
    (value (n + 1)).obj S.X₃ ⟶ (value n).obj S.X₁

structure IsHomological (T : HomologicalSystem A B) : Prop where
  additive : ∀ n, (T.value n).Additive
  naturality : ∀ {S S' : ShortComplex A} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (f : S ⟶ S') (n : ℕ),
    (T.value (n + 1)).map f.τ₃ ≫ T.δ hS' n = T.δ hS n ≫ (T.value n).map f.τ₁
  exact₁ : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    ExactPair (T.δ hS n) ((T.value n).map S.f)
  exact₂ : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    ExactPair ((T.value n).map S.f) ((T.value n).map S.g)
  exact₃ : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    ExactPair ((T.value (n + 1)).map S.g) (T.δ hS n)
  epi_zero : ∀ {S : ShortComplex A}, S.ShortExact → Epi ((T.value 0).map S.g)

structure HomologicalMorphism (T U : HomologicalSystem A B) where
  component : ∀ n, T.value n ⟶ U.value n
  comm : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    T.δ hS n ≫ (component n).app S.X₁ =
      (component (n + 1)).app S.X₃ ≫ U.δ hS n

/-- The homological universal property is terminal: a map into degree zero
extends uniquely to a map into the derived homological system. -/
def IsUniversalHomological (T : HomologicalSystem A B) : Prop :=
  ∀ (U : HomologicalSystem A B), IsHomological U →
    ∀ α : U.value 0 ⟶ T.value 0,
      ∃! φ : HomologicalMorphism U T, φ.component 0 = α

section Right
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]

def rightSystem (F : A ⥤ B) [F.Additive] : CohomologicalSystem A B where
  value := rightValue F
  δ := rightBoundary F

end Right
section Left
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  [(minus A).IsTriangulated] [(minus B).IsTriangulated]

def leftSystem (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F) : HomologicalSystem A B where
  value := leftValue F R
  δ := leftBoundary F R
end Left

/-- All three types of consecutive pairs in the long exact sequence, together
with the initial zero, additivity, and naturality for every SES morphism. -/
def rightDeltaType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F],
    IsCohomological (rightSystem F)

def leftDeltaType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughProjectives A]
    (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated),
    letI := hA; letI := hB
    ∀ (F : A ⥤ B) [F.Additive] (R : ExactLeftData.{u, v, u', v', w, w'} F)
      [PreservesFiniteColimits F], IsHomological (leftSystem F R)

/-- Extension from F along the degree-zero map induced by the derived unit. -/
def rightUniversalType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F],
    ∀ (U : CohomologicalSystem A B), IsCohomological U →
      ∀ α : F ⟶ U.value 0,
        ∃! φ : CohomologicalMorphism (rightSystem F) U,
          rightDegreeZeroUnit F ≫ φ.component 0 = α

/-- Extension into F uses the degree-zero map induced by the derived counit. -/
def leftUniversalType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughProjectives A]
    (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated),
    letI := hA; letI := hB
    ∀ (F : A ⥤ B) [F.Additive] (R : ExactLeftData.{u, v, u', v', w, w'} F)
      [PreservesFiniteColimits F],
    ∀ (U : HomologicalSystem A B), IsHomological U →
      ∀ α : U.value 0 ⟶ F,
        ∃! φ : HomologicalMorphism U (leftSystem F R),
          φ.component 0 ≫ leftDegreeZeroCounit F R = α

def rightEffacementType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (X : A),
    ∃ (I : A) (i : X ⟶ I), Injective I ∧ Mono i ∧
      ∀ n : ℕ, (rightValue F (n + 1)).map i = 0

def leftEffacementType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughProjectives A]
    (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated),
    letI := hA; letI := hB
    ∀ (F : A ⥤ B) [F.Additive] (R : ExactLeftData.{u, v, u', v', w, w'} F) (X : A),
      ∃ (P : A) (p : P ⟶ X), Projective P ∧ Epi p ∧
        ∀ n : ℕ, (leftValue F R (n + 1)).map p = 0

end Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
