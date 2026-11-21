import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-!
HA-R07, source 1938–1963, including its comparison, model computation,
shift convention and natural transformations (R05 and the paragraph following R07).
The only resolution hypothesis is enough projectives in the source.
-/
set_option linter.checkUnivs false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty

namespace Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor

variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B]

section Shifts
variable [(minus A).IsTriangulated] [(minus B).IsTriangulated]

/-- The standard termwise cochain shift, with its usual differential sign. -/
@[instance_reducible]
noncomputable def termwiseShift (F : A ⥤ B) [F.Additive] :
    (termwiseMinusValue F).CommShift ℤ := by
  dsimp [termwiseMinusValue]
  infer_instance

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]

@[instance_reducible]
noncomputable def quotientShift : (QMinus A).CommShift ℤ :=
  ObjectProperty.commShiftLift ..

@[instance_reducible]
noncomputable def inputShift (F : A ⥤ B) [F.Additive] : (minusUValue F).CommShift ℤ := by
  letI := termwiseShift F
  letI : (QMinus B).CommShift ℤ := quotientShift
  exact inferInstanceAs ((termwiseMinusValue F ⋙ QMinus B).CommShift ℤ)

/-- Full total left derived data, including exactness and the standard comparison.
The universal property is inherited from R05 and tests all target functors. -/
structure ExactLeftData (F : A ⥤ B) [F.Additive] extends
    LeftData (QMinus A) (minusUValue F) where
  commShift : functor.CommShift ℤ
  triangulated : letI := commShift; functor.IsTriangulated
  counit_shift : letI := commShift
    letI : (QMinus A).CommShift ℤ := quotientShift
    letI : (minusUValue F).CommShift ℤ := inputShift F
    NatTrans.CommShift counit ℤ
  model_iso : ∀ P : KMinus A, (∀ n : ℤ, Projective (P.obj.as.X n)) →
    IsIso (counit.app P)
end Shifts

/-- Existence with arbitrary additive F; no right exactness or injectives. -/
def existenceType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [EnoughProjectives A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] (F : A ⥤ B) [F.Additive],
    ∃ (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated),
      letI := hA; letI := hB
      Nonempty (ExactLeftData.{u, v, u', v', w, w'} F)

/-- Every projective replacement computes LF, with its specified comparison.
WMinus is precisely the quasi-isomorphism property from D06. The displayed
identity identifies the counit with F(p) after the computation isomorphism. -/
def computationType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated),
    letI := hA; letI := hB
    ∀ (F : A ⥤ B) [F.Additive] (R : ExactLeftData.{u, v, u', v', w, w'} F)
      (P X : KMinus A) (p : P ⟶ X),
      (∀ n : ℤ, Projective (P.obj.as.X n)) → WMinus A p →
      ∃ e : R.functor.obj ((QMinus A).obj X) ≅ (minusUValue F).obj P,
        e.hom ≫ (minusUValue F).map p = R.counit.app X ∧
        R.functor.map ((QMinus A).map p) ≫ e.hom = R.counit.app P

/-- Natural transformations are derived uniquely and use the same model
identifications. This is the R05 comparison square, specialized to R07. -/
def transformationsType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated),
    letI := hA; letI := hB
    ∀ (F G : A ⥤ B) [F.Additive] [G.Additive]
      (R : ExactLeftData.{u, v, u', v', w, w'} F)
      (S : ExactLeftData.{u, v, u', v', w, w'} G) (τ : F ⟶ G),
      ∃! α : R.functor ⟶ S.functor,
        whiskerLeft (QMinus A) α ≫ S.counit = R.counit ≫ minusUMapValue F G τ

/-- On every projective model, the transformation is exactly termwise τ
under the comparison isomorphisms, independently of resolution choices. -/
def transformationModelsType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated),
    letI := hA; letI := hB
    ∀ (F G : A ⥤ B) [F.Additive] [G.Additive]
      (R : ExactLeftData.{u, v, u', v', w, w'} F)
      (S : ExactLeftData.{u, v, u', v', w, w'} G) (τ : F ⟶ G)
      (α : R.functor ⟶ S.functor),
      whiskerLeft (QMinus A) α ≫ S.counit = R.counit ≫ minusUMapValue F G τ →
      ∀ (P : KMinus A) (hP : ∀ n : ℤ, Projective (P.obj.as.X n)),
        letI := S.model_iso P hP
        α.app ((QMinus A).obj P) = R.counit.app P ≫
          (minusUMapValue F G τ).app P ≫ inv (S.counit.app P)

end Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
