import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.SimpleObjects
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.WeightBounds
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RingTheory.FiniteLength

/-! Weight bounds, abelianness, finite length, and simple objects of finite category O. -/

open CategoryTheory CategoryTheory.Limits
open Specs.LieAlgebrasAndRepresentations.VermaModules (U)

namespace Specs.RepTheorySurvey.CategoryO

universe u v

/-- Each object of the finite category O has finite length over the enveloping algebra. -/
def CategoryOFiniteLengthType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X : category_value.{u, v} D), IsFiniteLength (U g) X.obj

/-- Category O is abelian with its inherited addition on morphisms. Its inclusion
into left enveloping modules creates kernels and cokernels. -/
def CategoryOAbelianType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g),
    (∃ A : Abelian (category_value.{u, v} D),
      A.toPreadditive = inferInstanceAs (Preadditive (category_value.{u, v} D))) ∧
    ∀ {X Y : category_value.{u, v} D} (f : X ⟶ Y),
      Nonempty (CreatesLimit (parallelPair f 0) (objects_value D).ι) ∧
      Nonempty (CreatesColimit (parallelPair f 0) (objects_value D).ι)

/-- The complete finite category O theorem (LO02). -/
def CategoryOTheoremType : Prop :=
  WeightBounds.BoundsType.{u, v} ∧
  CategoryOAbelianType.{u, v} ∧
  CategoryOFiniteLengthType.{u, v} ∧
  SimpleObjects.SimpleQuotientInOType.{u} ∧
  SimpleObjects.SimpleQuotientEquivIffType.{u} ∧
  SimpleObjects.ClassificationType.{u, v}

end Specs.RepTheorySurvey.CategoryO
