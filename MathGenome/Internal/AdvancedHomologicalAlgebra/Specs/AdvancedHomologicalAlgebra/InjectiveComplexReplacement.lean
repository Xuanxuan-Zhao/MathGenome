import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! HA-R01, notes/002/advanced-homological-algebra.tex:1802–1816.
The chapter assumes abelian categories. Bounds on complexes concern terms,
whereas bounds on derived objects concern ordinary cohomology (HA-D06).
`IsStrictlyGE a` says precisely that every term in degree `< a` is zero.
No boundedness above or functorial choice of replacement is imposed. -/

set_option linter.checkUnivs false
universe w v u
open CategoryTheory CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.DerivedCategory

namespace Specs.AdvancedHomologicalAlgebra.InjectiveComplexReplacement

/-- Replacement of every strictly bounded below complex, retaining its given
lower bound and monicity in every degree. -/
def replacementType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (X : CochainComplex A ℤ) (a : ℤ), X.IsStrictlyGE a →
    ∃ (I : CochainComplex A ℤ) (f : X ⟶ I),
      (∀ n : ℤ, Mono (f.f n)) ∧ QuasiIso f ∧
      (∀ n : ℤ, Injective (I.X n)) ∧ I.IsStrictlyGE a

/-- A cohomological lower bound yields an injective representative with the
same lower term bound, by first passing to a strict model. -/
def derivedRepresentativeType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{w} A] (Y : D A) (a : ℤ),
    (∀ n : ℤ, n < a → IsZero ((HD A n).obj Y)) →
    ∃ I : CochainComplex A ℤ, (∀ n : ℤ, Injective (I.X n)) ∧
      I.IsStrictlyGE a ∧ Nonempty (Y ≅ _root_.DerivedCategory.Q.obj I)

/-- In particular every object of the full category D⁺ has such a representative. -/
def plusRepresentativeType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{w} A] (Y : _root_.DerivedCategory.Plus A),
    ∃ (a : ℤ) (I : CochainComplex A ℤ),
      (∀ n : ℤ, Injective (I.X n)) ∧ I.IsStrictlyGE a ∧
      Nonempty (Y.obj ≅ _root_.DerivedCategory.Q.obj I)

end Specs.AdvancedHomologicalAlgebra.InjectiveComplexReplacement
