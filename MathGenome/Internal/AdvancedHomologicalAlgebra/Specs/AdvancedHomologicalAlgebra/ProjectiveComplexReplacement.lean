import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-! HA-R02, notes/002/advanced-homological-algebra.tex:1818–1829.
The complex assertion retains the specified upper term bound and includes
an epimorphism in every degree, as well as the quasi-isomorphism.
The derived assertion uses the ordinary cohomological bound defining D⁻. -/
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace Specs.AdvancedHomologicalAlgebra.ProjectiveComplexReplacement

def replacementType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [EnoughProjectives A]
    (X : CochainComplex A ℤ) (b : ℤ), X.IsStrictlyLE b →
    ∃ (P : CochainComplex A ℤ) (p : P ⟶ X),
      P.IsStrictlyLE b ∧ (∀ n : ℤ, Projective (P.X n)) ∧
      (∀ n : ℤ, Epi (p.f n)) ∧ QuasiIso p

def derivedRepresentativeType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [EnoughProjectives A]
    [HasDerivedCategory.{w} A] (X : _root_.DerivedCategory.Minus A),
    ∃ (b : ℤ) (P : CochainComplex A ℤ),
      P.IsStrictlyLE b ∧ (∀ n : ℤ, Projective (P.X n)) ∧
      Nonempty (X.obj ≅ _root_.DerivedCategory.Q.obj P)

end Specs.AdvancedHomologicalAlgebra.ProjectiveComplexReplacement
