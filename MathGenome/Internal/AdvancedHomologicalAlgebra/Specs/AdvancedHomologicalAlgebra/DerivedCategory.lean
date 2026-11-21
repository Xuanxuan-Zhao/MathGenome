import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedFractions
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TriangleExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
HA-D03, notes/002/advanced-homological-algebra.tex:1515–1547.
The abelian and universe conventions are at 1433–1438; cochain shifts at
107–109 and source distinguished triangles at HA-K05. Complexes are unbounded.
The chosen derived category has Hom universe w. This is no smallness restriction:
`standardChoice` supplies a choice at w = max u v for every abelian category.
The Verdier assertion includes localization at the actual acyclic cone class,
the image description of triangles, and exact descent for functors killing
acyclics. The ordinary localization equivalence supplies uniqueness, including
natural transformations, of such descents. Cohomology is ordinary cohomology.
-/

set_option linter.checkUnivs false
universe w v u v' u'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
open Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory
open Specs.AdvancedHomologicalAlgebra.DerivedFractions
open Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory

namespace Specs.AdvancedHomologicalAlgebra.DerivedCategory

abbrev D (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A] :=
  _root_.DerivedCategory A
noncomputable abbrev localizationQ (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : K A ⥤ D A := _root_.DerivedCategory.Qh
noncomputable abbrev HD (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (n : ℤ) : D A ⥤ A :=
  _root_.DerivedCategory.homologyFunctor A n

def standardChoiceType := ∀ (A : Type u) [Category.{v} A] [Abelian A],
  HasDerivedCategory.{max u v} A
noncomputable def standardChoiceValue : standardChoiceType := HasDerivedCategory.standard

def derivedCategoryType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A], Type (max u v)
def derivedCategoryValue : derivedCategoryType := fun A _ _ _ => D A

def quotientType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A], K A ⥤ D A
noncomputable def quotientValue : quotientType := localizationQ

def cohomologyType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A], ℤ → (D A ⥤ A)
noncomputable def cohomologyValue : cohomologyType := HD

def cohomologyFactorsType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (n : ℤ), localizationQ A ⋙ HD A n ≅ H A n
noncomputable def cohomologyFactorsValue : cohomologyFactorsType :=
  _root_.DerivedCategory.homologyFunctorFactorsh

def localizationType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A], (localizationQ A).IsLocalization (W A)

def verdierLocalizationType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A], (localizationQ A).IsLocalization (acyclicObjects A).trW

def triangulatedType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A], IsTriangulated (D A)

def preservesTrianglesType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (T : Triangle (K A)), Distinguished T →
  (localizationQ A).mapTriangle.obj T ∈ distTriang (D A)

def distinguishedType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (T : Triangle (D A)),
  T ∈ distTriang (D A) ↔ ∃ T₀ : Triangle (K A),
    Distinguished T₀ ∧ Nonempty (T ≅ (localizationQ A).mapTriangle.obj T₀)

def isIso_iffType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (X Y : D A) (f : X ⟶ Y),
  IsIso f ↔ ∀ n : ℤ, IsIso ((HD A n).map f)

def isZero_iffType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (X : D A),
  IsZero X ↔ ∀ n : ℤ, IsZero ((HD A n).obj X)

def kernelType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (X : K A),
  IsZero ((localizationQ A).obj X) ↔ acyclicObjects A X

/-- All overlapping six-term windows in the descended long cohomology sequence. -/
def cohomologyExactType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (T : Triangle (D A)), T ∈ distTriang (D A) →
  TriangleExactSequences.LongExact (HD A 0) T

/-- The localization universal property, with its actual precomposition functor. -/
def universalType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (E : Type u') [Category.{v'} E],
  (D A ⥤ E) ≌ (W A).FunctorsInverting E
noncomputable def universalValue : universalType := fun A _ _ _ E _ =>
  Localization.functorEquivalence (localizationQ A) (W A) E

section Exact
variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (E : Type u') [Category.{v'} E] [HasShift E ℤ] [Preadditive E]
  [HasZeroObject E] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
  (F : K A ⥤ E) [F.CommShift ℤ]

/-- An exact descent includes the comparison of shifts for its factorization. -/
structure ExactLift where
  functor : D A ⥤ E
  commShift : functor.CommShift ℤ
  iso : localizationQ A ⋙ functor ≅ F
  compatible : letI := commShift; NatTrans.CommShift iso.hom ℤ
  exact : letI := commShift; functor.IsTriangulated
end Exact

/-- For exact functors, killing acyclics is exactly inverting quasi-isomorphisms. -/
def inverts_iff_killsType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  (E : Type u') [Category.{v'} E] [HasShift E ℤ] [Preadditive E]
  [HasZeroObject E] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
  (F : K A ⥤ E) [F.CommShift ℤ] [F.IsTriangulated],
  (W A).IsInvertedBy F ↔ ∀ X : K A, acyclicObjects A X → IsZero (F.obj X)

/-- Existence of the exact factorization; `universal` above gives its uniqueness. -/
def exactDescentType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A]
  (E : Type u') [Category.{v'} E] [HasShift E ℤ] [Preadditive E]
  [HasZeroObject E] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
  (F : K A ⥤ E) [F.CommShift ℤ] [F.IsTriangulated],
  (∀ X : K A, acyclicObjects A X → IsZero (F.obj X)) → Nonempty (ExactLift A E F)

end Specs.AdvancedHomologicalAlgebra.DerivedCategory
