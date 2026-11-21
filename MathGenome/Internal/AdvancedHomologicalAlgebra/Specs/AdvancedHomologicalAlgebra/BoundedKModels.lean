import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-!
HA-R03, notes/002/advanced-homological-algebra.tex:1832–1850.
The chapter assumes an arbitrary abelian category. All complexes are integer
cochain complexes. The lower and upper bounds below are on terms, expressed
by zero objects, and the acyclic test complexes have no boundedness hypothesis.
No enough-injectives or enough-projectives assumption is needed.
-/

set_option linter.checkUnivs false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace Specs.AdvancedHomologicalAlgebra.BoundedKModels

/-- Every map from an arbitrary acyclic complex to `I` is null-homotopic. -/
def KInjective {A : Type u} [Category.{v} A] [Abelian A]
    (I : CochainComplex A ℤ) : Prop :=
  ∀ (C : CochainComplex A ℤ) (f : C ⟶ I), C.Acyclic → Nonempty (Homotopy f 0)

/-- Every map from `P` to an arbitrary acyclic complex is null-homotopic. -/
def KProjective {A : Type u} [Category.{v} A] [Abelian A]
    (P : CochainComplex A ℤ) : Prop :=
  ∀ (C : CochainComplex A ℤ) (f : P ⟶ C), C.Acyclic → Nonempty (Homotopy f 0)

def kInjectiveType :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A], CochainComplex A ℤ → Prop

def kInjectiveValue : kInjectiveType := fun _A _ _ => KInjective

def kProjectiveType :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A], CochainComplex A ℤ → Prop

def kProjectiveValue : kProjectiveType := fun _A _ _ => KProjective

/-- The canonical predicate agrees with the library's null-homotopy class. -/
def kInjective_iffType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] (I : CochainComplex A ℤ),
    KInjective I ↔ I.IsKInjective

/-- The dual canonical predicate agrees with the library's class. -/
def kProjective_iffType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] (P : CochainComplex A ℤ),
    KProjective P ↔ P.IsKProjective

/-- A complex whose terms are injective and vanish below a bound is K-injective. -/
def boundedBelow_injectiveType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] (I : CochainComplex A ℤ) (b : ℤ),
    (∀ n : ℤ, n < b → IsZero (I.X n)) →
    (∀ n : ℤ, Injective (I.X n)) → KInjective I

/-- A complex whose terms are projective and vanish above a bound is K-projective. -/
def boundedAbove_projectiveType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] (P : CochainComplex A ℤ) (b : ℤ),
    (∀ n : ℤ, b < n → IsZero (P.X n)) →
    (∀ n : ℤ, Projective (P.X n)) → KProjective P

end Specs.AdvancedHomologicalAlgebra.BoundedKModels
