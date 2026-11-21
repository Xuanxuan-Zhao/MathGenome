import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GoodTruncations
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-! HA-D06, source lines 1636–1677. Bounds are existential, on terms for K,
and on ordinary cohomology for D. The bounded homotopy category is represented
as a full subcategory of K⁻; its composite inclusion into K is fully faithful.
This nested representation retains exactly the strictly bounded complexes. -/
set_option linter.checkUnivs false
universe w v u
open CategoryTheory CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
open Specs.AdvancedHomologicalAlgebra.DerivedCategory

namespace Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Upper bounds concern the terms of the underlying complex. -/
def minus : ObjectProperty (K A) := fun X => ∃ b : ℤ, CochainComplex.IsStrictlyLE X.as b
abbrev KMinus := (minus A).FullSubcategory
abbrev minusInclusion : KMinus A ⥤ K A := (minus A).ι

/-- Lower term bounds inside the upper term bounded category. -/
def boundedInMinus : ObjectProperty (KMinus A) :=
  (HomotopyCategory.plus A).inverseImage (minusInclusion A)
abbrev KBounded := (boundedInMinus A).FullSubcategory
abbrev boundedInclusion : KBounded A ⥤ K A :=
  (boundedInMinus A).ι ⋙ minusInclusion A

variable [HasDerivedCategory.{w} A]

noncomputable def QMinus : KMinus A ⥤ _root_.DerivedCategory.Minus A :=
  _root_.DerivedCategory.TStructure.t.minus.lift
    (minusInclusion A ⋙ localizationQ A) (by
      rintro ⟨X, b, hb⟩
      obtain ⟨X : CochainComplex A ℤ, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      have hb : X.IsStrictlyLE b := hb
      exact ⟨b, _root_.DerivedCategory.TStructure.t.isLE_of_iso
        ((_root_.DerivedCategory.quotientCompQhIso A).symm.app X) b⟩)

noncomputable def QBounded : KBounded A ⥤ _root_.DerivedCategory.Bounded A :=
  _root_.DerivedCategory.TStructure.t.bounded.lift
    (boundedInclusion A ⋙ localizationQ A) (by
      rintro ⟨⟨X, b, hb⟩, ha⟩
      obtain ⟨X : CochainComplex A ℤ, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      have hb : X.IsStrictlyLE b := hb
      obtain ⟨a, ha⟩ := (HomotopyCategory.plus_quotient_obj_iff X).mp ha
      exact ⟨⟨a, _root_.DerivedCategory.TStructure.t.isGE_of_iso
        ((_root_.DerivedCategory.quotientCompQhIso A).symm.app X) a⟩,
        ⟨b, _root_.DerivedCategory.TStructure.t.isLE_of_iso
        ((_root_.DerivedCategory.quotientCompQhIso A).symm.app X) b⟩⟩)

/-- These are precisely the quasi-isomorphisms, restricted along the inclusions. -/
def WMinus : MorphismProperty (KMinus A) :=
  (HomotopyCategory.quasiIso A (.up ℤ)).inverseImage (minusInclusion A)
def WBounded : MorphismProperty (KBounded A) :=
  (HomotopyCategory.quasiIso A (.up ℤ)).inverseImage (boundedInclusion A)


def homotopyBoundsType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A],
    (∀ X : K A, minus A X ↔ ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (X.as.X i)) ∧
    (∀ X : KMinus A, boundedInMinus A X ↔
      ∃ a : ℤ, ∀ i : ℤ, i < a → IsZero (X.obj.as.X i))

def cohomologyBoundsType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X : D A),
    (_root_.DerivedCategory.TStructure.t.plus X ↔
      ∃ a : ℤ, ∀ i : ℤ, i < a → IsZero ((HD A i).obj X)) ∧
    (_root_.DerivedCategory.TStructure.t.minus X ↔
      ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((HD A i).obj X)) ∧
    (_root_.DerivedCategory.TStructure.t.bounded X ↔
      (∃ a : ℤ, ∀ i : ℤ, i < a → IsZero ((HD A i).obj X)) ∧
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((HD A i).obj X)))

/-- Models retain the specified bounds, including the two-sided case. -/
def strictModelsType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X : D A) (a b : ℤ),
    ((∀ i : ℤ, i < a → IsZero ((HD A i).obj X)) →
      ∃ L : CochainComplex A ℤ, L.IsStrictlyGE a ∧
        Nonempty (X ≅ _root_.DerivedCategory.Q.obj L)) ∧
    ((∀ i : ℤ, b < i → IsZero ((HD A i).obj X)) →
      ∃ L : CochainComplex A ℤ, L.IsStrictlyLE b ∧
        Nonempty (X ≅ _root_.DerivedCategory.Q.obj L)) ∧
    ((∀ i : ℤ, i < a → IsZero ((HD A i).obj X)) →
      (∀ i : ℤ, b < i → IsZero ((HD A i).obj X)) →
      ∃ L : CochainComplex A ℤ, L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
        Nonempty (X ≅ _root_.DerivedCategory.Q.obj L))

def homotopyTriangulatedType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A],
    (HomotopyCategory.plus A).IsTriangulated ∧
      ∃ h : (minus A).IsTriangulated, letI := h; (boundedInMinus A).IsTriangulated

/-- The nested bounded representation embeds fully faithfully in unbounded K,
and both inclusions preserve distinguished triangles. -/
def homotopyInclusionsType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A],
    Nonempty ((minusInclusion A).FullyFaithful) ∧
    Nonempty ((boundedInclusion A).FullyFaithful) ∧
    ∃ hm : (minus A).IsTriangulated, letI := hm;
      ∃ hb : (boundedInMinus A).IsTriangulated, letI := hb;
        (minusInclusion A).IsTriangulated ∧ (boundedInclusion A).IsTriangulated

/-- The restrictions of Qh preserve the inherited triangulated structures. -/
def exactQuotientsType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A],
    ∃ hm : (minus A).IsTriangulated, letI := hm;
      ∃ hb : (boundedInMinus A).IsTriangulated, letI := hb;
        (∃ cm : (QMinus A).CommShift ℤ, letI := cm; (QMinus A).IsTriangulated) ∧
        (∃ cb : (QBounded A).CommShift ℤ, letI := cb; (QBounded A).IsTriangulated)

def derivedTriangulatedType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A],
    (_root_.DerivedCategory.TStructure.t (C := A)).plus.IsTriangulated ∧
    (_root_.DerivedCategory.TStructure.t (C := A)).minus.IsTriangulated ∧
    (_root_.DerivedCategory.TStructure.t (C := A)).bounded.IsTriangulated

/-- The actual restrictions of Qh are localization functors, not merely
abstract equivalences of unrelated categories. -/
def localizationType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A],
    (_root_.DerivedCategory.Plus.Qh (C := A)).IsLocalization
      (HomotopyCategory.Plus.quasiIso A) ∧
    (QMinus A).IsLocalization (WMinus A) ∧
    (QBounded A).IsLocalization (WBounded A)

/-- Explicit equivalences from the ordinary localizations, compatible with Qh. -/
def equivalencesType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A],
    (∃ e : (HomotopyCategory.Plus.quasiIso A).Localization ≌
        _root_.DerivedCategory.Plus A,
      Nonempty ((HomotopyCategory.Plus.quasiIso A).Q ⋙ e.functor ≅
        _root_.DerivedCategory.Plus.Qh)) ∧
    (∃ e : (WMinus A).Localization ≌ _root_.DerivedCategory.Minus A,
      Nonempty ((WMinus A).Q ⋙ e.functor ≅ QMinus A)) ∧
    (∃ e : (WBounded A).Localization ≌ _root_.DerivedCategory.Bounded A,
      Nonempty ((WBounded A).Q ⋙ e.functor ≅ QBounded A))

end Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
