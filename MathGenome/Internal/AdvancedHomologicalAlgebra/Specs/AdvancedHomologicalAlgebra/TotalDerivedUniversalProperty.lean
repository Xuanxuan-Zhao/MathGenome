import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels

/-!
HA-R05, notes/002/advanced-homological-algebra.tex, lines 1767–1775 and 1881–1908.
The comparison is part of the data. Its universal property quantifies over ALL
functors on the localized source, without exactness or additivity restrictions.
The categorical arguments are stated for arbitrary Q and U, hence apply to
both bounded localizations below, and do not assert existence of resolutions.
Lean writes Q ⋙ R for the source's ordinary composition R Q.
-/
set_option linter.checkUnivs false
universe u₁ v₁ u₂ v₂ u₃ v₃ u v u' v' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels

namespace Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty

/-- Right comparison data with exactly the bijections in HA-R05. -/
structure RightData {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (Q : C ⥤ D) (U : C ⥤ E) where
  functor : D ⥤ E
  unit : U ⟶ Q ⋙ functor
  universal : ∀ H : D ⥤ E,
    Function.Bijective (fun α : functor ⟶ H => unit ≫ whiskerLeft Q α)

/-- Left comparison data, with the reverse comparison and reverse Nat sets. -/
structure LeftData {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (Q : C ⥤ D) (U : C ⥤ E) where
  functor : D ⥤ E
  counit : Q ⋙ functor ⟶ U
  universal : ∀ H : D ⥤ E,
    Function.Bijective (fun α : H ⟶ functor => whiskerLeft Q α ≫ counit)

section Bounded
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B]

/-- F_K on K⁺: the library quotient of termwise application. -/
def termwisePlusType := ∀ (F : A ⥤ B) [F.Additive],
  HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B

def termwisePlusValue : termwisePlusType (A := A) (B := B) :=
  fun F _ => F.mapHomotopyCategoryPlus

/-- F_K on the shared K⁻ model, retaining upper bounds on terms. -/
def termwiseMinusType := ∀ (F : A ⥤ B) [F.Additive], KMinus A ⥤ KMinus B

def termwiseMinusValue : termwiseMinusType (A := A) (B := B) := fun F _ =>
  (minus B).lift (minusInclusion A ⋙ F.mapHomotopyCategory (.up ℤ)) (by
    rintro ⟨X, b, hb⟩
    obtain ⟨X : CochainComplex A ℤ, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    have : X.IsStrictlyLE b := hb
    exact ⟨b, inferInstanceAs
      (CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (.up ℤ)).obj X) b)⟩)

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]

/-- U⁺ is Q_B F_K, with target D⁺(B). -/
def plusUType := ∀ (F : A ⥤ B) [F.Additive],
  HomotopyCategory.Plus A ⥤ _root_.DerivedCategory.Plus B
noncomputable def plusUValue : plusUType (A := A) (B := B) :=
  fun F _ => termwisePlusValue F ⋙ _root_.DerivedCategory.Plus.Qh

/-- U⁻ is Q_B F_K, with target D⁻(B). -/
def minusUType := ∀ (F : A ⥤ B) [F.Additive],
  KMinus A ⥤ _root_.DerivedCategory.Minus B
noncomputable def minusUValue : minusUType (A := A) (B := B) :=
  fun F _ => termwiseMinusValue F ⋙ QMinus B

/-- No enough-injectives hypothesis is part of the definition. -/
def rightDerivedDataType := ∀ (F : A ⥤ B) [F.Additive],
  Type (max u v u' v' w w')
noncomputable def rightDerivedDataValue : rightDerivedDataType.{u, v, u', v', w, w'} (A := A) (B := B) :=
  fun F _ => RightData (_root_.DerivedCategory.Plus.Qh.{v, u, w} (C := A))
    (plusUValue F : HomotopyCategory.Plus A ⥤ _root_.DerivedCategory.Plus.{w'} B)

/-- No enough-projectives hypothesis is part of the definition. -/
def leftDerivedDataType := ∀ (F : A ⥤ B) [F.Additive],
  Type (max u v u' v' w w')
noncomputable def leftDerivedDataValue : leftDerivedDataType.{u, v, u', v', w, w'} (A := A) (B := B) :=
  fun F _ => LeftData (QMinus.{w} A)
    (minusUValue F : KMinus A ⥤ _root_.DerivedCategory.Minus.{w'} B)

/-- Natural transformations of the original functors act termwise, then by Q_B. -/
def plusUMapType := ∀ (F G : A ⥤ B) [F.Additive] [G.Additive],
  (F ⟶ G) → (plusUValue F ⟶ plusUValue G)
noncomputable def plusUMapValue : plusUMapType (A := A) (B := B) :=
  fun _ _ _ _ τ => whiskerRight τ.mapHomotopyCategoryPlus _

def minusUMapType := ∀ (F G : A ⥤ B) [F.Additive] [G.Additive],
  (F ⟶ G) → (minusUValue F ⟶ minusUValue G)
noncomputable def minusUMapValue : minusUMapType (A := A) (B := B) := fun F G _ _ τ =>
  whiskerRight
    ({ app := fun X => (minus B).homMk ((τ.mapHomotopyCategory (.up ℤ)).app X.obj)
       naturality := by
         intro X Y f
         ext : 1
         exact (τ.mapHomotopyCategory (.up ℤ)).naturality f.hom } :
      termwiseMinusValue F ⟶ termwiseMinusValue G) (QMinus B)
end Bounded

/-- Closed declaration types for the bounded constructions above. -/
def termwisePlusDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B],
    termwisePlusType (A := A) (B := B)

def termwiseMinusDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B],
    termwiseMinusType (A := A) (B := B)

def plusUDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B],
    plusUType (A := A) (B := B)

def minusUDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B],
    minusUType (A := A) (B := B)

def rightDerivedDataDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B],
    rightDerivedDataType.{u, v, u', v', w, w'} (A := A) (B := B)

def leftDerivedDataDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B],
    leftDerivedDataType.{u, v, u', v', w, w'} (A := A) (B := B)

def plusUMapDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B],
    plusUMapType (A := A) (B := B)

def minusUMapDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B],
    minusUMapType (A := A) (B := B)


/-- The required bijections are given by composition with the comparison. -/
def rightUniversalType : Prop :=
  ∀ (C : Type u₁) (D : Type u₂) (E : Type u₃)
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (Q : C ⥤ D) (U : C ⥤ E) (R : RightData Q U) (H : D ⥤ E),
    ∃ e : (R.functor ⟶ H) ≃ (U ⟶ Q ⋙ H),
      ∀ α, e α = R.unit ≫ whiskerLeft Q α

def leftUniversalType : Prop :=
  ∀ (C : Type u₁) (D : Type u₂) (E : Type u₃)
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (Q : C ⥤ D) (U : C ⥤ E) (R : LeftData Q U) (H : D ⥤ E),
    ∃ e : (H ⟶ R.functor) ≃ (Q ⋙ H ⟶ U),
      ∀ α, e α = whiskerLeft Q α ≫ R.counit

/-- Unique compatible isomorphism, including uniqueness as an isomorphism. -/
def rightUniqueType : Prop :=
  ∀ (C : Type u₁) (D : Type u₂) (E : Type u₃)
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (Q : C ⥤ D) (U : C ⥤ E) (R S : RightData Q U),
    ∃! e : R.functor ≅ S.functor, R.unit ≫ whiskerLeft Q e.hom = S.unit

def leftUniqueType : Prop :=
  ∀ (C : Type u₁) (D : Type u₂) (E : Type u₃)
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (Q : C ⥤ D) (U : C ⥤ E) (R S : LeftData Q U),
    ∃! e : R.functor ≅ S.functor, whiskerLeft Q e.hom ≫ S.counit = R.counit

/-- Induced maps are characterized uniquely by their comparison squares. -/
def rightMapType : Prop :=
  ∀ (C : Type u₁) (D : Type u₂) (E : Type u₃)
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (Q : C ⥤ D) (U V : C ⥤ E) (R : RightData Q U) (S : RightData Q V) (τ : U ⟶ V),
    ∃! α : R.functor ⟶ S.functor, R.unit ≫ whiskerLeft Q α = τ ≫ S.unit

def leftMapType : Prop :=
  ∀ (C : Type u₁) (D : Type u₂) (E : Type u₃)
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (Q : C ⥤ D) (U V : C ⥤ E) (R : LeftData Q U) (S : LeftData Q V) (τ : U ⟶ V),
    ∃! α : R.functor ⟶ S.functor, whiskerLeft Q α ≫ S.counit = R.counit ≫ τ

/-- Explicit specialization to natural transformations of additive F on K⁺. -/
def rightOriginalMapType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    (R : rightDerivedDataValue.{u, v, u', v', w, w'} F)
    (S : rightDerivedDataValue.{u, v, u', v', w, w'} G) (τ : F ⟶ G),
    ∃! α : R.functor ⟶ S.functor,
      R.unit ≫ whiskerLeft _root_.DerivedCategory.Plus.Qh α = plusUMapValue F G τ ≫ S.unit

/-- Explicit specialization to natural transformations of additive F on K⁻. -/
def leftOriginalMapType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    (R : leftDerivedDataValue.{u, v, u', v', w, w'} F)
    (S : leftDerivedDataValue.{u, v, u', v', w, w'} G) (τ : F ⟶ G),
    ∃! α : R.functor ⟶ S.functor,
      whiskerLeft (QMinus A) α ≫ S.counit = R.counit ≫ minusUMapValue F G τ

end Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
