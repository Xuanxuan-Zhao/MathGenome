import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses
import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! HA-R15, source lines 2208–2335, with the cochain convention at 107–109.
The unsigned translation retains the displayed differentials of an extension.
Its pullback against the positive projection describes literal splicing,
including the composite through the common endpoint at the junction.
No product identity is included in the definition of geometric splicing. -/
set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses

namespace Specs.AdvancedHomologicalAlgebra.YonedaProducts
variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Translation of a row retaining its unsigned differentials. -/
abbrev translate (n : ℤ) : CochainComplex 𝒜 ℤ ⥤ CochainComplex 𝒜 ℤ where
  obj K :=
    { X := fun i => K.X (i+n)
      d := fun i j => K.d (i+n) (j+n)
      shape i j h := K.shape _ _ (by change ¬ i+1=j at h; change ¬ i+n+1=j+n; omega)
      d_comp_d' i j k _ _ := K.d_comp_d _ _ _ }
  map f := { f := fun i => f.f (i+n) }

/-- The positive identification of an unsigned translated stalk. -/
noncomputable def translateSingleIso (X : 𝒜) (a n : ℤ) :
    (translate n).obj ((CochainComplex.singleFunctor 𝒜 a).obj X) ≅
      (CochainComplex.singleFunctor 𝒜 (a-n)).obj X :=
  HomologicalComplex.Hom.isoOfComponents (fun i => eqToIso (by
    dsimp [translate, CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single]
    by_cases hi : i+n=a
    · have hj : i=a-n := by omega
      simp [hj]
    · have hj : i≠a-n := by omega
      simp [hi, hj])) (by intros; simp [translate, CochainComplex.singleFunctor])

variable {X Y Z : 𝒜} {m n : ℕ}

/-- Augmentation of the translated left row to the common endpoint in degree -n. -/
noncomputable def translatedAugmentation (A : Extension Y Z m) (n : ℕ) :
    (translate (n : ℤ)).obj A.complex ⟶
      (CochainComplex.singleFunctor 𝒜 (-(n : ℤ))).obj Y :=
  (translate (n : ℤ)).map A.augmentation ≫ (translateSingleIso Y 0 (n : ℤ)).hom ≫ eqToHom (by simp)

/-- Universal characterization of the actual spliced row. At the junction
this pullback identifies the left endpoint of B with Y, so the differential
is the augmentation of A followed by the first differential of B. -/
structure SpliceData (A : Extension Y Z m) (B : Extension X Y n) where
  row : Extension X Z (n+m)
  a : row.complex ⟶ B.complex
  b : row.complex ⟶ (translate (n : ℤ)).obj A.complex
  square : IsPullback a b B.projection (translatedAugmentation A n)
  augmentation : a ≫ B.augmentation = row.augmentation
  left : b.f (-((n+m : ℕ) : ℤ)) ≫
    (A.complex.XIsoOfEq (show -((n+m : ℕ) : ℤ) + (n : ℤ) = -(m : ℤ) by omega)).hom ≫
    A.left.hom = row.left.hom

/-- Composition of shifted morphisms, including the shift-addition comparison. -/
noncomputable def product [HasDerivedCategory.{w} 𝒜]
    (α : Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext Y Z (m : ℤ))
    (β : Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (n : ℤ)) :
    Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Z ((n+m : ℕ) : ℤ) :=
  ShiftedHom.comp β α (by omega)

/-- Existence of literal splicing in every pair of positive degrees. -/
def spliceExistsType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    (X Y Z : 𝒜) (m n : ℕ) (A : Extension Y Z m) (B : Extension X Y n),
  Nonempty (SpliceData A B)

/-- The product formula concerns every actual spliced row, not a row chosen
by transporting shifted composition through the classification bijection. -/
def positiveProductType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y Z : 𝒜) (m n : ℕ)
    (A : Extension Y Z m) (B : Extension X Y n) (S : SpliceData A B),
  S.row.yonedaClass = product A.yonedaClass B.yonedaClass

/-- A degree-zero left factor acts by an actual pushout. -/
def leftZeroType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y Z : 𝒜) (n : ℕ)
    (f : Y ⟶ Z) (B : Extension X Y n),
  ∃ O : B.PushoutData f,
    O.row.yonedaClass = ShiftedHom.comp B.yonedaClass
      (Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.zeroHom f) (zero_add _)

/-- A degree-zero right factor acts by an actual pullback. -/
def rightZeroType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y Z : 𝒜) (m : ℕ)
    (A : Extension Y Z m) (f : X ⟶ Y),
  ∃ P : A.PullbackData f,
    P.row.yonedaClass = ShiftedHom.comp
      (Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.zeroHom f) A.yonedaClass (add_zero _)

/-- Two degree-zero factors compose as ordinary morphisms. -/
def zeroZeroType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y Z : 𝒜) (f : Y ⟶ Z) (g : X ⟶ Y),
  product (Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.zeroHom f)
      (Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.zeroHom g) =
    Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.zeroHom (g ≫ f)

/-- The pullback description recovers precisely the two original rows on
either side of the junction. Their cochain-map equations give the displayed
unsigned differentials and the composite through Y. -/
def spliceTermsType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    (X Y Z : 𝒜) (m n : ℕ) (A : Extension Y Z m) (B : Extension X Y n)
    (S : SpliceData A B) (i : ℤ),
  (-(n : ℤ) < i → IsIso (S.a.f i)) ∧ (i ≤ -(n : ℤ) → IsIso (S.b.f i))

/-- Geometric splicing induces an operation on the actual equivalence classes.
The three bijections have the specified normalized values on every row, and
the class operation is carried to shifted composition. -/
def classProductType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y Z : 𝒜) (m n : ℕ),
  ∃ (eA : Quotient (Extension.extensionSetoid Y Z (m+1)) ≃
      ExtShiftedHom.Ext Y Z ((m+1 : ℕ) : ℤ))
    (eB : Quotient (Extension.extensionSetoid X Y (n+1)) ≃
      ExtShiftedHom.Ext X Y ((n+1 : ℕ) : ℤ))
    (eC : Quotient (Extension.extensionSetoid X Z ((n+1)+(m+1))) ≃
      ExtShiftedHom.Ext X Z (((n+1)+(m+1) : ℕ) : ℤ))
    (splice : Quotient (Extension.extensionSetoid Y Z (m+1)) →
      Quotient (Extension.extensionSetoid X Y (n+1)) →
      Quotient (Extension.extensionSetoid X Z ((n+1)+(m+1)))),
  (∀ A : Extension Y Z (m+1), eA ⟦A⟧ = A.yonedaClass) ∧
  (∀ B : Extension X Y (n+1), eB ⟦B⟧ = B.yonedaClass) ∧
  (∀ C : Extension X Z ((n+1)+(m+1)), eC ⟦C⟧ = C.yonedaClass) ∧
  (∀ (A : Extension Y Z (m+1)) (B : Extension X Y (n+1)) (S : SpliceData A B),
    splice ⟦A⟧ ⟦B⟧ = ⟦S.row⟧) ∧
  ∀ a b, eC (splice a b) = product (eA a) (eB b)

/-- The classification portion is reused with its geometric Baer and
naturality clauses; degree zero is included separately. -/
def classificationType : Prop :=
  HigherYonedaClasses.zeroClassificationType.{w,v,u} ∧
  HigherYonedaClasses.zeroNaturalityType.{w,v,u} ∧
  HigherYonedaClasses.naturalAdditiveClassificationType.{w,v,u} ∧
  HigherYonedaClasses.degreeOneBoundaryType.{w,v,u}

end Specs.AdvancedHomologicalAlgebra.YonedaProducts
