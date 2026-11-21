import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedCategory
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
HA-D05, notes/002/advanced-homological-algebra.tex:1576–1629.
The category is abelian, complexes are unbounded, and the cochain shift is
K[m]^i = K^(i+m), with differential (-1)^m d. No splitting or boundedness
hypothesis is imposed. The derived category is the same chosen localization
as HA-D03; its standard universe choice exists for every abelian category.
The library's cycles and opcycles are respectively the kernel of the outgoing
differential and cokernel of the incoming differential, not homology objects.
-/

set_option linter.checkUnivs false
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
open Specs.AdvancedHomologicalAlgebra.DerivedCategory

namespace Specs.AdvancedHomologicalAlgebra.GoodTruncations

noncomputable abbrev LE (A : Type u) [Category.{v} A] [Abelian A] (n : ℤ) :=
  (ComplexShape.embeddingUpIntLE n).truncLEFunctor A
noncomputable abbrev GE (A : Type u) [Category.{v} A] [Abelian A] (n : ℤ) :=
  (ComplexShape.embeddingUpIntGE n).truncGEFunctor A

section DerivedRow
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

noncomputable abbrev comparison (K : CochainComplex A ℤ) (n : ℤ) :=
  K.shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl

noncomputable def boundary (K : CochainComplex A ℤ) (n : ℤ) :
    _root_.DerivedCategory.Q.obj (K.truncGE (n + 1)) ⟶
      (_root_.DerivedCategory.Q.obj (K.truncLE n))⟦(1 : ℤ)⟧ :=
  inv (_root_.DerivedCategory.Q.map (comparison K n)) ≫
    _root_.DerivedCategory.triangleOfSESδ (K.shortComplexTruncLE_shortExact n)

noncomputable def row (K : CochainComplex A ℤ) (n : ℤ) : Triangle (D A) :=
  Triangle.mk (_root_.DerivedCategory.Q.map (K.ιTruncLE n))
    (_root_.DerivedCategory.Q.map (K.πTruncGE (n + 1))) (boundary K n)
end DerivedRow

def truncLEType := ∀ (A : Type u) [Category.{v} A] [Abelian A], ℤ → (CochainComplex A ℤ ⥤ CochainComplex A ℤ)
noncomputable def truncLEValue : truncLEType := fun A _ _ n => LE A n

def truncGEType := ∀ (A : Type u) [Category.{v} A] [Abelian A], ℤ → (CochainComplex A ℤ ⥤ CochainComplex A ℤ)
noncomputable def truncGEValue : truncGEType := fun A _ _ n => GE A n

def inclusionType := ∀ (A : Type u) [Category.{v} A] [Abelian A] (n : ℤ), LE A n ⟶ 𝟭 _
noncomputable def inclusionValue : inclusionType := fun A _ _ n => (ComplexShape.embeddingUpIntLE n).ιTruncLENatTrans A

def projectionType := ∀ (A : Type u) [Category.{v} A] [Abelian A] (n : ℤ), 𝟭 _ ⟶ GE A n
noncomputable def projectionValue : projectionType := fun A _ _ n => (ComplexShape.embeddingUpIntGE n).πTruncGENatTrans A

def termsLEType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] (K : CochainComplex A ℤ) (n i : ℤ),
  (i < n → Nonempty ((K.truncLE n).X i ≅ K.X i)) ∧
  Nonempty ((K.truncLE n).X n ≅ kernel (K.d n (n + 1))) ∧
  (n < i → IsZero ((K.truncLE n).X i))

def termsGEType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] (K : CochainComplex A ℤ) (n i : ℤ),
  (i < n → IsZero ((K.truncGE n).X i)) ∧
  Nonempty ((K.truncGE n).X n ≅ cokernel (K.d (n - 1) n)) ∧
  (n < i → Nonempty ((K.truncGE n).X i ≅ K.X i))

def cohomologyLEType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] (K : CochainComplex A ℤ) (n i : ℤ),
  (i ≤ n → IsIso (HomologicalComplex.homologyMap (K.ιTruncLE n) i)) ∧
  (n < i → IsZero ((K.truncLE n).homology i))

def cohomologyGEType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] (K : CochainComplex A ℤ) (n i : ℤ),
  (n ≤ i → IsIso (HomologicalComplex.homologyMap (K.πTruncGE n) i)) ∧
  (i < n → IsZero ((K.truncGE n).homology i))

def preservesQuasiIsoLEType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] (X Y : CochainComplex A ℤ) (f : X ⟶ Y) (n : ℤ),
  QuasiIso f → QuasiIso (CochainComplex.truncLEMap f n)

def preservesQuasiIsoGEType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] (X Y : CochainComplex A ℤ) (f : X ⟶ Y) (n : ℤ),
  QuasiIso f → QuasiIso (CochainComplex.truncGEMap f n)

def preservesHomotopyLEType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] (X Y : CochainComplex A ℤ) (f g : X ⟶ Y) (n : ℤ),
  Nonempty (Homotopy f g) →
    Nonempty (Homotopy (CochainComplex.truncLEMap f n) (CochainComplex.truncLEMap g n))

def preservesHomotopyGEType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] (X Y : CochainComplex A ℤ) (f g : X ⟶ Y) (n : ℤ),
  Nonempty (Homotopy f g) →
    Nonempty (Homotopy (CochainComplex.truncGEMap f n) (CochainComplex.truncGEMap g n))

def homotopyDescentType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] (n : ℤ),
  ∃ (F G : K A ⥤ K A),
    Nonempty (LE A n ⋙ Q A ≅ Q A ⋙ F) ∧
    Nonempty (GE A n ⋙ Q A ≅ Q A ⋙ G)

def derivedDescentType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A] (n : ℤ),
  ∃ (F G : D A ⥤ D A),
    Nonempty (LE A n ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙ F) ∧
    Nonempty (GE A n ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙ G)

def shiftLEType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] (n m : ℤ),
  Nonempty (LE A n ⋙ shiftFunctor (CochainComplex A ℤ) m ≅
    shiftFunctor (CochainComplex A ℤ) m ⋙ LE A (n - m))

def shiftGEType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] (n m : ℤ),
  Nonempty (GE A n ⋙ shiftFunctor (CochainComplex A ℤ) m ≅
    shiftFunctor (CochainComplex A ℤ) m ⋙ GE A (n - m))

def comparisonQuasiIsoType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] (K : CochainComplex A ℤ) (n : ℤ),
  QuasiIso (K.shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl)

def distinguishedType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A] (K : CochainComplex A ℤ) (n : ℤ),
  row K n ∈ distTriang (D A)

def naturalDerivedTriangleType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A] (n : ℤ),
  ∃ (F : D A ⥤ Triangle (D A)) (e : ∀ K, F.obj (_root_.DerivedCategory.Q.obj K) ≅ row K n),
    (∀ X, F.obj X ∈ distTriang (D A)) ∧
    (∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y),
      (F.map (_root_.DerivedCategory.Q.map f)).hom₁ ≫ (e Y).hom.hom₁ =
        (e X).hom.hom₁ ≫ _root_.DerivedCategory.Q.map (CochainComplex.truncLEMap f n)) ∧
    (∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y),
      (F.map (_root_.DerivedCategory.Q.map f)).hom₂ ≫ (e Y).hom.hom₂ =
        (e X).hom.hom₂ ≫ _root_.DerivedCategory.Q.map f) ∧
    (∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y),
      (F.map (_root_.DerivedCategory.Q.map f)).hom₃ ≫ (e Y).hom.hom₃ =
        (e X).hom.hom₃ ≫ _root_.DerivedCategory.Q.map (CochainComplex.truncGEMap f (n + 1)))

end Specs.AdvancedHomologicalAlgebra.GoodTruncations
