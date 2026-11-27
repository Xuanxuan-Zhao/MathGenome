import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.Generators
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.SmallObject.Construction
import Mathlib.LinearAlgebra.Finsupp.Defs

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomologicalComplex HomotopicalAlgebra

universe u

namespace DerivedFormalization.Specs.ComplexCellFactorization

open Model.Complexes ComplexGenerators

/-- A sequential composite of pushouts of small coproducts of sphere inclusions. -/
noncomputable def iCellValue : generatorClassType.{u} := fun A _ ↦
  ((coproducts.{u} (iValue A)).pushouts).transfiniteCompositionsOfShape ℕ

/-- A sequential composite of pushouts of small coproducts of zero-to-disk maps. -/
noncomputable def jCellValue : generatorClassType.{u} := fun A _ ↦
  ((coproducts.{u} (jValue A)).pushouts).transfiniteCompositionsOfShape ℕ

/-- The lower generator of a disk, represented by the unit of the regular module. -/
noncomputable def diskGenerator (A : Type u) [Ring A] (n : ℤ) : (diskValue A n).X n :=
  (doubleXIso₀ (𝟙 (ModuleCat.of A A)) (ComplexShape.up_mk n (n + 1) rfl)).inv (1 : A)

/-- The generator of a sphere, represented by the unit of the regular module. -/
noncomputable def sphereGenerator (A : Type u) [Ring A] (n : ℤ) :
    (sphereValue A n).X n :=
  (singleObjXSelf (ComplexShape.up ℤ) n (ModuleCat.of A A)).inv (1 : A)

/-- In each degree the attachment adds one free generator for each cell with lower degree
equal to that degree. Its differential is the image of the attaching sphere generator. -/
def iAttachmentType : Prop :=
  ∀ (A : Type u) [Ring A] {X Y : Cochains A} (f : X ⟶ Y)
    (a : AttachCells.{u} (iGeneratorValue A) f),
    ∃ e : ∀ n : ℤ, (X.X n × ({i : a.ι // a.π i = n} →₀ A)) ≃ₗ[A] Y.X n,
      (∀ n (x : X.X n), e n (x, 0) = f.f n x) ∧
      ∀ i : a.ι,
        let n := a.π i
        let x := e n (0, Finsupp.single ⟨i, rfl⟩ 1)
        x = (a.cell i).f n (diskGenerator A n) ∧
          Y.d n (n + 1) x =
            f.f (n + 1) ((a.cofan₁.inj i ≫ a.g₁).f (n + 1) (sphereGenerator A (n + 1)))

/-- The pushout along zero is the coproduct of the old complex and the direct sum of
disks exhibited by the attachment. The direct sum is contractible. -/
def jAttachmentType : Prop :=
  ∀ (A : Type u) [Ring A] {X Y : Cochains A} (f : X ⟶ Y)
    (a : AttachCells.{u} (jGeneratorValue A) f),
    (∃ e : X ⨿ a.cofan₂.pt ≅ Y,
      coprod.inl ≫ e.hom = f ∧ coprod.inr ≫ e.hom = a.g₂) ∧
    Nonempty (Homotopy (𝟙 a.cofan₂.pt) 0)

/-- A sequential composite of disk attachments adjoins a direct sum of disks. -/
def jCellDecompositionType : Prop :=
  ∀ (A : Type u) [Ring A] {X Y : Cochains A} (f : X ⟶ Y), jCellValue A f →
    ∃ (K : Type u) (degree : K → ℤ),
      let D := ∐ (fun k : K ↦ diskValue A (degree k))
      (∃ e : X ⨿ D ≅ Y, coprod.inl ≫ e.hom = f) ∧ Nonempty (Homotopy (𝟙 D) 0)

/-- The left factor is the map into the sequential colimit. At each step the square
indexed pushout is taken against the stage's projection to the original target. -/
def IsSequentialCellFactorization {A : Type u} [Ring A] {S T : ℤ → Cochains A}
    (g : ∀ n, S n ⟶ T n) {X Z Y : Cochains A} (l : X ⟶ Z) (p : Z ⟶ Y) : Prop :=
  ∃ c : CategoryTheory.TransfiniteCompositionOfShape ℕ l,
    ∀ n : ℕ,
      let q := c.incl.app n ≫ p
      ∃ e : SmallObject.functorObj g q ≅ c.F.obj (n + 1),
        SmallObject.ιFunctorObj g q ≫ e.hom = c.F.map (homOfLE (n.le_add_right 1)) ∧
          e.hom ≫ c.incl.app (n + 1) ≫ p = SmallObject.πFunctorObj g q

def iFactorizationType : Prop :=
  ∀ (A : Type u) [Ring A],
    ∃ F : FunctorialFactorizationData (iCellValue A) (iValue A).rlp,
      ∀ f : Arrow (Cochains A),
        IsSequentialCellFactorization (iGeneratorValue A) (F.i.app f) (F.p.app f)

def jFactorizationType : Prop :=
  ∀ (A : Type u) [Ring A],
    ∃ F : FunctorialFactorizationData (jCellValue A) (jValue A).rlp,
      ∀ f : Arrow (Cochains A),
        IsSequentialCellFactorization (jGeneratorValue A) (F.i.app f) (F.p.app f)

end DerivedFormalization.Specs.ComplexCellFactorization
