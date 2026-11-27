import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.EndomorphismGenerator
import Mathlib.Algebra.Homology.Single
import Mathlib.LinearAlgebra.Matrix.ToLin

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open _root_.DerivedFormalization

universe u v z j

namespace Specs.DerivedFormalization.DG.MatrixMoritaExample

open EndomorphismGenerator
open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance)

noncomputable section

variable {k : Type u} [Field k]

/-- The cochain complex of a vector space placed in degree zero. -/
abbrev inDegreeZero (V : ModuleCat.{u} k) : ModuleCochain.{u,u} k :=
  (single (ModuleCat.{u} k) (ComplexShape.up ℤ) 0).obj V

abbrev zeroTerm (V : ModuleCat.{u} k) (i : ℤ) := (inDegreeZero V).X i

theorem subsingleton_zeroTerm (V : ModuleCat.{u} k) {i : ℤ} (h : i ≠ 0) :
    Subsingleton (zeroTerm V i) :=
  ModuleCat.isZero_iff_subsingleton.mp (isZero_single_obj_X _ _ V _ h)

/-- Evaluation in degree zero, extended by the zero map in other degrees. -/
def readZero (V : ModuleCat.{u} k) (i : ℤ) : zeroTerm V i ⟶ V :=
  if h : i = 0 then (singleObjXIsoOfEq _ 0 V i h).hom else 0

/-- Inclusion in degree zero, extended by the zero map in other degrees. -/
def writeZero (V : ModuleCat.{u} k) (i : ℤ) : V ⟶ zeroTerm V i :=
  if h : i = 0 then (singleObjXIsoOfEq _ 0 V i h).inv else 0

@[simp] theorem readZero_zero (V : ModuleCat.{u} k) :
    readZero V 0 = (singleObjXSelf _ 0 V).hom := by
  simp [readZero, singleObjXSelf]

@[simp] theorem writeZero_zero (V : ModuleCat.{u} k) :
    writeZero V 0 = (singleObjXSelf _ 0 V).inv := by
  simp [writeZero, singleObjXSelf]

@[simp] theorem read_write (V : ModuleCat.{u} k) (x : V) :
    readZero V 0 (writeZero V 0 x) = x := by simp

@[simp] theorem write_read (V : ModuleCat.{u} k) (x : zeroTerm V 0) :
    writeZero V 0 (readZero V 0 x) = x := by simp

variable (R : Type u) [Ring R] [Algebra k R]

/-- Ordinary algebra multiplication, extended to the degree-zero complex. -/
def zeroProduct (i j n : ℤ) :
    zeroTerm (ModuleCat.of k R) i →ₗ[k] zeroTerm (ModuleCat.of k R) j →ₗ[k]
      zeroTerm (ModuleCat.of k R) n where
  toFun x := (writeZero (ModuleCat.of k R) n).hom.comp
    (((LinearMap.mul k R) (readZero (ModuleCat.of k R) i x)).comp
      (readZero (ModuleCat.of k R) j).hom)
  map_add' x y := by ext a; simp
  map_smul' c x := by ext a; simp

@[simp] theorem zeroProduct_apply (i j n : ℤ) (x : zeroTerm (ModuleCat.of k R) i)
    (y : zeroTerm (ModuleCat.of k R) j) :
    zeroProduct R i j n x y =
      writeZero (ModuleCat.of k R) n
        (readZero (ModuleCat.of k R) i x * readZero (ModuleCat.of k R) j y) := rfl

@[simp] theorem zeroProduct_zero_left (i j n : ℤ) (x : zeroTerm (ModuleCat.of k R) j) :
    zeroProduct R i j n 0 x = 0 := by simp

@[simp] theorem zeroProduct_zero_right (i j n : ℤ) (x : zeroTerm (ModuleCat.of k R) i) :
    zeroProduct R i j n x 0 = 0 := by simp

/-- The one-object dg category attached to an ordinary unital algebra. -/
@[reducible] def algebraCategory : DGCategoryModel.{u,u,z} k where
  Obj := PUnit.{z+1}
  toData :=
    { hom := fun _ _ => inDegreeZero (ModuleCat.of k R)
      comp := fun i j n _ => zeroProduct R i j n
      id := fun _ => writeZero (ModuleCat.of k R) 0 1
      d_id := fun _ => rfl
      id_comp := by
        intro a b i x
        by_cases hi : i = 0
        · subst i
          simp
        · exact (subsingleton_zeroTerm _ hi).elim _ _
      comp_id := by
        intro a b i x
        by_cases hi : i = 0
        · subst i
          simp
        · exact (subsingleton_zeroTerm _ hi).elim _ _
      assoc := by
        intro a b c e i j l x y t
        by_cases hi : i = 0
        · by_cases hj : j = 0
          · by_cases hl : l = 0
            · subst i j l
              simpa using congrArg (writeZero (ModuleCat.of k R) 0)
                (mul_assoc (readZero _ 0 x) (readZero _ 0 y) (readZero _ 0 t))
            · obtain rfl : t = 0 := (subsingleton_zeroTerm _ hl).elim _ _
              simp
          · obtain rfl : y = 0 := (subsingleton_zeroTerm _ hj).elim _ _
            simp
        · obtain rfl : x = 0 := (subsingleton_zeroTerm _ hi).elim _ _
          simp
      leibniz := by
        intro a b c i j n h x y
        simp }

abbrev fieldCategory (k : Type u) [Field k] : DGCategoryModel.{u,u,u} k :=
  algebraCategory.{u,u} k

abbrev matrixCategory (k : Type u) [Field k] (m : ℕ) : DGCategoryModel.{u,u,u} k :=
  algebraCategory.{u,u} (Matrix (Fin m) (Fin m) k)

/-- Represent the same algebra at a common Hom bound over the original field. -/
abbrev liftedAlgebraCategory (R : Type u) [Ring R] [Algebra k R] :
    DGCategoryModel.{u,max u v,z} k :=
  CoefficientLift.liftCategory.{u,u,z,v} (algebraCategory.{u,z} (k := k) R)

abbrev regular (k : Type u) [Field k] : RightDGModuleModel (fieldCategory k) :=
  Yoneda.representable PUnit.unit

/-- The finite free right module, with its given standard coordinates. -/
abbrev freeModule (k : Type u) [Field k] (m : ℕ) : RightDGModuleModel (fieldCategory k) :=
  SemiFree.directSum (fun _ : ULift.{u} (Fin m) => regular k)

/-- Quasi-equivalences can point in either direction at every step. -/
inductive QuasiEquivalenceZigzag :
    DGCategoryModel.{u,v,z} k → DGCategoryModel.{u,v,z} k → Prop
  | refl (A) : QuasiEquivalenceZigzag A A
  | forward {A B C} : QuasiEquivalenceZigzag A B →
      (F : DGFunctorModel B C) → Basic.quasiEquivalence F → QuasiEquivalenceZigzag A C
  | backward {A B C} : QuasiEquivalenceZigzag A B →
      (F : DGFunctorModel C B) → Basic.quasiEquivalence F → QuasiEquivalenceZigzag A C

/-- The vector space is the ordinary finite free space at degree zero, and is
zero in all other degrees. -/
def FreeTerms : Prop :=
  ∀ (k : Type u) [Field k] (m : ℕ),
    Nonempty (((freeModule k m).complex PUnit.unit).X 0 ≃ₗ[k] (Fin m → k)) ∧
    ∀ i : ℤ, i ≠ 0 → Subsingleton (((freeModule k m).complex PUnit.unit).X i)

/-- The dg endomorphisms are exactly the ordinary matrices, with their
multiplication and identity. -/
def MatrixEndomorphisms : Prop :=
  ∀ (k : Type u) [Field k] (m : ℕ), 2 ≤ m →
    ∃ F : DGFunctorModel (endomorphismCategory.{u,u,u,u} (freeModule k m))
        (matrixCategory k m),
      Function.Bijective F.obj ∧ ∀ a b, IsIso (F.map a b)

/-- A finite free module of positive rank is a compact K-projective generator
of the actual native localization. -/
def FreeGenerator : Prop :=
  ∀ (k : Type u) [Field k] (m : ℕ), 2 ≤ m →
    KProjective.isKProjective (freeModule k m) ∧
    ∀ h : HomotopyCategoryLaws (fieldCategory k),
      letI := Derived.homotopyCategory _ h
      letI := derivedCategoryInstance _ h
      ∀ (S : Preadditive (Derived.derivedCategory _ h)),
        CompactRepresentables.LocalizationMapAdditive h S →
        CompactFiniteCells.CompactAt.{u,u,j,u} h S
          ((Derived.quotient _ h).obj (freeModule k m)) ∧
        ShiftedModuleDetectsZero (freeModule k m) h

/-- In the native G13 model the endomorphism bimodule induces an equivalence.
Restriction along the dg identification transports this tensor functor to the
derived category of the literal matrix dg category. -/
def DerivedMatrixMorita : Prop :=
  ∀ (k : Type u) [Field k] (m : ℕ), 2 ≤ m →
    let P := freeModule k m
    let A := endomorphismCategory.{u,u,u,u} P
    let B := fieldCategory k
    ∀ (s : DerivedBimoduleAdjunction.SignedModels.{u,u,u,u} (endomorphismAction P))
      (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B)
      (hM : HomotopyCategoryLaws (matrixCategory k m)),
      letI := Derived.homotopyCategory _ hA
      letI := Derived.homotopyCategory _ hB
      letI := Derived.homotopyCategory _ hM
      letI := derivedCategoryInstance _ hA
      letI := derivedCategoryInstance _ hB
      letI := derivedCategoryInstance _ hM
      ∀ (S : Preadditive (Derived.derivedCategory B hB))
        (d : DerivedBimoduleAdjunction.DerivedAdjunctionData.{u,u,u,u}
          s.tensor s.hom hA hB),
        CompactRepresentables.LocalizationMapAdditive hB S →
        d.Realizes s.adjunction → d.ComputesRepresentatives → d.IsExact →
        d.tensor.IsEquivalence ∧
          ∃ (F : DGFunctorModel A (matrixCategory k m))
            (H : HomComplex.homotopyCategory (matrixCategory k m) ⥤ HomComplex.homotopyCategory A)
            (R : Derived.derivedCategory (matrixCategory k m) hM ⥤ Derived.derivedCategory A hA),
            Function.Bijective F.obj ∧ (∀ a b, IsIso (F.map a b)) ∧
            (∀ M : RightDGModuleModel (matrixCategory k m),
              H.obj M = CoefficientLiftComparison.restrictModule F M) ∧
            (∀ {M N : RightDGModuleModel (matrixCategory k m)} (f : M ⟶ N),
              HEq (H.map (HomComplex.homotopyClass f))
                (HomComplex.homotopyClass (CoefficientLiftComparison.restrictMap F f))) ∧
            Nonempty (Derived.quotient (matrixCategory k m) hM ⋙ R ≅ H ⋙ Derived.quotient A hA) ∧
            (R ⋙ d.tensor).IsEquivalence

/-- The native localizations of the field and matrix dg categories are equivalent. -/
def DerivedCategoriesEquivalent : Prop :=
  ∀ (k : Type u) [Field k] (m : ℕ), 2 ≤ m →
    ∀ (hM : HomotopyCategoryLaws (matrixCategory k m)) (hB : HomotopyCategoryLaws (fieldCategory k)),
      letI := derivedCategoryInstance _ hM
      letI := derivedCategoryInstance _ hB
      Nonempty (Derived.derivedCategory (matrixCategory k m) hM ≌
        Derived.derivedCategory (fieldCategory k) hB)

/-- The two one-object dg categories admit no zigzag of quasi-equivalences
at the native Hom bound or after enlargement to a common Hom bound.
The enlargement and the object universe are independent of the field. -/
def NoQuasiEquivalenceZigzag : Prop :=
  ∀ (k : Type u) [Field k] (m : ℕ), 2 ≤ m →
    (¬ QuasiEquivalenceZigzag
      (algebraCategory.{u,z} (k := k) k)
      (algebraCategory.{u,z} (k := k) (Matrix (Fin m) (Fin m) k))) ∧
    (¬ QuasiEquivalenceZigzag
      (liftedAlgebraCategory.{u,v,z} (k := k) k)
      (liftedAlgebraCategory.{u,v,z} (k := k) (Matrix (Fin m) (Fin m) k)))

end

end Specs.DerivedFormalization.DG.MatrixMoritaExample
