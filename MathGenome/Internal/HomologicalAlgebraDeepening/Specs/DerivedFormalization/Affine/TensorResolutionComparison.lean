import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.DerivedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SemifreeAlgebras
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Specs.DerivedFormalization.Affine.TensorResolutionComparison

open _root_.DerivedFormalization.Affine
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor dgCat regular restrict)
open Specs.DerivedFormalization.Affine.DerivedTensor (TensorResolution)
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws homotopyCategory quotient)
open Specs.DerivedFormalization.DG.DerivedKProjective (derivedCategoryInstance)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B C B' C' : NonpositiveCDGA.{u,v} k}

/-- The choices allowed in a semifree surjective resolution of a specified A-algebra. -/
structure Resolution (f : A ⟶ B) where
  obj : NonpositiveCDGA.{u,v} k
  base : A ⟶ obj
  augmentation : obj ⟶ B
  commutes : base ≫ augmentation = f
  semifree : Semifree.IsSemifree A base
  surjective : NonpositiveCDGA.DegreewiseSurjective augmentation
  quasiIso : NonpositiveCDGA.IsQuasiIso augmentation

private abbrev commMap (f : A ⟶ B) : A.toCommDGAlgebra ⟶ B.toCommDGAlgebra := f

/-- The module of an A-algebra, with the right action through its structure map. -/
abbrev underlying (f : A ⟶ B) : A.Module :=
  restrict (commMap f) (regular B.toCommDGAlgebra)

/-- A common signed tensor for all the nonpositive algebras over the field. -/
structure CoproductModel (T : ModuleTensor.{u,v} k) where
  algebra {A B C : NonpositiveCDGA.{u,v} k} (f : A ⟶ B) (g : A ⟶ C) :
    T.AlgebraCoproduct (commMap f) (commMap g)
  formulas {A B C : NonpositiveCDGA.{u,v} k} (f : A ⟶ B) (g : A ⟶ C) :
    (algebra f g).Formulas

variable {T : ModuleTensor.{u,v} k} (S : CoproductModel T)

namespace CoproductModel

def tensor (f : A ⟶ B) (g : A ⟶ C) : NonpositiveCDGA.{u,v} k :=
  ⟨(S.algebra f g).obj, (S.formulas f g).nonpositive B.nonpositive C.nonpositive⟩

abbrev inl (f : A ⟶ B) (g : A ⟶ C) : B ⟶ S.tensor f g := (S.algebra f g).inl

abbrev inr (f : A ⟶ B) (g : A ⟶ C) : C ⟶ S.tensor f g := (S.algebra f g).inr

abbrev base (f : A ⟶ B) (g : A ⟶ C) : A ⟶ S.tensor f g := g ≫ S.inr f g

def cofan (f : A ⟶ B) (g : A ⟶ C) : BinaryCofan (Under.mk f) (Under.mk g) :=
  BinaryCofan.mk (P := Under.mk (S.base f g))
    (Under.homMk (S.inl f g) (S.formulas f g).base)
    (Under.homMk (S.inr f g) rfl)

/-- The tensor map in the category of cdgas, with its two inclusion equations
and action on homogeneous tensors. -/
structure Induced {f : A ⟶ B} {g : A ⟶ C} {f' : A ⟶ B'} {g' : A ⟶ C'}
    (b : B ⟶ B') (c : C ⟶ C') (t : S.tensor f g ⟶ S.tensor f' g') : Prop where
  inl : S.inl f g ≫ t = b ≫ S.inl f' g'
  inr : S.inr f g ≫ t = c ≫ S.inr f' g'
  tmul (i j n : ℤ) (h : i + j = n) (x : B.complex.X i) (y : C.complex.X j) :
    t.chainMap.f n ((S.algebra f g).tmul i j n h x y) =
      (S.algebra f' g').tmul i j n h (b.chainMap.f i x) (c.chainMap.f j y)

end CoproductModel

/-- Either augmentation gives the indicated strict quasi-isomorphism from
the tensor of two resolutions to the model resolving only the other factor. -/
def AugmentationComparisons : Prop :=
  ∀ {A B C : NonpositiveCDGA.{u,v} k} {f : A ⟶ B} {g : A ⟶ C}
    (P : Resolution f) (Q : Resolution g),
    (∃ t : S.tensor P.base Q.base ⟶ S.tensor P.base g,
      S.Induced (𝟙 P.obj) Q.augmentation t ∧ NonpositiveCDGA.IsQuasiIso t) ∧
    (∃ t : S.tensor P.base Q.base ⟶ S.tensor f Q.base,
      S.Induced P.augmentation (𝟙 Q.obj) t ∧ NonpositiveCDGA.IsQuasiIso t)

/-- A comparison of the resolved factor lifts through the target augmentation.
The lift induces a quasi-isomorphism on tensoring with a fixed K-flat factor
in either position. Taking the identity comparison of the targets compares any
two resolutions over the same algebra. -/
def ResolutionComparisons : Prop :=
  ∀ {A B B' : NonpositiveCDGA.{u,v} k}
    {f : A ⟶ B} {f' : A ⟶ B'} (b : B ⟶ B'),
    f ≫ b = f' → NonpositiveCDGA.IsQuasiIso b →
    ∀ (P : Resolution f) (P' : Resolution f'),
      ∃ p : P.obj ⟶ P'.obj,
        P.base ≫ p = P'.base ∧ p ≫ P'.augmentation = P.augmentation ≫ b ∧
        NonpositiveCDGA.IsQuasiIso p ∧
        ∀ {C : NonpositiveCDGA.{u,v} k} (g : A ⟶ C), T.KFlat (underlying g) →
          (∃ t : S.tensor P.base g ⟶ S.tensor P'.base g,
            S.Induced p (𝟙 C) t ∧ NonpositiveCDGA.IsQuasiIso t) ∧
          (∃ t : S.tensor g P.base ⟶ S.tensor g P'.base,
            S.Induced (𝟙 C) p t ∧ NonpositiveCDGA.IsQuasiIso t)

/-- A three-arrow zigzag (L \leftarrow X \to Y \to R) of strict cdga
quasi-isomorphisms. -/
def ComparisonZigzag (L X Y R : NonpositiveCDGA.{u,v} k) : Prop :=
  ∃ (a : X ⟶ L) (b : X ⟶ Y) (c : Y ⟶ R),
    NonpositiveCDGA.IsQuasiIso a ∧ NonpositiveCDGA.IsQuasiIso b ∧
      NonpositiveCDGA.IsQuasiIso c

/-- Changing the chosen resolution in either one-sided model gives a zigzag
through the double resolutions, with the other resolution fixed. -/
def ModelZigzags : Prop :=
  ∀ {A B C : NonpositiveCDGA.{u,v} k} (f : A ⟶ B) (g : A ⟶ C),
    (∀ (P P' : Resolution f) (Q : Resolution g),
      ComparisonZigzag (S.tensor P.base g) (S.tensor P.base Q.base)
        (S.tensor P'.base Q.base) (S.tensor P'.base g)) ∧
    (∀ (P : Resolution f) (Q Q' : Resolution g),
      ComparisonZigzag (S.tensor f Q.base) (S.tensor P.base Q.base)
        (S.tensor P.base Q'.base) (S.tensor f Q'.base))

/-- The algebra tensors with both resolutions or either single resolution
represent the derived tensor of the original inputs in the native derived
category of dg A-modules. -/
def ModuleComputations (h : HomotopyCategoryLaws (dgCat A.toCommDGAlgebra))
    (R : TensorResolution T A.toCommDGAlgebra h) : Prop :=
  letI := homotopyCategory (dgCat A.toCommDGAlgebra) h
  letI := derivedCategoryInstance (dgCat A.toCommDGAlgebra) h
  let L := quotient (dgCat A.toCommDGAlgebra) h
  ∀ {B C : NonpositiveCDGA.{u,v} k} (f : A ⟶ B) (g : A ⟶ C),
    let M := R.functor.obj (L.obj (underlying f), L.obj (underlying g))
    (∀ (P : Resolution f) (Q : Resolution g),
      Nonempty (M ≅ L.obj (underlying (S.base P.base Q.base)))) ∧
    (∀ P : Resolution f, Nonempty (M ≅ L.obj (underlying (S.base P.base g)))) ∧
    (∀ Q : Resolution g, Nonempty (M ≅ L.obj (underlying (S.base f Q.base))))

/-- The opposite-variance diagram supplied by a left-resolved tensor model.
The projection to the original left factor pulls back along the localization
isomorphism of the augmentation to the strict projection to the resolution. -/
def AffineDiagrams : Prop :=
  ∀ {A B C : NonpositiveCDGA.{u,v} k} {f : A ⟶ B} {g : A ⟶ C}
    (P : Resolution f),
    let X := derivedSpec k
    ∃ l : X.obj (Opposite.op (S.tensor P.base g)) ⟶ X.obj (Opposite.op B),
      l ≫ X.map P.augmentation.op = X.map (S.inl P.base g).op ∧
      l ≫ X.map f.op = X.map (S.inr P.base g).op ≫ X.map g.op

/-- The derived coproduct model is the signed strict coproduct on two semifree
resolutions. Either augmentation reduces it to a one-sided model. All comparison
maps act on the same algebra and module tensor models. -/
def TensorModels : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k],
    ∃ (T : ModuleTensor.{u,v} k) (S : CoproductModel T),
      (∀ {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B), Nonempty (Resolution f)) ∧
      (∀ {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B),
        Semifree.IsSemifree A f → T.KFlat (underlying f)) ∧
      (∀ {A B C : NonpositiveCDGA.{u,v} k} (f : A ⟶ B) (g : A ⟶ C),
        Nonempty (IsColimit (S.cofan f g))) ∧
      AugmentationComparisons S ∧ ResolutionComparisons S ∧
      (∀ (A : NonpositiveCDGA.{u,v} k)
        (h : HomotopyCategoryLaws (dgCat A.toCommDGAlgebra)),
        ∃ R : TensorResolution T A.toCommDGAlgebra h, ModuleComputations S h R) ∧
      AffineDiagrams S ∧ ModelZigzags S

end

end Specs.DerivedFormalization.Affine.TensorResolutionComparison
