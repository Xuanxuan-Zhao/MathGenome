import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensorTransport
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.Subcategory

/-! Independent specifications for the unbounded derived tensor (U07). -/

namespace Specs.DerivedFormalization.DerivedTensor

open CategoryTheory MonoidalCategory
open Cochains (compValue derivedValue homotopyValue qValue qhValue quotientValue
  quotientCompQhIsoValue)
open CochainTensor (isKFlat pure)
open CochainTensorTransport (AdequateModel representedUnit)

universe u a v w

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable (R : Type u) [CommRing R]

/-- The full subcategory of the homotopy category on K-flat complexes.
The acyclic tests use precisely the carrier level of the complex. -/
def kFlatHomotopy : ObjectProperty (homotopyValue.{a} R) := fun X => isKFlat X.as

abbrev flatObject (X : compValue.{a} R) (hX : isKFlat X) :
    (kFlatHomotopy.{u,a} R).FullSubcategory := ⟨(quotientValue R).obj X, hX⟩

abbrev flatQh : (kFlatHomotopy.{u,a} R).FullSubcategory ⥤ derivedValue.{a} R :=
  (kFlatHomotopy.{u,a} R).ι ⋙ qhValue R

abbrev flatQuasiIso : MorphismProperty (kFlatHomotopy.{u,a} R).FullSubcategory :=
  (HomotopyCategory.quasiIso (ModuleCat.{a} R) (.up ℤ)).inverseImage (kFlatHomotopy.{u,a} R).ι

variable {R} {A : Type a} [CommRing A] {e : R ≃+* A}

/-- The symmetric monoidal localization of the K-flat homotopy category in the
given ordinary model, with the derived category of the original ring as target. -/
structure Descent (M : AdequateModel e) where
  flatMonoidal :
    letI := M.homotopyMonoidal
    (kFlatHomotopy.{u,a} R).IsMonoidal
  monoidal : MonoidalCategory (derivedValue.{a} R)
  symmetric : @SymmetricCategory (derivedValue.{a} R) _ monoidal
  localization : (flatQh.{u,a} R).IsLocalization (flatQuasiIso.{u,a} R)
  braided :
    letI := M.homotopyMonoidal
    letI := M.homotopySymmetric
    letI := flatMonoidal
    letI := monoidal
    letI := symmetric
    (flatQh.{u,a} R).Braided

variable {M : AdequateModel e}

/-- The derived tensor on objects and morphisms of the original-ring localization. -/
abbrev Descent.tensorFunctor (T : Descent M) :
    derivedValue.{a} R × derivedValue.{a} R ⥤ derivedValue.{a} R :=
  letI := T.monoidal
  MonoidalCategory.tensor _

set_option linter.checkUnivs false in
def TensorFunctorType :=
  ∀ {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e}, Descent M → derivedValue.{a} R × derivedValue.{a} R ⥤ derivedValue.{a} R

/-- The unit is the image of the original ring's rank-one stalk. -/
def Descent.unitComparison (T : Descent M) :
    letI := T.monoidal
    𝟙_ (derivedValue.{a} R) ≅ (qValue R).obj (representedUnit e) :=
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  letI := M.homotopyMonoidal
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  letI := T.flatMonoidal
  letI := T.monoidal
  letI := T.symmetric
  letI := T.braided
  Functor.Monoidal.εIso (flatQh.{u,a} R) ≪≫
    (qhValue R).mapIso (Functor.Monoidal.εIso (quotientValue R)) ≪≫
    (quotientValue R ⋙ qhValue R).mapIso M.unitModel.symm ≪≫
    (quotientCompQhIsoValue R).app (representedUnit e)

/-- With two K-flat models the comparison is the composite of the two strong
monoidal comparison maps and the identification with the signed chain tensor. -/
def Descent.flatComparison (T : Descent M) (X Y : compValue.{a} R)
    (hX : isKFlat X) (hY : isKFlat Y) :
    T.tensorFunctor.obj ((qValue R).obj X, (qValue R).obj Y) ≅
      (qValue R).obj (CochainTensor.tensor X Y) :=
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  letI := M.homotopyMonoidal
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  letI := T.flatMonoidal
  letI := T.monoidal
  letI := T.symmetric
  letI := T.braided
  tensorIso ((quotientCompQhIsoValue R).app X).symm ((quotientCompQhIsoValue R).app Y).symm ≪≫
    Functor.Monoidal.μIso (flatQh.{u,a} R) (flatObject.{u,a} R X hX) (flatObject.{u,a} R Y hY) ≪≫
    (qhValue R).mapIso (Functor.Monoidal.μIso (quotientValue R) X Y) ≪≫
    (quotientValue R ⋙ qhValue R).mapIso (M.tensorModel X Y).symm ≪≫
    (quotientCompQhIsoValue R).app (CochainTensor.tensor X Y)

/-- The comparison for any K-flat presentations of derived objects. In
particular the presentations can be the images of both U02 augmentations. -/
def Descent.presentationComparison (T : Descent M)
    {X Y : derivedValue.{a} R} {P Q : compValue.{a} R}
    (hP : isKFlat P) (hQ : isKFlat Q)
    (p : (qValue R).obj P ≅ X) (q : (qValue R).obj Q ≅ Y) :
    T.tensorFunctor.obj (X, Y) ≅ (qValue R).obj (CochainTensor.tensor P Q) :=
  letI := T.monoidal
  (tensorIso p q).symm ≪≫ T.flatComparison P Q hP hQ

/-- Use the actual images of the augmentation maps for two K-flat replacements. -/
def Descent.augmentationComparison (T : Descent M)
    {X Y P Q : compValue.{a} R} (hP : isKFlat P) (hQ : isKFlat Q)
    (p : P ⟶ X) (q : Q ⟶ Y) [QuasiIso p] [QuasiIso q] :
    T.tensorFunctor.obj ((qValue R).obj X, (qValue R).obj Y) ≅
      (qValue R).obj (CochainTensor.tensor P Q) :=
  letI : IsIso ((qValue R).map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{a} R) p).2 inferInstance
  letI : IsIso ((qValue R).map q) := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{a} R) q).2 inferInstance
  T.presentationComparison hP hQ (asIso ((qValue R).map p)) (asIso ((qValue R).map q))

/-- The ordinary signed tensor computes the derived tensor on the locus where
either factor is K-flat. The comparison is natural on the full subcategory of
pairs satisfying that condition, including pairs where different factors are flat. -/
structure Model (M : AdequateModel e) extends Descent M where
  compare (X Y : compValue.{a} R) (h : isKFlat X ∨ isKFlat Y) :
    toDescent.tensorFunctor.obj ((qValue R).obj X, (qValue R).obj Y) ≅
      (qValue R).obj (CochainTensor.tensor X Y)
  compare_flat (X Y : compValue.{a} R) (hX : isKFlat X) (hY : isKFlat Y) :
    compare X Y (Or.inl hX) = toDescent.flatComparison X Y hX hY
  compare_natural {X X' Y Y' : compValue.{a} R} (f : X ⟶ X') (g : Y ⟶ Y')
      (h : isKFlat X ∨ isKFlat Y) (h' : isKFlat X' ∨ isKFlat Y') :
    toDescent.tensorFunctor.map ((qValue R).map f, (qValue R).map g) ≫
        (compare X' Y' h').hom =
      (compare X Y h).hom ≫ (qValue R).map (CochainTensor.map f g)

/-- U07 at any bound containing a representative of the ring. -/
def ExistsModel : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] {e : R ≃+* A}
    (M : AdequateModel e), Nonempty (Model M)

/-- Any representatives of the derived maps on K-flat models give the same
tensor map after conjugation by the presentation comparisons. This applies also
to changes of model and, by composing such changes, is independent of the
chosen U02 augmentations. -/
def PresentationNaturality : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e} (T : Descent M)
    {X X' Y Y' : derivedValue.{a} R} {P P' Q Q' : compValue.{a} R}
    (hP : isKFlat P) (hP' : isKFlat P') (hQ : isKFlat Q) (hQ' : isKFlat Q')
    (p : (qValue R).obj P ≅ X) (p' : (qValue R).obj P' ≅ X')
    (q : (qValue R).obj Q ≅ Y) (q' : (qValue R).obj Q' ≅ Y')
    (f : X ⟶ X') (g : Y ⟶ Y') (f₀ : P ⟶ P') (g₀ : Q ⟶ Q'),
    (qValue R).map f₀ ≫ p'.hom = p.hom ≫ f →
    (qValue R).map g₀ ≫ q'.hom = q.hom ≫ g →
    T.tensorFunctor.map (f, g) ≫ (T.presentationComparison hP' hQ' p' q').hom =
      (T.presentationComparison hP hQ p q).hom ≫ (qValue R).map (CochainTensor.map f₀ g₀)

/-- The derived braiding is the image of the chain Koszul interchange on
K-flat models. -/
def BraidingOnModels : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e} (T : Descent M)
    (X Y : compValue.{a} R) (hX : isKFlat X) (hY : isKFlat Y),
    letI := M.chainMonoidal
    letI := M.chainSymmetric
    letI := T.monoidal
    letI := T.symmetric
    let q := qValue.{a} R
    let b := M.tensorModel X Y ≪≫ β_ X Y ≪≫ (M.tensorModel Y X).symm
    ((β_ (q.obj X) (q.obj Y)).hom ≫ (T.flatComparison Y X hY hX).hom =
      (T.flatComparison X Y hX hY).hom ≫ q.map b.hom) ∧
    ∀ (i j n : ℤ) (h : i + j = n) (x : X.X i) (y : Y.X j),
      b.hom.f n (pure X Y h x y) =
        (i * j).negOnePow • pure Y X (by omega : j + i = n) y x

/-- When one original is K-flat, applying the two augmentations to the model
tensor gives the same comparison with the ordinary tensor. -/
def AugmentationCompatibility : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e} (T : Model M) {X Y P Q : compValue.{a} R}
    (h : isKFlat X ∨ isKFlat Y) (hP : isKFlat P) (hQ : isKFlat Q)
    (p : P ⟶ X) (q : Q ⟶ Y) [QuasiIso p] [QuasiIso q],
    (T.toDescent.augmentationComparison hP hQ p q).hom ≫
        (qValue R).map (CochainTensor.map p q) =
      (T.compare X Y h).hom

/-- Every derived map is represented by a chain map on K-projective source
presentations, uniquely up to chain homotopy. U02 supplies such presentations
which are also K-flat. -/
def KProjectiveMapLifting : Prop :=
  ∀ {R : Type u} [CommRing R] {X Y : derivedValue.{a} R} {P Q : compValue.{a} R}
    [P.IsKProjective] (p : (qValue R).obj P ≅ X) (q : (qValue R).obj Q ≅ Y)
    (f : X ⟶ Y),
    (∃ f₀ : P ⟶ Q, (qValue R).map f₀ ≫ q.hom = p.hom ≫ f) ∧
    ∀ f₀ f₁ : P ⟶ Q, (qValue R).map f₀ ≫ q.hom = p.hom ≫ f →
      (qValue R).map f₁ ≫ q.hom = p.hom ≫ f → Nonempty (Homotopy f₀ f₁)

/-- A presentation with the separately specified coefficient lifts of two
complexes of independently sized carriers into the same adequate category. -/
abbrev Descent.tensorOfLifts {A : Type (max u v w)} [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e} (T : Descent M) (X : compValue.{v} R) (Y : compValue.{w} R) :
    derivedValue.{max u v w} R :=
  T.tensorFunctor.obj
    (((CochainCoefficientLift.lift.{max u w, v} R) ⋙ qValue R).obj X,
      ((CochainCoefficientLift.lift.{max u v, w} R) ⋙ qValue R).obj Y)

/-- For two originals at a common coefficient level, the comparison with the
ordinary lifted tensor uses the canonical lift on pure tensors. Its composite
with the single-flat comparison is natural in both originals. -/
def CoefficientLiftComparison : Prop :=
  ∀ {R : Type u} {A : Type (max u v a)} [CommRing R] [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e} (T : Model M),
    let L := CochainCoefficientLift.lift.{max u a, v} R
    let q := qValue.{max u v a} R
    ∃ (c : ∀ X Y : compValue.{v} R,
          L.obj (CochainTensor.tensor X Y) ≅ CochainTensor.tensor (L.obj X) (L.obj Y)),
      (∀ (X Y : compValue.{v} R) (i j n : ℤ) (h : i + j = n) (x : X.X i) (y : Y.X j),
        (c X Y).hom.f n
            (CochainCoefficientLift.termEquiv.{max u a} (CochainTensor.tensor X Y) n
              (pure X Y h x y)) =
          pure (L.obj X) (L.obj Y) h (CochainCoefficientLift.termEquiv.{max u a} X i x)
            (CochainCoefficientLift.termEquiv.{max u a} Y j y)) ∧
      (∀ {X X' Y Y' : compValue.{v} R} (f : X ⟶ X') (g : Y ⟶ Y'),
        L.map (CochainTensor.map f g) ≫ (c X' Y').hom =
          (c X Y).hom ≫ CochainTensor.map (L.map f) (L.map g)) ∧
      ∀ {X X' Y Y' : compValue.{v} R} (f : X ⟶ X') (g : Y ⟶ Y')
        (h : isKFlat (L.obj X) ∨ isKFlat (L.obj Y))
        (h' : isKFlat (L.obj X') ∨ isKFlat (L.obj Y')),
        let comparison := fun (U V : compValue.{v} R)
            (hUV : isKFlat (L.obj U) ∨ isKFlat (L.obj V)) =>
          (T.compare (L.obj U) (L.obj V) hUV) ≪≫ q.mapIso (c U V).symm
        T.toDescent.tensorFunctor.map ((L ⋙ q).map f, (L ⋙ q).map g) ≫
            (comparison X' Y' h').hom =
          (comparison X Y h).hom ≫ (L ⋙ q).map (CochainTensor.map f g)

end

end Specs.DerivedFormalization.DerivedTensor
