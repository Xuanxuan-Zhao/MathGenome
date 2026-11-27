import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ScalarExtensionTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.SemifreeReplacement
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! Independent specifications for derived extension of scalars (U09). -/

namespace Specs.DerivedFormalization.DerivedScalarExtension

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Cochains (compValue derivedValue homotopyValue qValue qhValue quotientValue
  quotientCompQhIsoValue)
open CochainTensor (isKFlat)
open CochainTensorTransport (AdequateModel representedUnit)
open DerivedRestriction (restrictScalarsComplexValue derivedRestrictScalarsValue
  derivedRestrictScalarsFactorsValue)
open CochainRingTransport (complexFunctorValue derivedFunctorValue derivedFactorsValue
  derivedRestrictionIsoValue conjugateValue restrictionComp conjugateComp derivedComp
  adjunctionCompatible)
open ScalarExtensionTransport (extension extensionAdjunction diagonalExtension diagonalAdjunction
  MonoidalChange DiagonalComparison)
open DerivedTensor (Descent kFlatHomotopy flatQh flatQuasiIso flatObject)

universe u w z a v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CochainTensorMonoidal.cochainMonoidalValue

noncomputable section

variable {R : Type u} {S : Type w} {T : Type z} {A B C : Type a}
  [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B] [CommRing C]
  {e : R ≃+* A} {d : S ≃+* B} {c : T ≃+* C} {f : R →+* S} {g : S →+* T}

/-- Chain maps between K-flat representatives, with no restriction on their augmentations. -/
def flatComplexes (R : Type u) [CommRing R] : ObjectProperty (compValue.{a} R) := isKFlat

abbrev flatQ (R : Type u) [CommRing R] :
    (flatComplexes.{u,a} R).FullSubcategory ⥤ derivedValue.{a} R :=
  (flatComplexes.{u,a} R).ι ⋙ qValue R

/-- A natural computation on all K-flat representatives and their chain maps. -/
structure Lift (F : compValue.{a} R ⥤ compValue.{a} S) where
  derived : derivedValue.{a} R ⥤ derivedValue.{a} S
  factors : flatQ R ⋙ derived ≅ (flatComplexes.{u,a} R).ι ⋙ F ⋙ qValue S

def Lift.model {F : compValue.{a} R ⥤ compValue.{a} S} (L : Lift F)
    (P : compValue.{a} R) (hP : isKFlat P) :
    L.derived.obj ((qValue R).obj P) ≅ (qValue S).obj (F.obj P) :=
  L.factors.app ⟨P, hP⟩

/-- The ordinary adjunction computes the derived adjunction on K-projective
models, after the canonical factorization for restriction. -/
structure AdjointModel (f : R →+* S) (F : compValue.{a} R ⥤ compValue.{a} S)
    (adj₀ : F ⊣ restrictScalarsComplexValue.{a} f) extends Lift F where
  adj : derived ⊣ derivedRestrictScalarsValue.{a} f
  preservesFlat (P : compValue.{a} R) : isKFlat P → isKFlat (F.obj P)
  preservesProjective (P : compValue.{a} R) : P.IsKProjective → (F.obj P).IsKProjective
  projectiveFlat (P : compValue.{a} R) : P.IsKProjective → isKFlat P
  adj_on_model (P : compValue.{a} R) (Y : compValue.{a} S)
      (hP : P.IsKProjective) (k : F.obj P ⟶ Y) :
    adj.homEquiv ((qValue R).obj P) ((qValue S).obj Y)
        ((toLift.model P (projectiveFlat P hP)).hom ≫ (qValue S).map k) =
      (qValue R).map (adj₀.homEquiv P Y k) ≫ (derivedRestrictScalarsFactorsValue f).inv.app Y

abbrev Extension (d : S ≃+* B) (f : R →+* S) :=
  AdjointModel f (extension d f) (extensionAdjunction d f)

/-- The derived tensorator and unit restrict to the ordinary ones under the
two U07 comparisons. The braided structure includes strong monoidality. -/
structure MonoidalExtension {MR : AdequateModel e} {MS : AdequateModel d}
    (DR : Descent MR) (DS : Descent MS) (F : MonoidalChange e d f MR MS)
    (L : Extension d f) where
  braided :
    letI := DR.monoidal
    letI := DS.monoidal
    letI := DR.symmetric
    letI := DS.symmetric
    L.derived.Braided
  tensor_on_models (P Q : compValue.{a} R) (hP : isKFlat P) (hQ : isKFlat Q)
      (hPQ : isKFlat (CochainTensor.tensor P Q)) :
    letI := MR.chainMonoidal
    letI := MS.chainMonoidal
    letI := MR.chainSymmetric
    letI := MS.chainSymmetric
    letI := F.extensionBraided
    letI := DR.monoidal
    letI := DS.monoidal
    letI := DR.symmetric
    letI := DS.symmetric
    letI := braided
    let E := extension d f
    let ordinary := MS.tensorModel (E.obj P) (E.obj Q) ≪≫ Functor.Monoidal.μIso E P Q ≪≫
      E.mapIso (MR.tensorModel P Q).symm
    Functor.Monoidal.μIso L.derived ((qValue R).obj P) ((qValue R).obj Q) ≪≫
        L.derived.mapIso (DR.flatComparison P Q hP hQ) ≪≫
        L.toLift.model (CochainTensor.tensor P Q) hPQ =
      tensorIso (L.toLift.model P hP) (L.toLift.model Q hQ) ≪≫
        DS.flatComparison (E.obj P) (E.obj Q) (L.preservesFlat P hP) (L.preservesFlat Q hQ) ≪≫
        (qValue S).mapIso ordinary
  unit_on_model (h : isKFlat (representedUnit e)) :
    letI := MR.chainMonoidal
    letI := MS.chainMonoidal
    letI := MR.chainSymmetric
    letI := MS.chainSymmetric
    letI := F.extensionBraided
    letI := DR.monoidal
    letI := DS.monoidal
    letI := DR.symmetric
    letI := DS.symmetric
    letI := braided
    let E := extension d f
    let ordinary := MS.unitModel ≪≫ Functor.Monoidal.εIso E ≪≫ E.mapIso MR.unitModel.symm
    Functor.Monoidal.εIso L.derived ≪≫ L.derived.mapIso DR.unitComparison ≪≫
        L.toLift.model (representedUnit e) h =
      DS.unitComparison ≪≫ (qValue S).mapIso ordinary

/-- Localization of the signed native homotopy model over the representative ring. -/
structure NativeTensor (MR : AdequateModel e) where
  flatMonoidal :
    letI := MR.nativeHomotopyMonoidal
    (kFlatHomotopy.{a,a} A).IsMonoidal
  monoidal : MonoidalCategory (derivedValue.{a} A)
  symmetric : @SymmetricCategory (derivedValue.{a} A) _ monoidal
  localization : (flatQh.{a,a} A).IsLocalization (flatQuasiIso.{a,a} A)
  braided :
    letI := MR.nativeHomotopyMonoidal
    letI := MR.nativeHomotopySymmetric
    letI := flatMonoidal
    letI := monoidal
    letI := symmetric
    (flatQh.{a,a} A).Braided

variable {MR : AdequateModel e} {MS : AdequateModel d} {MT : AdequateModel c}

def NativeTensor.tensorComparison (N : NativeTensor MR) (P Q : compValue.{a} A)
    (hP : isKFlat P) (hQ : isKFlat Q) :
    letI := N.monoidal
    (qValue A).obj P ⊗ (qValue A).obj Q ≅ (qValue A).obj (CochainModels.tensorComplexValue P Q) :=
  letI := MR.nativeSymmetric
  letI := MR.nativeHomotopyMonoidal
  letI := MR.nativeHomotopySymmetric
  letI := MR.nativeQuotientBraided
  letI := N.flatMonoidal
  letI := N.monoidal
  letI := N.symmetric
  letI := N.braided
  tensorIso ((quotientCompQhIsoValue A).app P).symm ((quotientCompQhIsoValue A).app Q).symm ≪≫
    Functor.Monoidal.μIso (flatQh.{a,a} A) (flatObject.{a,a} A P hP) (flatObject.{a,a} A Q hQ) ≪≫
    (qhValue A).mapIso (Functor.Monoidal.μIso (quotientValue A) P Q) ≪≫
    (quotientCompQhIsoValue A).app (CochainModels.tensorComplexValue P Q)

def NativeTensor.unitComparison (N : NativeTensor MR) :
    letI := N.monoidal
    𝟙_ (derivedValue.{a} A) ≅ (qValue A).obj (CochainTensorMonoidal.tensorUnitValue A) :=
  letI := MR.nativeSymmetric
  letI := MR.nativeHomotopyMonoidal
  letI := MR.nativeHomotopySymmetric
  letI := MR.nativeQuotientBraided
  letI := N.flatMonoidal
  letI := N.monoidal
  letI := N.symmetric
  letI := N.braided
  Functor.Monoidal.εIso (flatQh.{a,a} A) ≪≫
    (qhValue A).mapIso (Functor.Monoidal.εIso (quotientValue A)) ≪≫
    (quotientCompQhIsoValue A).app (CochainTensorMonoidal.tensorUnitValue A)

/-- Tensor transport along the exact ring equivalence, characterized on flat chain models
using the ordinary strong monoidal transport of U01AdequateModels. -/
structure RingTensor (DR : Descent MR) extends NativeTensor MR where
  transport :
    letI := DR.monoidal
    letI := DR.symmetric
    letI := toNativeTensor.monoidal
    letI := toNativeTensor.symmetric
    (derivedFunctorValue e).Braided
  tensor_on_models (P Q : compValue.{a} R) (hP : isKFlat P) (hQ : isKFlat Q) :
    letI := MR.chainMonoidal
    letI := MR.chainSymmetric
    letI := MR.nativeSymmetric
    letI := MR.chainTransport
    letI := DR.monoidal
    letI := DR.symmetric
    letI := toNativeTensor.monoidal
    letI := toNativeTensor.symmetric
    letI := transport
    let E := derivedFunctorValue e
    let H := complexFunctorValue e
    let ordinary := Functor.Monoidal.μIso H P Q ≪≫ H.mapIso (MR.tensorModel P Q).symm
    Functor.Monoidal.μIso E ((qValue R).obj P) ((qValue R).obj Q) ≪≫
        E.mapIso (DR.flatComparison P Q hP hQ) ≪≫
        (derivedFactorsValue e).app (CochainTensor.tensor P Q) =
      tensorIso ((derivedFactorsValue e).app P) ((derivedFactorsValue e).app Q) ≪≫
        toNativeTensor.tensorComparison (H.obj P) (H.obj Q)
          ((MR.kFlat P).2 hP) ((MR.kFlat Q).2 hQ) ≪≫
        (qValue A).mapIso ordinary
  unit_on_model :
    letI := MR.chainMonoidal
    letI := MR.chainSymmetric
    letI := MR.nativeSymmetric
    letI := MR.chainTransport
    letI := DR.monoidal
    letI := DR.symmetric
    letI := toNativeTensor.monoidal
    letI := toNativeTensor.symmetric
    letI := transport
    let E := derivedFunctorValue e
    let H := complexFunctorValue e
    let ordinary := Functor.Monoidal.εIso H ≪≫ H.mapIso MR.unitModel.symm
    Functor.Monoidal.εIso E ≪≫ E.mapIso DR.unitComparison ≪≫
        (derivedFactorsValue e).app (representedUnit e) =
      toNativeTensor.unitComparison ≪≫ (qValue A).mapIso ordinary

/-- The tensor transport exists for each U07 model on the original ring. -/
def RingTensorExists : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] {e : R ≃+* A}
    {MR : AdequateModel e} (DR : Descent MR), Nonempty (RingTensor DR)

abbrev NativeExtension (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S) :=
  AdjointModel (conjugateValue e d f) (diagonalExtension e d f) (diagonalAdjunction e d f)

variable {DR : Descent MR} {DS : Descent MS} {DT : Descent MT}

/-- The change-of-rings square uses the actual derived ring equivalences,
and is both monoidal and the adjunction mate of the restriction comparison. -/
structure DiagonalExtension (NR : RingTensor DR) (NS : RingTensor DS)
    {F : MonoidalChange e d f MR MS} {L : Extension d f} (ML : MonoidalExtension DR DS F L)
    (D : DiagonalComparison e d f MR MS F) where
  native : NativeExtension e d f
  braided :
    letI := NR.toNativeTensor.monoidal
    letI := NS.toNativeTensor.monoidal
    letI := NR.toNativeTensor.symmetric
    letI := NS.toNativeTensor.symmetric
    native.derived.Braided
  comparison : L.derived ⋙ derivedFunctorValue d ≅ derivedFunctorValue e ⋙ native.derived
  adjunction :
    adjunctionCompatible L.adj native.adj comparison.inv (derivedRestrictionIsoValue e d f).hom
  monoidal :
    letI := DR.monoidal
    letI := DS.monoidal
    letI := DR.symmetric
    letI := DS.symmetric
    letI := NR.toNativeTensor.monoidal
    letI := NS.toNativeTensor.monoidal
    letI := NR.toNativeTensor.symmetric
    letI := NS.toNativeTensor.symmetric
    letI := NR.transport
    letI := NS.transport
    letI := ML.braided
    letI := braided
    NatTrans.IsMonoidal comparison.hom
  on_models (P : compValue.{a} R) (hP : isKFlat P) :
    let H := complexFunctorValue e
    let E := extension d f
    comparison.app ((qValue R).obj P) ≪≫
        native.derived.mapIso ((derivedFactorsValue e).app P) ≪≫
        native.toLift.model (H.obj P) ((MR.kFlat P).2 hP) =
      (derivedFunctorValue d).mapIso (L.toLift.model P hP) ≪≫
        (derivedFactorsValue d).app (E.obj P) ≪≫ (qValue B).mapIso (D.comparison.app P)
  native_tensor_on_models (P Q : compValue.{a} A) (hP : isKFlat P) (hQ : isKFlat Q)
      (hPQ : isKFlat (CochainModels.tensorComplexValue P Q)) :
    letI := MR.nativeSymmetric
    letI := MS.nativeSymmetric
    letI := D.nativeBraided
    letI := NR.toNativeTensor.monoidal
    letI := NS.toNativeTensor.monoidal
    letI := NR.toNativeTensor.symmetric
    letI := NS.toNativeTensor.symmetric
    letI := braided
    let E := diagonalExtension e d f
    Functor.Monoidal.μIso native.derived ((qValue A).obj P) ((qValue A).obj Q) ≪≫
        native.derived.mapIso (NR.toNativeTensor.tensorComparison P Q hP hQ) ≪≫
        native.toLift.model (CochainModels.tensorComplexValue P Q) hPQ =
      tensorIso (native.toLift.model P hP) (native.toLift.model Q hQ) ≪≫
        NS.toNativeTensor.tensorComparison (E.obj P) (E.obj Q)
          (native.preservesFlat P hP) (native.preservesFlat Q hQ) ≪≫
        (qValue B).mapIso (Functor.Monoidal.μIso E P Q)
  native_unit_on_model (h : isKFlat (CochainTensorMonoidal.tensorUnitValue A)) :
    letI := MR.nativeSymmetric
    letI := MS.nativeSymmetric
    letI := D.nativeBraided
    letI := NR.toNativeTensor.monoidal
    letI := NS.toNativeTensor.monoidal
    letI := NR.toNativeTensor.symmetric
    letI := NS.toNativeTensor.symmetric
    letI := braided
    Functor.Monoidal.εIso native.derived ≪≫
        native.derived.mapIso NR.toNativeTensor.unitComparison ≪≫
        native.toLift.model (CochainTensorMonoidal.tensorUnitValue A) h =
      NS.toNativeTensor.unitComparison ≪≫
        (qValue B).mapIso (Functor.Monoidal.εIso (diagonalExtension e d f))

/-- Derived extension for every ring map in the given adequate categories,
with both ordinary and native diagonal comparisons. -/
def ExistsExtension : Prop :=
  ∀ {R : Type u} {S : Type w} {A B : Type a}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    {e : R ≃+* A} {d : S ≃+* B} (f : R →+* S)
    {MR : AdequateModel e} {MS : AdequateModel d}
    {DR : Descent MR} {DS : Descent MS} (NR : RingTensor DR) (NS : RingTensor DS),
    ∃ (F : MonoidalChange e d f MR MS) (D : DiagonalComparison e d f MR MS F)
      (L : Extension d f) (ML : MonoidalExtension DR DS F L),
      Nonempty (DiagonalExtension NR NS ML D)

/-- The composite isomorphism is the mate of transitivity of the actual
restriction functors. The same construction works on the diagonal rings. -/
def extensionComp
    {F : compValue.{a} R ⥤ compValue.{a} S} {G : compValue.{a} S ⥤ compValue.{a} T}
    {H : compValue.{a} R ⥤ compValue.{a} T} {h : R →+* T}
    {adjF : F ⊣ restrictScalarsComplexValue.{a} f} {adjG : G ⊣ restrictScalarsComplexValue.{a} g}
    {adjH : H ⊣ restrictScalarsComplexValue.{a} h}
    (LF : AdjointModel f F adjF) (LG : AdjointModel g G adjG) (LH : AdjointModel h H adjH)
    (r : ModuleCat.restrictScalars.{a} g ⋙ ModuleCat.restrictScalars.{a} f ≅
        ModuleCat.restrictScalars.{a} h) :
    LF.derived ⋙ LG.derived ≅ LH.derived :=
  ((LF.adj.comp LG.adj).ofNatIsoRight (derivedComp r)).leftAdjointUniq LH.adj

/-- Transitivity is monoidal, is ordinary transitivity on the same K-flat
models, and is compatible with the native diagonal square. -/
def Composition : Prop :=
  ∀ {R : Type u} {S : Type w} {T : Type z} {A B C : Type a}
    [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B] [CommRing C]
    {e : R ≃+* A} {d : S ≃+* B} {c : T ≃+* C} {f : R →+* S} {g : S →+* T}
    {MR : AdequateModel e} {MS : AdequateModel d} {MT : AdequateModel c}
    {DR : Descent MR} {DS : Descent MS} {DT : Descent MT}
    {NR : RingTensor DR} {NS : RingTensor DS} {NT : RingTensor DT}
    {F : MonoidalChange e d f MR MS} {G : MonoidalChange d c g MS MT}
    {H : MonoidalChange e c (g.comp f) MR MT}
    {DF : DiagonalComparison e d f MR MS F} {DG : DiagonalComparison d c g MS MT G}
    {DH : DiagonalComparison e c (g.comp f) MR MT H}
    {LF : Extension d f} {LG : Extension c g} {LH : Extension c (g.comp f)}
    {MF : MonoidalExtension DR DS F LF} {MG : MonoidalExtension DS DT G LG}
    {MH : MonoidalExtension DR DT H LH}
    (NF : DiagonalExtension NR NS MF DF) (NG : DiagonalExtension NS NT MG DG)
    (NH : DiagonalExtension NR NT MH DH),
    let iso := extensionComp LF LG LH (restrictionComp f g)
    let nativeIso := extensionComp NF.native NG.native NH.native (conjugateComp e d c f g)
    (∀ (P : compValue.{a} R) (hP : isKFlat P),
      iso.app ((qValue R).obj P) ≪≫ LH.toLift.model P hP =
        LG.derived.mapIso (LF.toLift.model P hP) ≪≫
          LG.toLift.model ((extension d f).obj P) (LF.preservesFlat P hP) ≪≫
          (qValue T).mapIso ((ScalarExtensionTransport.compositionIso d f c g).app P)) ∧
    (letI := DR.monoidal
     letI := DS.monoidal
     letI := DT.monoidal
     letI := DR.symmetric
     letI := DS.symmetric
     letI := DT.symmetric
     letI := MF.braided
     letI := MG.braided
     letI := MH.braided
     NatTrans.IsMonoidal iso.hom) ∧
    ∀ X : derivedValue.{a} R,
      (derivedFunctorValue c).mapIso (iso.app X) ≪≫ NH.comparison.app X =
        NG.comparison.app (LF.derived.obj X) ≪≫
          NG.native.derived.mapIso (NF.comparison.app X) ≪≫
          nativeIso.app ((derivedFunctorValue e).obj X)

/-- The calculation on a strict K-projective augmentation of the coefficient lift
of an original complex, viewed in the localized coefficient lift. -/
def originalModel {B' : Type (max u w v a)} [CommRing B']
    {d' : S ≃+* B'} {f' : R →+* S}
    (L : Extension d' f') {X : compValue.{v} R}
    {P : compValue.{max u w v a} R}
    (p : P ⟶ (CochainCoefficientLift.lift.{max u w a, v} R).obj X)
    (hP : P.IsKProjective) [QuasiIso p] :
    L.derived.obj ((CochainCoefficientLift.liftD.{max u w a, v} R).obj ((qValue R).obj X)) ≅
      (qValue S).obj ((extension d' f').obj P) :=
  letI : IsIso ((qValue R).map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u w v a} R) p).2 inferInstance
  L.derived.mapIso
    ((CochainCoefficientLift.liftDFactors.{max u w a, v} R).app X ≪≫
      (asIso ((qValue R).map p)).symm) ≪≫ L.toLift.model P (L.projectiveFlat P hP)

/-- Existence of the U02 computations for original inputs and naturality with
respect to maps of their augmented chain models. -/
def OriginalPresentations : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    {B : Type (max u w v a)} [CommRing B] (d : S ≃+* B) (f : R →+* S)
    (L : Extension d f),
    let j := CochainCoefficientLift.lift.{max u w a, v} R
    let J := CochainCoefficientLift.liftD.{max u w a, v} R
    let E := extension d f
    (∀ X : compValue.{v} R,
      ∃ (P : compValue.{max u w v a} R) (p : P ⟶ j.obj X)
        (_ : QuasiIso p) (_ : P.IsKProjective),
        (∀ i, Function.Surjective (p.f i)) ∧
        Nonempty (SemifreeFiltrationTransport.Filtration
          (CochainRingTransport.uliftRingEquivValue.{max u w v a} R) P) ∧
        Nonempty (L.derived.obj (J.obj ((qValue R).obj X)) ≅ (qValue S).obj (E.obj P))) ∧
    ∀ {X Y : compValue.{v} R} {P Q : compValue.{max u w v a} R}
      (p : P ⟶ j.obj X) (q : Q ⟶ j.obj Y) [QuasiIso p] [QuasiIso q]
      (hP : P.IsKProjective) (hQ : Q.IsKProjective)
      (k : X ⟶ Y) (l : P ⟶ Q), l ≫ q = p ≫ j.map k →
      L.derived.map ((qValue R ⋙ J).map k) ≫ (originalModel.{u,w,a,v} L q hQ).hom =
        (originalModel.{u,w,a,v} L p hP).hom ≫ (qValue S).map (E.map l)

end

end Specs.DerivedFormalization.DerivedScalarExtension
