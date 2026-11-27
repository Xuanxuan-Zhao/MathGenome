import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedHomModels
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! The closed derived adjunction and the cohomology of derived Hom (U08). -/

namespace Specs.DerivedFormalization.DerivedHomAdjunction

open CategoryTheory Opposite
open Cochains (compValue derivedValue qValue quotientValue quotientCompQhIsoValue
  derivedCohomologyValue cohomologyFactorsValue qShiftIsoValue)
open CochainTensor (isKFlat tensor)
open CochainModels (internalHomValue internalHomCohomologyValue)
open CochainTensorTransport (AdequateModel)
open DerivedHomModels (Models Representative rHomValue modelMap)

universe u a v w t s

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable {R : Type u} [CommRing R]

/-- A cochain complex presenting a derived object, with its chosen identification. -/
structure Presentation (X : (derivedValue.{a} R)) where
  complex : (compValue.{a} R)
  iso : (qValue.{a} R).obj complex ≅ X

def Presentation.representative {X : (derivedValue.{a} R)} (P : Presentation X) : Representative X :=
  ⟨(quotientValue R).obj P.complex, (quotientCompQhIsoValue R).app P.complex ≪≫ P.iso⟩

def Presentation.Over {X Y : (derivedValue.{a} R)} (P : Presentation X) (S : Presentation Y)
    (f : X ⟶ Y) (g : P.complex ⟶ S.complex) : Prop :=
  (qValue.{a} R).map g ≫ S.iso.hom = P.iso.hom ≫ f

variable {A : Type a} [CommRing A] {e : R ≃+* A} {M : AdequateModel e}

/-- The single K-flat tensor computation transported to the presented objects. -/
def tensorComparison (T : DerivedTensor.Model M) {Z X : (derivedValue.{a} R)}
    (S : Presentation Z) (P : Presentation X) (hP : isKFlat P.complex) :
    T.toDescent.tensorFunctor.obj (Z, X) ≅ (qValue.{a} R).obj (tensor S.complex P.complex) :=
  (T.toDescent.tensorFunctor.mapIso (S.iso.prod P.iso)).symm ≪≫
    T.compare S.complex P.complex (Or.inr hP)

/-- The canonical map from the signed Hom of representatives to derived Hom. -/
def homComparison (H : Models.{u,a} R) {X Y : (derivedValue.{a} R)}
    (P : Presentation X) (I : Presentation Y) :
    (qValue.{a} R).obj (internalHomValue P.complex I.complex) ⟶ (rHomValue H).obj (op X, Y) :=
  eqToHom (H.hom.obj_eq P.representative.obj I.representative.obj).symm ≫
    modelMap H P.representative I.representative

/-- The specified identification of a shifted representative, with the cochain shift sign. -/
def shiftedPresentation {Y : (derivedValue.{a} R)} (I : Presentation Y) (n : ℤ) :
    (qValue.{a} R).obj (I.complex⟦n⟧) ≅ Y⟦n⟧ :=
  (qShiftIsoValue R n).app I.complex ≪≫ (shiftFunctor (derivedValue.{a} R) n).mapIso I.iso

def HomOfFlatInjective : Prop :=
  ∀ {R : Type u} [CommRing R] (P I : (compValue.{a} R)),
    isKFlat P → I.IsKInjective → (internalHomValue P I).IsKInjective

/-- The closed adjunction, natural in all three arguments and induced by the
ordinary signed currying on each pair of a flat and an injective representative. -/
structure Closed (T : DerivedTensor.Model M) (H : Models.{u,a} R) where
  equiv (Z X Y : (derivedValue.{a} R)) :
    (T.toDescent.tensorFunctor.obj (Z, X) ⟶ Y) ≃ₗ[R]
      (Z ⟶ (rHomValue H).obj (op X, Y))
  natural {Z Z' X X' Y Y' : (derivedValue.{a} R)} (z : Z' ⟶ Z) (x : X' ⟶ X) (y : Y ⟶ Y')
      (f : T.toDescent.tensorFunctor.obj (Z, X) ⟶ Y) :
    equiv Z' X' Y' (T.toDescent.tensorFunctor.map (Prod.mkHom z x) ≫ f ≫ y) =
      z ≫ equiv Z X Y f ≫ (rHomValue H).map (Prod.mkHom x.op y)
  on_models {Z X Y : (derivedValue.{a} R)} (S : Presentation Z) (P : Presentation X) (I : Presentation Y)
      (hP : isKFlat P.complex) (hI : I.complex.IsKInjective)
      (f : tensor S.complex P.complex ⟶ I.complex) :
    equiv Z X Y ((tensorComparison T S P hP).hom ≫ (qValue.{a} R).map f ≫ I.iso.hom) =
      S.iso.inv ≫ (qValue.{a} R).map ((M.rawClosed P.complex).adj.homEquiv _ _ f) ≫ homComparison H P I

/-- The derived tensor functor with fixed right factor. -/
abbrev tensorRight (T : DerivedTensor.Model M) (X : derivedValue.{a} R) :
    derivedValue.{a} R ⥤ derivedValue.{a} R :=
  (Functor.curryObj T.toDescent.tensorFunctor).flip.obj X

/-- The derived Hom functor with fixed source. -/
abbrev homFrom (H : Models.{u,a} R) (X : derivedValue.{a} R) :
    derivedValue.{a} R ⥤ derivedValue.{a} R :=
  (Functor.curryObj (rHomValue H)).obj (op X)

/-- The three-variable correspondence gives an adjunction for each fixed X. -/
def Closed.adjunctionCore {T : DerivedTensor.Model M} {H : Models.{u,a} R}
    (c : Closed T H) (X : derivedValue.{a} R) :
    Adjunction.CoreHomEquiv (tensorRight T X) (homFrom H X) where
  homEquiv Z Y := (c.equiv Z X Y).toEquiv
  homEquiv_naturality_left_symm := by
    intro Z' Z Y f g
    apply (c.equiv Z' X Y).injective
    have h := c.natural f (𝟙 X) (𝟙 Y) ((c.equiv Z X Y).symm g)
    change c.equiv Z' X Y ((tensorRight T X).map f ≫ (c.equiv Z X Y).symm g ≫ 𝟙 Y) =
      f ≫ c.equiv Z X Y ((c.equiv Z X Y).symm g) ≫ (rHomValue H).map (𝟙 _) at h
    rw [(rHomValue H).map_id, Category.comp_id, LinearEquiv.apply_symm_apply, Category.comp_id] at h
    change c.equiv Z' X Y ((c.equiv Z' X Y).symm (f ≫ g)) =
      c.equiv Z' X Y ((tensorRight T X).map f ≫ (c.equiv Z X Y).symm g)
    rw [LinearEquiv.apply_symm_apply, h]
  homEquiv_naturality_right := by
    intro Z Y Y' f g
    have h := c.natural (𝟙 Z) (𝟙 X) g f
    change c.equiv Z X Y' (T.toDescent.tensorFunctor.map (𝟙 _) ≫ f ≫ g) =
      𝟙 Z ≫ c.equiv Z X Y f ≫ (homFrom H X).map g at h
    rw [T.toDescent.tensorFunctor.map_id, Category.id_comp, Category.id_comp] at h
    exact h

def Closed.adjunction {T : DerivedTensor.Model M} {H : Models.{u,a} R}
    (c : Closed T H) (X : derivedValue.{a} R) : tensorRight T X ⊣ homFrom H X :=
  Adjunction.mkOfHomEquiv (c.adjunctionCore X)

@[simp]
theorem Closed.adjunction_homEquiv {T : DerivedTensor.Model M} {H : Models.{u,a} R}
    (c : Closed T H) (Z X Y : derivedValue.{a} R) :
    (c.adjunction X).homEquiv Z Y = (c.equiv Z X Y).toEquiv := by
  rw [Closed.adjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- Cohomology is identified linearly with maps to the shift, with the
identification induced by the cocycle-to-homotopy-class correspondence. -/
structure Cohomology (H : Models.{u,a} R) where
  equiv (X Y : (derivedValue.{a} R)) (n : ℤ) :
    ((derivedCohomologyValue R n).obj ((rHomValue H).obj (op X, Y))) ≃ₗ[R]
      (X ⟶ Y⟦n⟧)
  natural {X X' Y Y' : (derivedValue.{a} R)} (x : X' ⟶ X) (y : Y ⟶ Y') (n : ℤ)
      (z : (derivedCohomologyValue R n).obj ((rHomValue H).obj (op X, Y))) :
    equiv X' Y' n ((derivedCohomologyValue R n).map
        ((rHomValue H).map (Prod.mkHom x.op y)) z) =
      x ≫ equiv X Y n z ≫ (shiftFunctor (derivedValue.{a} R) n).map y
  on_models {X Y : (derivedValue.{a} R)} (P : Presentation X) (I : Presentation Y)
      (hP : P.complex.IsKProjective) (n : ℤ)
      (z : (internalHomValue P.complex I.complex).homology n) :
    equiv X Y n (((cohomologyFactorsValue R n).inv.app _ ≫
      (derivedCohomologyValue R n).map (homComparison H P I)) z) =
      P.iso.inv ≫ (quotientCompQhIsoValue R).inv.app P.complex ≫
        (Cochains.qhValue R).map (internalHomCohomologyValue P.complex I.complex n z) ≫
        (quotientCompQhIsoValue R).hom.app (I.complex⟦n⟧) ≫ (shiftedPresentation I n).hom

def ClosedType : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e} (T : DerivedTensor.Model M) (H : Models.{u,a} R),
    Nonempty (Closed T H)

def CohomologyType : Prop :=
  ∀ {R : Type u} [CommRing R] (H : Models.{u,a} R), Nonempty (Cohomology H)

def SingleReplacements : Prop :=
  DerivedHomModels.modelMapNaturalType.{u,a} ∧
  DerivedHomModels.modelMapIsIsoType.{u,a} ∧
  DerivedHomModels.strictComparisonsType.{u,a} ∧
  DerivedHomModels.modelChoiceIndependenceType.{u,a}

/-- Cohomology on a strictly presented original input uses the linear
identification from the exact same-ring coefficient lift. -/
def liftedCohomologyEquiv (B : compValue.{v} R) (n : ℤ) :
    B.homology n ≃ₗ[R]
      (derivedCohomologyValue.{max v t} R n).obj
        ((CochainCoefficientLift.liftD.{t,v} R).obj ((qValue R).obj B)) :=
  let L := CochainCoefficientLift.lift.{t,v} R
  let F := derivedCohomologyValue.{max v t} R n
  (CochainCoefficientLift.cohomologyEquiv.{t} B n).trans
    ((((cohomologyFactorsValue R n).app (L.obj B)).symm ≪≫
      F.mapIso ((CochainCoefficientLift.liftDFactors.{t,v} R).app B).symm).toLinearEquiv)

/-- Independently sized original inputs are placed into one adequate derived
category by the exact same-ring lifts. The adjunction and the cohomology
identifications are those on this common category. -/
def LiftedInputs : Prop :=
  ∀ (R : Type u) [CommRing R],
    let e := CochainRingTransport.uliftRingEquivValue.{max u v w t s} R
    ∃ (M : AdequateModel e) (T : DerivedTensor.Model M)
      (H : Models.{u,max u v w t s} R) (c : Closed T H) (_h : Cohomology H),
      (∀ (Z : derivedValue.{v} R) (X : derivedValue.{w} R) (Y : derivedValue.{t} R),
        let Z' := (CochainCoefficientLift.liftD.{max u w t s,v} R).obj Z
        let X' := (CochainCoefficientLift.liftD.{max u v t s,w} R).obj X
        let Y' := (CochainCoefficientLift.liftD.{max u v w s,t} R).obj Y
        ∃ adj : tensorRight T X' ⊣ homFrom H X',
          adj.homEquiv Z' Y' = (c.equiv Z' X' Y').toEquiv) ∧
      DerivedHomModels.originalComparisonType.{u,w,t,max v s} ∧
      DerivedHomModels.mixedProductComparisonType.{u,w,t,max v s}

end

end Specs.DerivedFormalization.DerivedHomAdjunction
