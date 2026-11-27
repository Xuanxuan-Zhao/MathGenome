import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.DerivedHom
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.DerivedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.OrdinaryDGTensorComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensorTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedHomModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.OrdinaryComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.PerfectHomBaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open _root_.DerivedFormalization _root_.DerivedFormalization.Affine

namespace Specs.DerivedFormalization.Affine.CotangentAmitsurModels

noncomputable section

universe u v w t x y

open Cochains (compValue derivedValue homotopyValue qValue qhValue quotientValue)
open Tensor (ModuleTensor dgCat term regular restrictFunctor)
open CotangentComplex (Model LiftedModel oneObject cdgaLift liftCDGA)
open DG.Derived (HomotopyCategoryLaws)
open DG.HomComplex (homotopyClass gradedHom component HomotopyEquation)
open DG.KProjective (isKProjective)
open Descent.PerfectHomBaseChange (extend extendComp extendId changeCoefficients
  changeHomCoefficients)
open CochainComplex.HomComplex (Cochain)
attribute [local instance] HasDerivedCategory.standard

abbrev CP (A : Type u) (C : Type v) [CommRing A] [CommRing C] [Algebra A C] (p : ℕ) :=
  AmitsurAlgebrasSpec.degree A C p

abbrev BP (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (p : ℕ) :=
  B ⊗[A] CP A C p

abbrev baseMap {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (p : ℕ) :=
  (Algebra.TensorProduct.includeLeft : B →ₐ[B] BP A B C p)

abbrev columnMap {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) : BP A B C p →ₐ[B] BP A B C q :=
  Algebra.TensorProduct.map (AlgHom.id B B) (AmitsurAlgebrasSpec.map f)

def RingPowers : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Module.FaithfullyFlat A C],
    Module.FaithfullyFlat B (B ⊗[A] C) ∧
    (∀ p : ℕ, Module.Flat A (CP A C p) ∧ Module.Flat B (BP A B C p)) ∧
    ∃ e : ∀ p : ℕ, BP A B C p ≃ₐ[B] AmitsurAlgebrasSpec.degree B (B ⊗[A] C) p,
      (∀ (p : ℕ) (i : Fin (p + 1)) (b : B) (c : C),
        e p (b ⊗ₜ[A] AmitsurAlgebrasSpec.factor A C i c) =
          AmitsurAlgebrasSpec.factor B (B ⊗[A] C) i (b ⊗ₜ[A] c)) ∧
      (∀ p : ℕ, (e p).toAlgHom.comp (baseMap p) =
        AmitsurAlgebrasSpec.unit B (B ⊗[A] C) (p + 1)) ∧
      ∀ {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)),
        (e q).toAlgHom.comp (columnMap f) =
          (AmitsurAlgebrasSpec.map f).comp (e p).toAlgHom

section Ordinary

variable {k : Type u} [Field k] [CharZero k]
variable {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A B] [Algebra A C]
variable [IsScalarTower k A B] [IsScalarTower k A C]

abbrev ordinary (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R] :=
  NonpositiveCDGA.ordinary (CommAlgCat.of k R)

/-- The stalk at the common bound is the actual A08 coefficient lift of the
original ordinary algebra. -/
abbrev transported (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R] :=
  liftCDGA.{u,v,t} (ordinary k R)

abbrev transportedMap {R S : Type v} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f : R →ₐ[k] S) : transported.{u,v,t} k R ⟶ transported.{u,v,t} k S :=
  (cdgaLift.{u,v,t} k).map (NonpositiveCDGA.ordinaryMap (CommAlgCat.ofHom f))

abbrev originalMap {R S : Type v} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f : R →ₐ[k] S) : ordinary k R ⟶ ordinary k S :=
  NonpositiveCDGA.ordinaryMap (CommAlgCat.ofHom f)

abbrev cpMap (p : ℕ) : A →ₐ[k] CP A C p := IsScalarTower.toAlgHom k A _
abbrev bpMap (p : ℕ) : B →ₐ[k] BP A B C p := (baseMap (A := A) (C := C) p).restrictScalars k

abbrev localMap (p : ℕ) : CP A C p →ₐ[k] BP A B C p :=
  (Algebra.TensorProduct.includeRight : CP A C p →ₐ[A] BP A B C p).restrictScalars k

abbrev localBaseMap (p : ℕ) :
    transported.{u,v,t} k (CP A C p) ⟶ transported.{u,v,t} k (BP A B C p) :=
  transportedMap (localMap (k := k) (A := A) (B := B) (C := C) p)

abbrev originalBaseMap : ordinary k A ⟶ ordinary k B :=
  originalMap (IsScalarTower.toAlgHom k A B)

abbrev liftedBaseMap : transported.{u,v,t} k A ⟶ transported.{u,v,t} k B :=
  transportedMap (IsScalarTower.toAlgHom k A B)

abbrev liftComplex {R : Type v} [CommRing R] (X : compValue.{w} R) :
    compValue.{max w t} R :=
  (CochainCoefficientLift.lift.{t,w} R).obj X

def FiniteProjective {R : Type v} [CommRing R] (P : compValue.{w} R) : Prop :=
  (∃ L U : ℤ, ∀ i : ℤ, (i < L ∨ U < i) → Subsingleton (P.X i)) ∧
  (∀ i : ℤ, Module.Finite R (P.X i)) ∧ ∀ i : ℤ, Module.Projective R (P.X i)

end Ordinary

section Comparison

open DG.DerivedKProjective (derivedCategoryInstance)
open CochainModels ( internalHomValue internalHomMapValue isKProjectiveValue)
open Opposite

variable {k : Type u} [Field k] [CharZero k]
variable {R : Type v} [CommRing R] [Algebra k R]

abbrev transportHomotopy (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R] :=
  DG.AmbientDerived.homotopyCategory.{u,v,0,t} (oneObject (ordinary k R))

abbrev transportDerived (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R]
    (h : HomotopyCategoryLaws (oneObject (transported.{u,v,t} k R))) :=
  DG.AmbientDerived.derivedCategory.{u,v,0,t} (oneObject (ordinary k R)) h

abbrev ordinaryRestriction (k : Type u) [Field k]
    (R : Type v) [CommRing R] [Algebra k R] :=
  (ModuleCat.restrictScalars.{max v t} (algebraMap k R)).mapHomologicalComplex (.up ℤ)

local instance transportedCommRing :
    CommRing (transported.{u,v,t} k R).toCommDGAlgebra.DegreeZero :=
  CommDGAlgebra.instCommRingDegreeZero (transported.{u,v,t} k R).toCommDGAlgebra

local instance transportedAlgebra :
    Algebra k (transported.{u,v,t} k R).toCommDGAlgebra.DegreeZero :=
  CommDGAlgebra.instAlgebraDegreeZero (transported.{u,v,t} k R).toCommDGAlgebra

set_option autoImplicit false in
/-- Comparison on the actual transported algebra. The maps on terms also
specify the action and identify homogeneous evaluation. -/
structure RingBridge (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R] where
  scalar : R ≃ₐ[k] (transported.{u,v,t} k R).toCommDGAlgebra.DegreeZero
  scalar_apply (r : R) : scalar r = ULift.up r
  strict : compValue.{max v t} R ≌ (transported.{u,v,t} k R).Module
  additive {X Y : compValue.{max v t} R} (f g : X ⟶ Y) :
    (strict.functor.map (f + g)).app () = (strict.functor.map f).app () + (strict.functor.map g).app ()
  terms (X : compValue.{max v t} R) :
    (ordinaryRestriction.{u,v,t} k R).obj X ≅ (strict.functor.obj X).complex ()
  terms_natural {X Y : compValue.{max v t} R} (f : X ⟶ Y) :
    (ordinaryRestriction.{u,v,t} k R).map f ≫ (terms Y).hom =
      (terms X).hom ≫ (strict.functor.map f).app ()
  action (X : compValue.{max v t} R) (i : ℤ) (r : R) (x : X.X i) :
    Tensor.act (strict.functor.obj X) i 0 i (add_zero i) ((terms X).hom.f i x) (scalar r) =
      (terms X).hom.f i (r • x)
  homotopy {X Y : compValue.{max v t} R} (f g : X ⟶ Y) :
    Nonempty (Homotopy f g) ↔
      ∃ z : gradedHom (strict.functor.obj X) (strict.functor.obj Y) (-1),
        HomotopyEquation (strict.functor.map f) (strict.functor.map g) z
  quasiIso {X Y : compValue.{max v t} R} (f : X ⟶ Y) :
    QuasiIso f ↔ DG.Module.quasiIsomorphism (strict.functor.map f)
  projective (X : compValue.{max v t} R) :
    isKProjectiveValue X ↔ isKProjective (strict.functor.obj X)
  hom (X Y : compValue.{max v t} R) :
    strict.functor.obj (internalHomValue X Y) ≅
      DerivedHom.internalHom (strict.functor.obj X) (strict.functor.obj Y)
  evaluation (X Y : compValue.{max v t} R) (n i j : ℤ) (h : i + n = j)
      (f : Cochain X Y n) (x : X.X i) :
    component ((hom X Y).hom.app () |>.f n |>.hom ((terms (internalHomValue X Y)).hom.f n f))
        () i j h ((terms X).hom.f i x) =
      (terms Y).hom.f j (f.v i j h x)

  hom_natural
      (S : DerivedHom.HomActions (transported.{u,v,t} k R).toCommDGAlgebra)
      (_hS : DerivedHom.HomActionLaws (transported.{u,v,t} k R).toCommDGAlgebra S)
      {X X' Y Y' : compValue.{max v t} R} (f : X' ⟶ X) (g : Y ⟶ Y') :
    strict.functor.map (internalHomMapValue f g) ≫ (hom X' Y').hom =
      (hom X Y).hom ≫ S.pre (strict.functor.obj Y) (strict.functor.map f) ≫
        S.post (strict.functor.obj X') (strict.functor.map g)

/-- The strict comparison viewed as input to the signed tensor models. -/
abbrev RingBridge.tensorInput (E : RingBridge.{u,v,t} k R) :
    OrdinaryDGTensorComparison.StrictComparison.{u,v,t} k R :=
  ⟨E.scalar, E.scalar_apply, E.strict.functor, E.terms, E.terms_natural, E.action⟩

open Opposite in
/-- The equivalence compares the whole ordinary localization with the
one-object ambient dg localization and agrees with the strict comparison. -/
def RingBridge.Localizes (E : RingBridge.{u,v,t} k R)
    (h : HomotopyCategoryLaws (oneObject (transported.{u,v,t} k R))) : Prop :=
  let A := (transported.{u,v,t} k R).toCommDGAlgebra
  let G := oneObject (transported.{u,v,t} k R)
  letI := DG.Derived.homotopyCategory G h
  letI := derivedCategoryInstance G h
  let Q := DG.AmbientDerived.quotient.{u,v,0,t} (oneObject (ordinary k R)) h
  ∃ (K : homotopyValue.{max v t} R ≌ transportHomotopy.{u,v,t} k R)
    (D : derivedValue.{max v t} R ≌ transportDerived.{u,v,t} k R h)
    (a : ∀ X : compValue.{max v t} R, K.functor.obj ((quotientValue R).obj X) ≅
      (E.strict.functor.obj X : transportHomotopy.{u,v,t} k R))
    (τ : qhValue R ⋙ D.functor ≅ K.functor ⋙ Q),
    (∀ {X Y : compValue.{max v t} R} (f : X ⟶ Y),
      K.functor.map ((quotientValue R).map f) ≫ (a Y).hom =
        (a X).hom ≫ homotopyClass (E.strict.functor.map f)) ∧
    let KD := transportHomotopy.{u,v,t} k R
    let DD := transportDerived.{u,v,t} k R h
    let J : DerivedHom.Kp A h ⥤ KD := (DG.DerivedKProjective.kProjectiveObjects G).ι
    let Qp := DG.DerivedKProjective.restrictedLocalization G h
    ∀ (O : DerivedHomModels.Models.{v,max v t} R)
      (S : DerivedHom.HomActions A) (H : KDᵒᵖ × KD ⥤ KD) (F : DDᵒᵖ × DD ⥤ DD),
      DerivedHom.HomActionLaws A S →
      ∀ (objH : ∀ (X Y : A.Module), H.obj (op X, Y) = DerivedHom.internalHom X Y),
      (∀ {X X' Y Y' : A.Module} (f : X' ⟶ X) (g : Y ⟶ Y'),
        let f₀ : @Quiver.Hom KD (DG.Derived.homotopyCategory G h).toQuiver X' X := homotopyClass f
        let g₀ : @Quiver.Hom KD (DG.Derived.homotopyCategory G h).toQuiver Y Y' := homotopyClass g
        HEq (H.map (Prod.mkHom f₀.op g₀)) (homotopyClass (S.pre Y f ≫ S.post X' g))) →
      ∀ (σ : Qp.op.prod Q ⋙ F ≅ J.op.prod (𝟭 KD) ⋙ H ⋙ Q),
        ∃ β : DerivedHomModels.rHomValue O ⋙ D.functor ≅ D.functor.op.prod D.functor ⋙ F,
          ∀ (X Y : compValue.{max v t} R) (hX : isKProjectiveValue X),
            let X₀ : DerivedHomModels.Representative ((qValue R).obj X) :=
              ⟨(quotientValue R).obj X, Iso.refl _⟩
            let Y₀ : DerivedHomModels.Representative ((qValue R).obj Y) :=
              ⟨(quotientValue R).obj Y, Iso.refl _⟩
            let ρ (V : compValue.{max v t} R) :=
              τ.app ((quotientValue R).obj V) ≪≫ Q.mapIso (a V)
            let U : DerivedHom.Kp A h := ⟨E.strict.functor.obj X, (E.projective X).mp hX⟩
            let V : KD := E.strict.functor.obj Y
            let pair := ((ρ X).symm.op).prod (ρ Y)
            D.functor.map (eqToHom (O.hom.obj_eq X₀.obj Y₀.obj).symm ≫
                DerivedHomModels.modelMap O X₀ Y₀) ≫
              β.hom.app (op ((qValue R).obj X), (qValue R).obj Y) ≫
              F.map pair.hom ≫ (σ.app (op U, V)).hom ≫
              Q.map (eqToHom (objH (E.strict.functor.obj X) (E.strict.functor.obj Y))) =
            (ρ (internalHomValue X Y)).hom ≫ Q.map (homotopyClass (E.hom X Y).hom)

def OrdinaryBridge : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (R : Type v) [CommRing R] [Algebra k R],
    ∃ E : RingBridge.{u,v,t} k R,
      ∀ h : HomotopyCategoryLaws (oneObject (transported.{u,v,t} k R)), E.Localizes h

abbrev dgExtension (T : ModuleTensor.{u,max v t} k)
    {S : Type v} [CommRing S] [Algebra k S] (f : R →ₐ[k] S) :
    (transported.{u,v,t} k R).Module ⥤ (transported.{u,v,t} k S).Module :=
  T.baseChange (transportedMap f : (transported.{u,v,t} k R).toCommDGAlgebra ⟶
    (transported.{u,v,t} k S).toCommDGAlgebra)

/-- The comparison between the two strict signed tensor models. -/
abbrev TensorComparison (E : RingBridge.{u,v,t} k R) (T : ModuleTensor.{u,max v t} k) :=
  ∀ X Y : compValue.{max v t} R, E.strict.functor.obj (CochainTensor.tensor X Y) ≅
    T.obj (𝟙 (transported.{u,v,t} k R).toCommDGAlgebra) (E.strict.functor.obj X)
      (E.strict.functor.obj Y)

open DG.DerivedKProjective (kProjectiveObjects restrictedLocalization) in
/-- The localized component on K-projectives uses the actual resolution
section and inverts the image of the same strict tensor isomorphism. -/
def TensorComparison.Localized (E : RingBridge.{u,v,t} k R)
    (T : ModuleTensor.{u,max v t} k) (e : TensorComparison.{u,v,t} E T) : Prop :=
  let A := (transported.{u,v,t} k R).toCommDGAlgebra
  ∀ (h : HomotopyCategoryLaws (dgCat A)) (H : DerivedTensor.HomotopyTensor T (𝟙 A) h h),
    letI := DG.Derived.homotopyCategory (dgCat A) h
    letI := derivedCategoryInstance (dgCat A) h
    let Q := DG.Derived.quotient (dgCat A) h
    ∀ (I : (restrictedLocalization (dgCat A) h).IsEquivalence),
      letI := I
      let L := (restrictedLocalization (dgCat A) h).asEquivalence
      let J := (kProjectiveObjects (dgCat A)).ι
      ∀ (X Y : compValue.{max v t} R) (hX : isKProjectiveValue X) (hY : isKProjectiveValue Y),
        let P := E.strict.functor.obj X
        let N := E.strict.functor.obj Y
        let P₀ : (kProjectiveObjects (dgCat A)).FullSubcategory := ⟨P, (E.projective X).mp hX⟩
        let N₀ : (kProjectiveObjects (dgCat A)).FullSubcategory := ⟨N, (E.projective Y).mp hY⟩
        let ε := ((J.mapIso (L.unitIso.app P₀)).symm).prod ((J.mapIso (L.unitIso.app N₀)).symm)
        let d := (H.functor ⋙ Q).mapIso ε ≪≫ Q.mapIso (eqToIso (H.obj P N))
        ∃ a : (DerivedTensor.derivedTensorValue T h H I).obj (Q.obj P, Q.obj N) ≅
            Q.obj (E.strict.functor.obj (CochainTensor.tensor X Y)),
          a.hom = d.hom ≫ Q.map (homotopyClass (e X Y).inv)

/-- The signed tensor comparisons use identical homogeneous pure generators. -/
def TensorBridge (E : RingBridge.{u,v,t} k R) (T : ModuleTensor.{u,max v t} k) : Prop :=
  ∃ (_U : CochainTensorTransport.AdequateModel E.scalar.toRingEquiv)
    (e : TensorComparison.{u,v,t} E T),
    (∀ (X Y : compValue.{max v t} R) (i j n : ℤ) (h : i + j = n) (x : X.X i) (y : Y.X j),
      ((e X Y).hom.app ()).f n ((E.terms (CochainTensor.tensor X Y)).hom.f n
        (CochainTensor.pure X Y h x y)) =
      T.tmul (𝟙 (transported.{u,v,t} k R).toCommDGAlgebra) i j n h
        ((E.terms X).hom.f i x) ((E.terms Y).hom.f j y)) ∧
    e.Localized E T

variable {S : Type v} [CommRing S] [Algebra k S] [Algebra R S] [IsScalarTower k R S]

/-- The ordinary tensor writes the scalar first. The same generator in
the right dg module tensor writes the degree-zero scalar last. -/
structure ExtensionBridge (E : RingBridge.{u,v,t} k R) (F : RingBridge.{u,v,t} k S)
    (T : ModuleTensor.{u,max v t} k) where
  iso : (extend.{v,v,max v t} R S) ⋙ F.strict.functor ≅
    E.strict.functor ⋙ dgExtension T (IsScalarTower.toAlgHom k R S)
  on_tmul (X : compValue.{max v t} R) (i : ℤ) (s : S) (x : X.X i) :
    ((iso.hom.app X).app ()).f i ((F.terms ((extend.{v,v,max v t} R S).obj X)).hom.f i (s ⊗ₜ[R] x)) =
      T.tmul (transportedMap (IsScalarTower.toAlgHom k R S) :
          (transported.{u,v,t} k R).toCommDGAlgebra ⟶ (transported.{u,v,t} k S).toCommDGAlgebra)
        (N := regular (transported.{u,v,t} k S).toCommDGAlgebra)
        i 0 i (add_zero i) ((E.terms X).hom.f i x) (F.scalar s)

/-- The extension comparison in the ordinary and dg tensor interface. -/
abbrev ExtensionBridge.tensorInput {E : RingBridge.{u,v,t} k R} {F : RingBridge.{u,v,t} k S}
    {T : ModuleTensor.{u,max v t} k} (e : ExtensionBridge.{u,v,t} E F T) :
    OrdinaryDGTensorComparison.ExtensionComparison E.tensorInput F.tensorInput T :=
  ⟨e.iso, e.on_tmul⟩

open OrdinaryDGTensorComparison (scalarMap) in
/-- The scalar-identity stalk map is normalized to the identity dg map
before applying the signed tensor unit. -/
def ExtensionBridge.Unit (E : RingBridge.{u,v,t} k R) (T : ModuleTensor.{u,max v t} k)
    (e : ExtensionBridge.{u,v,t} E E T) : Prop :=
  let A := (transported.{u,v,t} k R).toCommDGAlgebra
  ∃ eq : scalarMap.{u,v,t} k R R = 𝟙 A,
    ∀ X : compValue.{max v t} R,
      let M := E.strict.functor.obj X
      ∃ a : (T.baseChange (𝟙 A)).obj M ≅ M,
        ((e.iso.app X).hom ≫ eqToHom (congrArg (fun r => (T.baseChange r).obj M) eq)) ≫ a.hom =
          E.strict.functor.map (extendId R X).hom ∧
        ∀ (i j n : ℤ) (h : i + j = n) (x : term M i) (r : A.complex.X j),
          (a.hom.app ()).f n (T.tmul (𝟙 A) (N := regular A) i j n h x r) =
            Tensor.act M i j n h x r

variable {V : Type v} [CommRing V] [Algebra k V] [Algebra R V] [Algebra S V]
  [IsScalarTower k R V] [IsScalarTower k S V] [IsScalarTower R S V]

open OrdinaryDGTensorComparison (scalarMap TowerOnPure TowerSquare) in
/-- The ordinary associator is compared with the dg associator on the
composite of the two specified maps. -/
def ExtensionBridge.Composition (E : RingBridge.{u,v,t} k R) (F : RingBridge.{u,v,t} k S)
    (G : RingBridge.{u,v,t} k V) (T : ModuleTensor.{u,max v t} k)
    (e : ExtensionBridge.{u,v,t} E F T) (f : ExtensionBridge.{u,v,t} F G T)
    (g : ExtensionBridge.{u,v,t} E G T) : Prop :=
  let r := scalarMap.{u,v,t} k R S
  let s := scalarMap.{u,v,t} k S V
  ∃ eq : r ≫ s = scalarMap.{u,v,t} k R V,
    ∀ X : compValue.{max v t} R,
      let M := E.strict.functor.obj X
      ∃ a : (T.baseChange s).obj ((T.baseChange r).obj M) ≅ (T.baseChange (r ≫ s)).obj M,
        TowerOnPure T M a.hom ∧
          TowerSquare E.tensorInput T F.tensorInput G.tensorInput
            e.tensorInput f.tensorInput g.tensorInput eq X a.hom

/-- Compare a specified realization of the derived scalar extension with
the ordinary scalar extension, using the strict map on K-projectives. -/
def ExtensionBridge.Localized (E : RingBridge.{u,v,t} k R) (F : RingBridge.{u,v,t} k S)
    (T : ModuleTensor.{u,max v t} k) (e : ExtensionBridge.{u,v,t} E F T)
    (hR : HomotopyCategoryLaws (oneObject (transported.{u,v,t} k R)))
    (hS : HomotopyCategoryLaws (oneObject (transported.{u,v,t} k S)))
    (W : DerivedTensor.ScalarExtension T
      (transportedMap.{u,v,t} (IsScalarTower.toAlgHom k R S) :
        (transported.{u,v,t} k R).toCommDGAlgebra ⟶ (transported.{u,v,t} k S).toCommDGAlgebra)
      hR hS) : Prop :=
  let R' := (transported.{u,v,t} k R).toCommDGAlgebra
  let S' := (transported.{u,v,t} k S).toCommDGAlgebra
  letI := DG.Derived.homotopyCategory (dgCat R') hR
  letI := DG.Derived.homotopyCategory (dgCat S') hS
  letI := derivedCategoryInstance (dgCat R') hR
  letI := derivedCategoryInstance (dgCat S') hS
  let QR := DG.Derived.quotient (dgCat R') hR
  let QS := DG.Derived.quotient (dgCat S') hS
  ∀ (P : compValue.{max v t} R) (hP : isKProjectiveValue P),
    let h := (E.projective P).mp hP
    ∃ a : W.functor.obj (QR.obj (E.strict.functor.obj P)) ≅
      QS.obj (F.strict.functor.obj ((extend.{v,v,max v t} R S).obj P)),
      a.hom = (W.onProjective (E.strict.functor.obj P) h).hom ≫
        QS.map (CotangentComplex.moduleClass hS (e.iso.inv.app P))

/-- The strict composition appearing in the projective comparison of the
derived extensions is sent to the ordinary F08a associator. -/
def ExtensionBridge.DerivedComposition (E : RingBridge.{u,v,t} k R)
    (F : RingBridge.{u,v,t} k S) (G : RingBridge.{u,v,t} k V)
    (T : ModuleTensor.{u,max v t} k)
    (e : ExtensionBridge.{u,v,t} E F T) (f : ExtensionBridge.{u,v,t} F G T)
    (g : ExtensionBridge.{u,v,t} E G T)
    (h : ∀ U : CommDGAlgebra.{u,max v t} k, HomotopyCategoryLaws (dgCat U))
    (W : ∀ {U U' : CommDGAlgebra.{u,max v t} k} (a : U ⟶ U'),
      DerivedTensor.ScalarExtension T a (h U) (h U')) : Prop :=
  let R' := (transported.{u,v,t} k R).toCommDGAlgebra
  let S' := (transported.{u,v,t} k S).toCommDGAlgebra
  let V' := (transported.{u,v,t} k V).toCommDGAlgebra
  let r : R' ⟶ S' := transportedMap (IsScalarTower.toAlgHom k R S)
  let s : S' ⟶ V' := transportedMap (IsScalarTower.toAlgHom k S V)
  let t₀ : R' ⟶ V' := transportedMap (IsScalarTower.toAlgHom k R V)
  letI := DG.Derived.homotopyCategory (dgCat R') (h R')
  letI := DG.Derived.homotopyCategory (dgCat S') (h S')
  letI := DG.Derived.homotopyCategory (dgCat V') (h V')
  letI := derivedCategoryInstance (dgCat R') (h R')
  letI := derivedCategoryInstance (dgCat S') (h S')
  letI := derivedCategoryInstance (dgCat V') (h V')
  let QR := DG.Derived.quotient (dgCat R') (h R')
  let QV := DG.Derived.quotient (dgCat V') (h V')
  ∃ eq : r ≫ s = t₀,
    ∃ (a : T.baseChange r ⋙ T.baseChange s ≅ T.baseChange (r ≫ s))
      (b : (W r).functor ⋙ (W s).functor ≅ (W (r ≫ s)).functor),
      (∀ X : compValue.{max v t} R,
        (f.iso.app ((extend.{v,v,max v t} R S).obj X)).hom ≫
          (T.baseChange s).map (e.iso.app X).hom ≫ a.hom.app (E.strict.functor.obj X) ≫
          eqToHom (congrArg (fun r' => (T.baseChange r').obj (E.strict.functor.obj X)) eq) =
        G.strict.functor.map (extendComp.{v,v,max v t} R S V X).hom ≫ (g.iso.app X).hom) ∧
      ∀ (P : R'.Module) (hP : isKProjective P),
        ∃ h₁ : isKProjective ((T.baseChange r).obj P),
          b.hom.app (QR.obj P) ≫ ((W (r ≫ s)).onProjective P hP).hom =
            (W s).functor.map ((W r).onProjective P hP).hom ≫
            ((W s).onProjective ((T.baseChange r).obj P) h₁).hom ≫
            QV.map (homotopyClass (a.hom.app P))

/-- At the native common level the same comparison is an equivalence with
the original one-object localization, using the inverse ambient transport. -/
def NativeLocalization : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (R : Type v) [CommRing R] [Algebra k R]
    (E : RingBridge.{u,v,0} k R)
    (h : HomotopyCategoryLaws (oneObject (ordinary k R))),
    let G := oneObject (ordinary k R)
    letI := DG.Derived.homotopyCategory G h
    letI := derivedCategoryInstance G h
    let Q := DG.Derived.quotient G h
    let F := E.strict.functor ⋙ DG.AmbientDerived.transportToNative.{u,v,0,0} G
    ∃ (K : homotopyValue.{v} R ≌ DG.HomComplex.homotopyCategory G)
      (D : derivedValue.{v} R ≌ DG.Derived.derivedCategory G h)
      (a : ∀ X : compValue.{v} R, K.functor.obj ((quotientValue R).obj X) ≅
        (F.obj X : DG.HomComplex.homotopyCategory G)),
      (∀ {X Y : compValue.{v} R} (f : X ⟶ Y),
        K.functor.map ((quotientValue R).map f) ≫ (a Y).hom =
          (a X).hom ≫ homotopyClass (F.map f)) ∧
      Nonempty (qhValue R ⋙ D.functor ≅ K.functor ⋙ Q)

end Comparison

section Models


open CotangentBaseChange (IsSymbolMap symbolTensor)
open DerivedHom (internalHom)
open CochainModels (internalHomValue isKProjectiveValue)
open Descent.PerfectHomBaseChange (restrict)


variable {k : Type u} [Field k] [CharZero k]
variable {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A B] [Algebra A C]
variable [IsScalarTower k A B] [IsScalarTower k A C]

local notation "g₀" => originalBaseMap (k := k) (A := A) (B := B)
local notation "Cₚ" => CP A C
local notation "Bₚ" => BP A B C
local notation "aₚ" => cpMap (k := k) (A := A) (C := C)
local notation "bₚ" => bpMap (k := k) (A := A) (B := B) (C := C)

/-- Both scalar extension squares are fixed, with the ordinary tensor ring
at the bottom right and the flat extension of the single resolution above it. -/
structure FlatColumn (T : ModuleTensor.{u,max v t} k) (M : Model ((liftedBaseMap.{u,v,t} (k := k) (A := A) (B := B)) : _))
    (p : ℕ) where
  model : Model ((localBaseMap.{u,v,t} (k := k) (A := A) (B := B) (C := C) p))
  resolutionMap : M.algebra ⟶ model.algebra
  resolutionPushout : IsPushout M.base (transportedMap (aₚ p)) resolutionMap model.base
  ordinaryPushout : IsPushout (liftedBaseMap.{u,v,t} (k := k) (A := A) (B := B)) (transportedMap (aₚ p)) (transportedMap (bₚ p)) ((localBaseMap.{u,v,t} (k := k) (A := A) (B := B) (C := C) p))
  augmentation_comm : resolutionMap ≫ model.augmentation =
    M.augmentation ≫ transportedMap (bₚ p)
  comparison : (dgExtension T (bₚ p)).obj (M.module T) ≅ model.module T
  symbols (i j l m n : ℤ) (hm : i + j = m) (hn : m + l = n)
      (x : M.algebra.complex.X i) (b : (transported.{u,v,t} k B).complex.X j)
      (s : (transported.{u,v,t} k (Bₚ p)).complex.X l) :
    (comparison.hom.app ()).f n
      (T.tmul (transportedMap (bₚ p) : _ ⟶ (transported.{u,v,t} k (Bₚ p)).toCommDGAlgebra)
        (N := regular (transported.{u,v,t} k (Bₚ p)).toCommDGAlgebra)
        m l n hn (symbolTensor T M.differentials M.augmentation i j m hm x b) s) =
    symbolTensor T model.differentials model.augmentation i (j + l) n (by omega)
      (resolutionMap.chainMap.f i x)
      ((transported.{u,v,t} k (Bₚ p)).mul j l (j + l) rfl ((transportedMap (bₚ p)).chainMap.f j b) s)

abbrev cMap {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) : Cₚ p →ₐ[k] Cₚ q :=
  (AmitsurAlgebrasSpec.map f : Cₚ p →ₐ[A] Cₚ q).restrictScalars k

abbrev bMap {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) : Bₚ p →ₐ[k] Bₚ q :=
  (columnMap f : Bₚ p →ₐ[B] Bₚ q).restrictScalars k

/-- At the strict level the cofaces act on a differential symbol by applying
the map of extended resolutions and on the coefficient by the ring map. -/
structure FlatColumnMap {T : ModuleTensor.{u,max v t} k} {M : Model ((liftedBaseMap.{u,v,t} (k := k) (A := A) (B := B)) : _)}
    (X : FlatColumn (C := C) T M p) (Y : FlatColumn (C := C) T M q)
    (f : Fin (p + 1) → Fin (q + 1)) where
  algebraMap : X.model.algebra ⟶ Y.model.algebra
  fromResolution : X.resolutionMap ≫ algebraMap = Y.resolutionMap
  fromBase : X.model.base ≫ algebraMap = transportedMap (cMap (A := A) (C := C) f) ≫ Y.model.base
  overTarget : X.model.augmentation ≫ transportedMap (bMap (A := A) (B := B) (C := C) f) = algebraMap ≫ Y.model.augmentation
  cotangentMap : X.model.module T ⟶
    Tensor.restrict (transportedMap (bMap (A := A) (B := B) (C := C) f) :
      (transported.{u,v,t} k (Bₚ p)).toCommDGAlgebra ⟶
        (transported.{u,v,t} k (Bₚ q)).toCommDGAlgebra) (Y.model.module T)
  symbols : IsSymbolMap T X.model.differentials Y.model.differentials
    X.model.augmentation Y.model.augmentation algebraMap (transportedMap (bMap (A := A) (B := B) (C := C) f)) cotangentMap

abbrev extColumn (X : compValue.{max v t} B) (p : ℕ) : compValue.{max v t} (Bₚ p) :=
  (extend.{v,v,max v t} B (Bₚ p)).obj X

/-- Augmentation and column maps on original-ring ordinary complexes. -/
abbrev ordinaryColumnMap (X : compValue.{max v t} B) {p q : ℕ}
    (f : Fin (p + 1) → Fin (q + 1)) :
    (Descent.PerfectHomBaseChange.restrict.{v,v,max v t} B (Bₚ p)).obj (extColumn X p) ⟶
      (Descent.PerfectHomBaseChange.restrict.{v,v,max v t} B (Bₚ q)).obj (extColumn X q) :=
  let φ : Bₚ p →ₐ[B] Bₚ q := columnMap f
  letI : Algebra (Bₚ p) (Bₚ q) := φ.toRingHom.toAlgebra
  letI : IsScalarTower B (Bₚ p) (Bₚ q) := IsScalarTower.of_algHom φ
  changeCoefficients.{v,v,max v t} B (Bₚ p) (Bₚ q) X

abbrev ordinaryHomColumnMap (P X : compValue.{max v t} B) {p q : ℕ}
    (f : Fin (p + 1) → Fin (q + 1)) :
    (Descent.PerfectHomBaseChange.restrict.{v,v,max v t} B (Bₚ p)).obj (internalHomValue (extColumn P p) (extColumn X p)) ⟶
      (Descent.PerfectHomBaseChange.restrict.{v,v,max v t} B (Bₚ q)).obj (internalHomValue (extColumn P q) (extColumn X q)) :=
  let φ : Bₚ p →ₐ[B] Bₚ q := columnMap f
  letI : Algebra (Bₚ p) (Bₚ q) := φ.toRingHom.toAlgebra
  letI : IsScalarTower B (Bₚ p) (Bₚ q) := IsScalarTower.of_algHom φ
  changeHomCoefficients.{v,v,max v t} B (Bₚ p) (Bₚ q) P X

/-- All strict identifications use the same comparison at the original ring.
The coface condition is equality of chain maps on their underlying functions. -/
structure CompatibleColumns (T : ModuleTensor.{u,max v t} k) (M : Model ((liftedBaseMap.{u,v,t} (k := k) (A := A) (B := B)) : _))
    (E : RingBridge.{u,v,t} k B) (F : ∀ p : ℕ, RingBridge.{u,v,t} k (Bₚ p)) where
  L : compValue.{max v t} B
  global : E.strict.functor.obj L ≅ M.module T
  column (p : ℕ) : FlatColumn (C := C) T M p
  extension (p : ℕ) : ExtensionBridge.{u,v,t} E (F p) T
  coface {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) : FlatColumnMap (column p) (column q) f
  coface_id (p : ℕ) : (coface (id : Fin (p + 1) → Fin (p + 1))).algebraMap = 𝟙 _
  coface_comp {p q r : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (g : Fin (q + 1) → Fin (r + 1)) :
    (coface (g ∘ f)).algebraMap = (coface f).algebraMap ≫ (coface g).algebraMap
  natural (p q : ℕ) (f : Fin (p + 1) → Fin (q + 1)) (i : ℤ) (s : Bₚ p) (x : L.X i) :
    let e (j : ℕ) :=
      (extension j).iso.app L ≪≫ (dgExtension T (bₚ j)).mapIso global ≪≫ (column j).comparison
    ((coface f).cotangentMap.app ()).f i
        (((e p).hom.app ()).f i (((F p).terms (extColumn L p)).hom.f i
          (s ⊗ₜ[B] x))) =
      ((e q).hom.app ()).f i (((F q).terms (extColumn L q)).hom.f i
        ((ordinaryColumnMap (A := A) (C := C) L f).f i (s ⊗ₜ[B] x)))

abbrev CompatibleColumns.identification {T : ModuleTensor.{u,max v t} k} {M : Model ((liftedBaseMap.{u,v,t} (k := k) (A := A) (B := B)) : _)}
    {E : RingBridge.{u,v,t} k B} {F : ∀ p : ℕ, RingBridge.{u,v,t} k (Bₚ p)}
    (D : CompatibleColumns T M E F) (p : ℕ) :
    (F p).strict.functor.obj (extColumn D.L p) ≅ (D.column p).model.module T :=
  (D.extension p).iso.app D.L ≪≫ (dgExtension T (bₚ p)).mapIso D.global ≪≫ (D.column p).comparison

/-- Lift the prescribed derived isomorphism, then extend that very chain map
in each column of the Amitsur diagram. -/
def CompatibleColumns.Represents {T : ModuleTensor.{u,max v t} k} {M : Model ((liftedBaseMap.{u,v,t} (k := k) (A := A) (B := B)) : _)}
    {E : RingBridge.{u,v,t} k B} {F : ∀ p : ℕ, RingBridge.{u,v,t} k (Bₚ p)}
    (D : CompatibleColumns T M E F) : Prop :=
  ∀ (P' : compValue.{max v t} B), FiniteProjective P' →
      ∀ α : (qValue B).obj P' ≅ (qValue B).obj D.L,
      ∃ c : P' ⟶ D.L, isKProjectiveValue P' ∧ QuasiIso c ∧ (qValue B).map c = α.hom ∧
        (∀ p : ℕ, isKProjectiveValue (extColumn (A := A) (C := C) P' p) ∧
          QuasiIso ((extend.{v,v,max v t} B (Bₚ p)).map c)) ∧
        ∀ (p q : ℕ) (f : Fin (p + 1) → Fin (q + 1)),
          (Descent.PerfectHomBaseChange.restrict.{v,v,max v t} B (Bₚ p)).map ((extend.{v,v,max v t} B (Bₚ p)).map c) ≫
            ordinaryColumnMap (A := A) (C := C) D.L f =
          ordinaryColumnMap (A := A) (C := C) P' f ≫
            (Descent.PerfectHomBaseChange.restrict.{v,v,max v t} B (Bₚ q)).map ((extend.{v,v,max v t} B (Bₚ q)).map c)

/-- The strict Hom cofaces are the same scalar-extension maps as in the
ordinary perfect Hom comparison. This equation tests each homogeneous
map on the base change of each homogeneous input element. -/
structure CompatibleHomColumns (E : RingBridge.{u,v,t} k B)
    (F : ∀ p : ℕ, RingBridge.{u,v,t} k (Bₚ p)) where
  augmentation (p : ℕ) (P X : compValue.{max v t} B) :
    internalHom (E.strict.functor.obj P) (E.strict.functor.obj X) ⟶
      Tensor.restrict (transportedMap (bₚ p) :
        (transported.{u,v,t} k B).toCommDGAlgebra ⟶ (transported.{u,v,t} k (Bₚ p)).toCommDGAlgebra)
        (internalHom ((F p).strict.functor.obj (extColumn P p)) ((F p).strict.functor.obj (extColumn X p)))
  augmentation_ordinary (p : ℕ) (P X : compValue.{max v t} B)
      (n : ℤ) (z : Cochain P X n) :
    let a := (E.terms (internalHomValue P X)).hom ≫ ((E.hom P X).hom.app ())
    let b := ((F p).terms (internalHomValue (extColumn P p) (extColumn X p))).hom ≫
      (((F p).hom (extColumn P p) (extColumn X p)).hom.app ())
    ((augmentation p P X).app ()).f n (a.f n z) =
      b.f n (Descent.PerfectHomBaseChange.extendCochain (Bₚ p) n z)
  map {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (P X : compValue.{max v t} B) :
    internalHom ((F p).strict.functor.obj (extColumn P p)) ((F p).strict.functor.obj (extColumn X p)) ⟶
      Tensor.restrict (transportedMap (bMap (A := A) (B := B) (C := C) f) :
        (transported.{u,v,t} k (Bₚ p)).toCommDGAlgebra ⟶
          (transported.{u,v,t} k (Bₚ q)).toCommDGAlgebra)
        (internalHom ((F q).strict.functor.obj (extColumn P q)) ((F q).strict.functor.obj (extColumn X q)))
  map_id (p : ℕ) (P X : compValue.{max v t} B) :
    (map (id : Fin (p + 1) → Fin (p + 1)) P X).app () = 𝟙 _
  map_comp {p q r : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (g : Fin (q + 1) → Fin (r + 1))
      (P X : compValue.{max v t} B) :
    (map (g ∘ f) P X).app () = (map f P X).app () ≫ (map g P X).app ()
  augmentation_comp {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (P X : compValue.{max v t} B) :
    (augmentation p P X).app () ≫ (map f P X).app () = (augmentation q P X).app ()
  ordinary {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (P X : compValue.{max v t} B) :
    let a (j : ℕ) := ((F j).terms (internalHomValue (extColumn P j) (extColumn X j))).hom ≫
      (((F j).hom (extColumn P j) (extColumn X j)).hom.app ())
    ∀ (n : ℤ) (z : Cochain (extColumn P p) (extColumn X p) n),
      ((map f P X).app ()).f n ((a p).f n z) =
        (a q).f n ((ordinaryHomColumnMap (A := A) (C := C) P X f).f n z)
  evaluation {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (P X : compValue.{max v t} B) :
    let a (j : ℕ) := ((F j).terms (internalHomValue (extColumn P j) (extColumn X j))).hom ≫
      (((F j).hom (extColumn P j) (extColumn X j)).hom.app ())
    ∀ (n i j : ℤ) (h : i + n = j) (z : Cochain (extColumn P p) (extColumn X p) n)
        (x : (extColumn (A := A) (C := C) P p).X i),
      component (((map f P X).app ()).f n ((a p).f n z)) () i j h
        (((F q).terms (extColumn P q)).hom.f i ((ordinaryColumnMap (A := A) (C := C) P f).f i x)) =
      ((F q).terms (extColumn X q)).hom.f j ((ordinaryColumnMap (A := A) (C := C) X f).f j (z.v i j h x))
  baseChangeIso (P X : compValue.{max v t} B) (_hP : FiniteProjective P) (p : ℕ) :
    IsIso (Descent.PerfectHomBaseChange.comparison (Bₚ p) P X)

def CompatibleColumns.CoherentExtensions {T : ModuleTensor.{u,max v t} k}
    {M : Model (liftedBaseMap.{u,v,t} (k := k) (A := A) (B := B))}
    {E : RingBridge.{u,v,t} k B} {F : ∀ p : ℕ, RingBridge.{u,v,t} k (Bₚ p)}
    (D : CompatibleColumns T M E F) : Prop :=
  (∃ e : ExtensionBridge.{u,v,t} E E T, e.Unit E T) ∧
  (∀ p : ℕ, ∃ e : ExtensionBridge.{u,v,t} (F p) (F p) T, e.Unit (F p) T) ∧
  ∀ (h : ∀ U : CommDGAlgebra.{u,max v t} k, HomotopyCategoryLaws (dgCat U)),
  ∃ W : ∀ {U U' : CommDGAlgebra.{u,max v t} k} (a : U ⟶ U'),
      DerivedTensor.ScalarExtension T a (h U) (h U'),
    (∀ p : ℕ, (D.extension p).Localized E (F p) T (h _) (h _)
      (W (transportedMap (bₚ p)))) ∧
    ∀ {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)),
      let φ : Bₚ p →ₐ[B] Bₚ q := columnMap f
      letI : Algebra (Bₚ p) (Bₚ q) := φ.toRingHom.toAlgebra
      letI : IsScalarTower B (Bₚ p) (Bₚ q) := IsScalarTower.of_algHom φ
      letI : IsScalarTower k (Bₚ p) (Bₚ q) :=
        IsScalarTower.of_algHom (φ.restrictScalars k)
      ∃ e : ExtensionBridge.{u,v,t} (F p) (F q) T,
        ExtensionBridge.Composition E (F p) (F q) T (D.extension p) e (D.extension q) ∧
        e.Localized (F p) (F q) T (h _) (h _) (W (transportedMap (φ.restrictScalars k))) ∧
        ExtensionBridge.DerivedComposition E (F p) (F q) T (D.extension p) e (D.extension q) h W

set_option linter.checkUnivs false in
/-- Keep the original ordinary coefficient ring and lift the two original
term levels into the one bound used throughout the diagram. -/
def CompatibleColumns.OriginalInputs
    {T : ModuleTensor.{u,max v (max u w x t)} k}
    {M : Model (liftedBaseMap.{u,v,max u w x t} (k := k) (A := A) (B := B))}
    {E : RingBridge.{u,v,max u w x t} k B}
    {F : ∀ p : ℕ, RingBridge.{u,v,max u w x t} k (Bₚ p)}
    (D : CompatibleColumns T M E F) : Prop :=
  ∀ (P₀ : compValue.{w} B) (X₀ : compValue.{x} B), FiniteProjective P₀ →
    let P := liftComplex.{v,w,max u v x t} P₀
    let X := liftComplex.{v,x,max u v w t} X₀
    FiniteProjective P ∧
    ∀ α : (qValue B).obj P ≅ (qValue B).obj D.L,
      ∃ c : P ⟶ D.L,
        isKProjectiveValue P ∧ QuasiIso c ∧ (qValue B).map c = α.hom ∧
        ∀ p : ℕ,
          isKProjectiveValue (extColumn.{v,max u w x t} (A := A) (C := C) P p) ∧
          QuasiIso ((extend.{v,v,max u v w x t} B (Bₚ p)).map c) ∧
          IsIso (Descent.PerfectHomBaseChange.comparison (Bₚ p) P X)

end Models

def CommonCotangentModels : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra A B] [Algebra A C] [IsScalarTower k A B]
    [Module.FaithfullyFlat A C]
    (T₀ : ModuleTensor.{u,v} k)
    (_hT₀ : ∀ {U V : CommDGAlgebra.{u,v} k} (f : U ⟶ V) (N : V.Module), T₀.Formulas f N)
    (M : Model (originalBaseMap (k := k) (A := A) (B := B))),
    ∃ (T : ModuleTensor.{u,max u v w x t} k) (U : LiftedModel.{u,v,max u w x t} T₀ T M)
      (E : RingBridge.{u,v,max u w x t} k B)
      (F : ∀ p : ℕ, RingBridge.{u,v,max u w x t} k (BP A B C p)),
      (∀ {R S : CommDGAlgebra.{u,max u v w x t} k} (f : R ⟶ S) (N : S.Module), T.Formulas f N) ∧
      (∀ h, E.Localizes h) ∧ (∀ p h, (F p).Localizes h) ∧
      TensorBridge.{u,v,max u w x t} E T ∧
      (∀ p, TensorBridge.{u,v,max u w x t} (F p) T) ∧
      Nonempty (CompatibleHomColumns (A := A) (C := C) E F) ∧
      ∃ D : CompatibleColumns (C := C) T U.model E F, D.Represents ∧ D.CoherentExtensions ∧ CompatibleColumns.OriginalInputs.{u,v,w,t,x} D

/-- The same restriction equivalence as URingLift, with the term level
allowed to exceed the level of either ring. -/
abbrev changeRepresentative {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (e : R ≃+* S) : compValue.{t} R ⥤ compValue.{t} S :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.mapHomologicalComplex (.up ℤ)


section OriginalRings

open CochainModels (internalHomValue)
open Descent.PerfectHomBaseChange (extendCochain)

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
variable {S : ℕ → Type w} {S' : ℕ → Type v}
variable [∀ p, CommRing (S p)] [∀ p, CommRing (S' p)]
variable [∀ p, Algebra R (S p)] [∀ p, Algebra R' (S' p)]

private abbrev homColumnMap {p q : ℕ} (f : S p →ₐ[R] S q)
    (P X : compValue.{t} R) :=
  letI : Algebra (S p) (S q) := f.toRingHom.toAlgebra
  letI : IsScalarTower R (S p) (S q) := IsScalarTower.of_algHom f
  changeHomCoefficients.{u,w,t} R (S p) (S q) P X

/-- An identification of the original-ring complexes with the ones computed
over representatives. The original localization and both Hom diagrams use
the same chain equivalences. -/
structure OriginalRingDiagramComparison
    (e : R ≃+* R') (eS : ∀ p, S p ≃+* S' p)
    (f : ∀ {p q : ℕ}, (Fin (p + 1) → Fin (q + 1)) → S p →ₐ[R] S q)
    (g : ∀ {p q : ℕ}, (Fin (p + 1) → Fin (q + 1)) → S' p →ₐ[R'] S' q) where
  d : derivedValue.{max u v w t} R ≌ derivedValue.{max u v w t} R'
  quotient : qValue R ⋙ d.functor ≅ changeRepresentative.{u,v,max u v w t} e ⋙ qValue R'
  originalModel (L' : compValue.{max u v w t} R') :
    ∃ (L : compValue.{max u v w t} R)
      (c : (changeRepresentative.{u,v,max u v w t} e).obj L ≅ L')
      (a : d.functor.obj ((qValue R).obj L) ≅ (qValue R').obj L'),
      a.hom = (quotient.app L).hom ≫ (qValue R').map c.hom
  extendIso (p : ℕ) :
    extend.{u,w,max u v w t} R (S p) ⋙ changeRepresentative.{w,v,max u v w t} (eS p) ≅
      changeRepresentative.{u,v,max u v w t} e ⋙ extend.{v,v,max u v w t} R' (S' p)
  extend_tmul (p : ℕ) (X : compValue.{max u v w t} R) (i : ℤ) (s : S p) (x : X.X i) :
    ((extendIso p).hom.app X).f i (s ⊗ₜ[R] x) =
      eS p s ⊗ₜ[R'] (show ((changeRepresentative.{u,v,max u v w t} e).obj X).X i from x)
  homIso (P X : compValue.{max u v w t} R) :
    (changeRepresentative.{u,v,max u v w t} e).obj (internalHomValue P X) ≅
      internalHomValue ((changeRepresentative.{u,v,max u v w t} e).obj P)
        ((changeRepresentative.{u,v,max u v w t} e).obj X)
  hom_evaluation (P X : compValue.{max u v w t} R) (n i j : ℤ) (h : i + n = j)
      (z : Cochain P X n) (x : P.X i) :
    (((homIso P X).hom.f n z).v i j h) x = z.v i j h x
  homColumnIso (p : ℕ) (P X : compValue.{max u v w t} R) :
    let E := extend.{u,w,max u v w t} R (S p)
    let E' := extend.{v,v,max u v w t} R' (S' p)
    let C := changeRepresentative.{u,v,max u v w t} e
    (changeRepresentative.{w,v,max u v w t} (eS p)).obj (internalHomValue (E.obj P) (E.obj X)) ≅
      internalHomValue (E'.obj (C.obj P)) (E'.obj (C.obj X))
  homColumn_evaluation (p : ℕ) (P X : compValue.{max u v w t} R) (n i j : ℤ) (h : i + n = j)
      (z : Cochain ((extend.{u,w,max u v w t} R (S p)).obj P)
        ((extend.{u,w,max u v w t} R (S p)).obj X) n)
      (x : ((extend.{u,w,max u v w t} R (S p)).obj P).X i) :
    (((homColumnIso p P X).hom.f n z).v i j h) (((extendIso p).hom.app P).f i x) =
      ((extendIso p).hom.app X).f j (z.v i j h x)
  augmentation (p : ℕ) (P X : compValue.{max u v w t} R) (n : ℤ) (z : Cochain P X n) :
    (homColumnIso p P X).hom.f n (extendCochain (S p) n z) =
      extendCochain (S' p) n ((homIso P X).hom.f n z)
  cofaces {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1)) (P X : compValue.{max u v w t} R)
      (n : ℤ) (z : Cochain ((extend.{u,w,max u v w t} R (S p)).obj P)
        ((extend.{u,w,max u v w t} R (S p)).obj X) n) :
    let F := changeRepresentative.{u,v,max u v w t} e
    (homColumnIso q P X).hom.f n ((homColumnMap.{u,w,max u v w t} (f a) P X).f n z) =
      (homColumnMap.{v,v,max u v w t} (g a) (F.obj P) (F.obj X)).f n
        ((homColumnIso p P X).hom.f n z)

end OriginalRings

/-- Rings starting at independent levels admit common representatives of
the whole original Amitsur diagram, including all units and factor maps. -/
def RingDiagramTransport : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (A : Type v) (B : Type x) (C : Type y) [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A B] [Algebra A C]
    [IsScalarTower k A B] [IsScalarTower k A C] [Module.FaithfullyFlat A C],
    ∃ (A' B' C' : CommAlgCat.{max u v x y} k)
      (eA : A ≃ₐ[k] A') (eB : B ≃ₐ[k] B') (eC : C ≃ₐ[k] C')
      (f : A' →ₐ[k] B') (g : A' →ₐ[k] C'),
      (∀ a : A, f (eA a) = eB (algebraMap A B a)) ∧
      (∀ a : A, g (eA a) = eC (algebraMap A C a)) ∧
      letI : Algebra A' B' := f.toRingHom.toAlgebra
      letI : Algebra A' C' := g.toRingHom.toAlgebra
      letI : IsScalarTower k A' B' := IsScalarTower.of_algHom f
      letI : IsScalarTower k A' C' := IsScalarTower.of_algHom g
      Module.FaithfullyFlat A' C' ∧
      ∃ (eCP : ∀ p : ℕ, CP A C p ≃ₐ[k] CP A' C' p)
        (eBP : ∀ p : ℕ, BP A B C p ≃ₐ[k] BP A' B' C' p),
        (∀ (p : ℕ) (i : Fin (p + 1)) (c : C),
          eCP p (AmitsurAlgebrasSpec.factor A C i c) = AmitsurAlgebrasSpec.factor A' C' i (eC c)) ∧
        (∀ (p : ℕ) (b : B) (z : CP A C p), eBP p (b ⊗ₜ[A] z) = eB b ⊗ₜ[A'] eCP p z) ∧
        (∀ (p : ℕ) (b : B), eBP p (baseMap p b) = baseMap p (eB b)) ∧
        (∀ {p q : ℕ} (d : Fin (p + 1) → Fin (q + 1))
          (z : CP A C p) (b : BP A B C p),
          eCP q (AmitsurAlgebrasSpec.map d z) = AmitsurAlgebrasSpec.map d (eCP p z) ∧
          eBP q (columnMap (A := A) (B := B) (C := C) d b) =
            columnMap (A := A') (B := B') (C := C') d (eBP p b)) ∧
        Nonempty (OriginalRingDiagramComparison.{x,max u v x y,max v x y,t}
          eB.toRingEquiv (fun p => (eBP p).toRingEquiv)
          (fun d => columnMap (A := A) (B := B) (C := C) d)
          (fun d => columnMap (A := A') (B := B') (C := C') d))

section OriginalCotangent

open CochainModels (isKProjectiveValue)

/-- Combine the original-ring equivalence with the same representative used
in the flat dg diagram, including the scalar extensions of that representative. -/
def OriginalCotangentComparison : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra A B] [Algebra A C] [IsScalarTower k A B]
    {R : Type y} [CommRing R] {S : ℕ → Type w}
    [∀ p, CommRing (S p)] [∀ p, Algebra R (S p)]
    (e : R ≃+* B) (eS : ∀ p, S p ≃+* BP A B C p)
    (f : ∀ {p q : ℕ}, (Fin (p + 1) → Fin (q + 1)) → S p →ₐ[R] S q)
    (O : OriginalRingDiagramComparison.{y,v,w,t} e eS f
      (fun d => columnMap (A := A) (B := B) (C := C) d))
    (T : ModuleTensor.{u,max v w y t} k)
    (M : Model (liftedBaseMap.{u,v,max w y t} (k := k) (A := A) (B := B)))
    (E : RingBridge.{u,v,max w y t} k B) (F : ∀ p, RingBridge.{u,v,max w y t} k (BP A B C p))
    (D : CompatibleColumns T M E F)
    (h : HomotopyCategoryLaws (oneObject (transported.{u,v,max w y t} k B))),
    let G := oneObject (transported.{u,v,max w y t} k B)
    letI := DG.Derived.homotopyCategory G h
    letI := DG.DerivedKProjective.derivedCategoryInstance G h
    let Q := DG.AmbientDerived.quotient.{u,v,0,max w y t} (oneObject (ordinary k B)) h
    ∃ (L : compValue.{max v w y t} R)
      (c : (changeRepresentative.{y,v,max v w y t} e).obj L ≅ D.L)
      (H : homotopyValue.{max v w y t} B ≌ transportHomotopy.{u,v,max w y t} k B)
      (I : derivedValue.{max v w y t} B ≌ transportDerived.{u,v,max w y t} k B h)
      (a : ∀ X : compValue.{max v w y t} B,
        H.functor.obj ((quotientValue B).obj X) ≅
          (E.strict.functor.obj X : transportHomotopy.{u,v,max w y t} k B))
      (τ : qhValue B ⋙ I.functor ≅ H.functor ⋙ Q)
      (l : (O.d.trans I).functor.obj ((qValue R).obj L) ≅ Q.obj (M.module T)),
      (∀ {X Y : compValue.{max v w y t} B} (m : X ⟶ Y),
        H.functor.map ((quotientValue B).map m) ≫ (a Y).hom =
          (a X).hom ≫ homotopyClass (E.strict.functor.map m)) ∧
      l.hom = I.functor.map ((O.quotient.app L).hom ≫ (qValue B).map c.hom) ≫
        (τ.app ((quotientValue B).obj D.L)).hom ≫ Q.map (a D.L).hom ≫
        Q.map (homotopyClass D.global.hom) ∧
      (∀ p : ℕ,
        let Gp := extend.{v,v,max v w y t} B (BP A B C p)
        let X := (changeRepresentative.{w,v,max v w y t} (eS p)).obj
          ((extend.{y,w,max v w y t} R (S p)).obj L)
        ∃ iso : (F p).strict.functor.obj X ≅ (D.column p).model.module T,
          iso.hom = (F p).strict.functor.map ((O.extendIso p).hom.app L ≫ Gp.map c.hom) ≫
            (D.identification p).hom) ∧
      ∀ (P : compValue.{max v w y t} R), FiniteProjective P →
        ∀ α : (qValue R).obj P ≅ (qValue R).obj L,
          ∃ g : P ⟶ L, isKProjectiveValue P ∧ QuasiIso g ∧ (qValue R).map g = α.hom

end OriginalCotangent

/-- The change of ring representatives keeps the original ordinary scalar
extension at a common term level, on all of its pure tensors. -/
def ExtensionOfRepresentatives : Prop :=
  ∀ (R : Type v) (S : Type w) (R' S' : Type x)
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R' S']
    (eR : R ≃+* R') (eS : S ≃+* S'),
    (∀ r : R, eS (algebraMap R S r) = algebraMap R' S' (eR r)) →
    let FR := changeRepresentative.{v,x,max v w x t} eR
    let FS := changeRepresentative.{w,x,max v w x t} eS
    ∃ a : extend.{v,w,max v w x t} R S ⋙ FS ≅ FR ⋙ extend.{x,x,max v w x t} R' S',
      ∀ (P : compValue.{max v w x t} R) (i : ℤ) (s : S) (z : P.X i),
        (a.hom.app P).f i (s ⊗ₜ[R] z) = eS s ⊗ₜ[R'] (show (FR.obj P).X i from z)

end
end Specs.DerivedFormalization.Affine.CotangentAmitsurModels
