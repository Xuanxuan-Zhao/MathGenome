import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurAlgebras
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Specs.DerivedFormalization.Affine.FlatCotangentAmitsurDiagram

open _root_.DerivedFormalization.Affine
open CotangentComplex (Model cdgaLift liftCDGA)
open CotangentBaseChange (IsAssociator IsSymbolMap extend symbolTensor)
open Tensor (ModuleTensor regular restrict restrictFunctor term)

noncomputable section

universe u v t

abbrev power (A C : Type v) [CommRing A] [CommRing C] [Algebra A C] (p : ℕ) :=
  AmitsurAlgebrasSpec.degree A C p

abbrev target (A B C : Type v) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (p : ℕ) :=
  B ⊗[A] power A C p

abbrev transported (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R] :=
  liftCDGA.{u,v,t} (NonpositiveCDGA.ordinary (CommAlgCat.of k R))

abbrev transportedMap {k : Type u} [Field k] [CharZero k]
    {R S : Type v} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f : R →ₐ[k] S) : transported.{u,v,t} k R ⟶ transported.{u,v,t} k S :=
  (cdgaLift.{u,v,t} k).map (NonpositiveCDGA.ordinaryMap (CommAlgCat.ofHom f))

variable {k : Type u} [Field k] [CharZero k]
variable {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A B] [Algebra A C]
variable [IsScalarTower k A B] [IsScalarTower k A C]

abbrev globalBase :
    transported.{u,v,t} k A ⟶ transported.{u,v,t} k B :=
  transportedMap (IsScalarTower.toAlgHom k A B)

abbrev powerLeg (p : ℕ) :
    transported.{u,v,t} k A ⟶ transported.{u,v,t} k (power A C p) :=
  transportedMap (IsScalarTower.toAlgHom k A _)

abbrev targetLeg (p : ℕ) :
    transported.{u,v,t} k B ⟶ transported.{u,v,t} k (target A B C p) :=
  transportedMap
    ((Algebra.TensorProduct.includeLeft : B →ₐ[B] target A B C p).restrictScalars k)

abbrev localBase (p : ℕ) :
    transported.{u,v,t} k (power A C p) ⟶ transported.{u,v,t} k (target A B C p) :=
  transportedMap
    ((Algebra.TensorProduct.includeRight : power A C p →ₐ[A] target A B C p).restrictScalars k)

abbrev powerMap {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) :
    transported.{u,v,t} k (power A C p) ⟶ transported.{u,v,t} k (power A C q) :=
  transportedMap
    ((AmitsurAlgebrasSpec.map f : power A C p →ₐ[A] power A C q).restrictScalars k)

abbrev targetMap {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) :
    transported.{u,v,t} k (target A B C p) ⟶ transported.{u,v,t} k (target A B C q) :=
  transportedMap
    ((Algebra.TensorProduct.map (AlgHom.id B B) (AmitsurAlgebrasSpec.map f) :
      target A B C p →ₐ[B] target A B C q).restrictScalars k)

set_option autoImplicit false

set_option quotPrecheck false in
set_option hygiene false in
local notation "globalLeg" => globalBase.{u,v,t} (k := k) (A := A) (B := B)

set_option quotPrecheck false in
set_option hygiene false in
local notation "toPower" => powerLeg.{u,v,t} (k := k) (A := A) (C := C)

set_option quotPrecheck false in
set_option hygiene false in
local notation "toTarget" => targetLeg.{u,v,t} (k := k) (A := A) (B := B) (C := C)

set_option quotPrecheck false in
set_option hygiene false in
local notation "localLeg" => localBase.{u,v,t} (k := k) (A := A) (B := B) (C := C)

set_option quotPrecheck false in
set_option hygiene false in
local notation "powerFactor" => powerMap.{u,v,t} (k := k) (A := A) (C := C)

set_option quotPrecheck false in
set_option hygiene false in
local notation "targetFactor" => targetMap.{u,v,t} (k := k) (A := A) (B := B) (C := C)

set_option maxHeartbeats 600000

variable (T : ModuleTensor.{u,max v t} k) (M : Model globalLeg)

/-- The pushed-out resolution of the prescribed ordinary tensor ring, its
strict cotangent comparison, and the normalization of the two extensions. -/
structure Column (p : ℕ) where
  model : Model (localLeg p)
  resolutionMap : M.algebra ⟶ model.algebra
  resolutionPushout : IsPushout M.base (toPower p) resolutionMap model.base
  ordinaryPushout : IsPushout globalLeg (toPower p) (toTarget p) (localLeg p)
  augmentation_comm : resolutionMap ≫ model.augmentation = M.augmentation ≫ (toTarget p)
  comparison : (extend T (toTarget p)).obj (M.module T) ≅ model.module T
  symbols (i h l m n : ℤ) (hm : i + h = m) (hn : m + l = n)
      (x : M.algebra.complex.X i) (y : (transported.{u,v,t} k B).complex.X h)
      (z : (transported.{u,v,t} k (target A B C p)).complex.X l) :
    (comparison.hom.app ()).f n
      (T.tmul ((toTarget p) : _ ⟶ (transported.{u,v,t} k (target A B C p)).toCommDGAlgebra)
        (N := regular (transported.{u,v,t} k (target A B C p)).toCommDGAlgebra)
        m l n hn (symbolTensor T M.differentials M.augmentation i h m hm x y) z) =
    symbolTensor T model.differentials model.augmentation i (h + l) n (by omega)
      (resolutionMap.chainMap.f i x)
      ((transported.{u,v,t} k (target A B C p)).mul h l (h + l) rfl ((toTarget p).chainMap.f h y) z)
  associator : (extend T (toTarget p)).obj (M.module T) ≅
    (extend T (M.augmentation ≫ (toTarget p))).obj M.differentials.module
  onAssociator : IsAssociator T M.augmentation (toTarget p) M.differentials.module associator

variable {T M} {p q : ℕ}

/-- A map of columns extends the identity of the original resolution. On
the cotangent modules it sends each differential and scalar to its image. -/
structure ColumnMap (X : Column (C := C) T M p) (Y : Column (C := C) T M q)
    (f : Fin (p + 1) → Fin (q + 1)) where
  algebraMap : X.model.algebra ⟶ Y.model.algebra
  fromResolution : X.resolutionMap ≫ algebraMap = Y.resolutionMap
  fromBase : X.model.base ≫ algebraMap = (powerFactor f) ≫ Y.model.base
  overTarget : X.model.augmentation ≫ (targetFactor f) = algebraMap ≫ Y.model.augmentation
  cotangentMap : X.model.module T ⟶
    restrict ((targetFactor f) : _ ⟶ (transported.{u,v,t} k (target A B C q)).toCommDGAlgebra) (Y.model.module T)
  symbols : IsSymbolMap T X.model.differentials Y.model.differentials
    X.model.augmentation Y.model.augmentation algebraMap (targetFactor f) cotangentMap
  normalizedMap : (extend T (M.augmentation ≫ (toTarget p))).obj M.differentials.module ⟶
    restrict ((targetFactor f) : _ ⟶ (transported.{u,v,t} k (target A B C q)).toCommDGAlgebra)
      ((extend T (M.augmentation ≫ (toTarget q))).obj M.differentials.module)
  normalizedSymbols : IsSymbolMap T M.differentials M.differentials
    (M.augmentation ≫ (toTarget p)) (M.augmentation ≫ (toTarget q)) (𝟙 M.algebra) (targetFactor f) normalizedMap
  naturality :
    X.associator.hom ≫ normalizedMap ≫
      (restrictFunctor ((targetFactor f) : _ ⟶ (transported.{u,v,t} k (target A B C q)).toCommDGAlgebra)).map
        (Y.associator.inv ≫ Y.comparison.hom) = X.comparison.hom ≫ cotangentMap

/-- The scalar map on extensions of the original cotangent module, expressed
using the normalized extension and then the inverse normalization. -/
abbrev ColumnMap.extensionMap {X : Column (C := C) T M p} {Y : Column (C := C) T M q}
    {f : Fin (p + 1) → Fin (q + 1)} (F : ColumnMap X Y f) :
    (extend T (toTarget p)).obj (M.module T) ⟶
      restrict ((targetFactor f) : _ ⟶ (transported.{u,v,t} k (target A B C q)).toCommDGAlgebra)
        ((extend T (toTarget q)).obj (M.module T)) :=
  X.associator.hom ≫ F.normalizedMap ≫
    (restrictFunctor ((targetFactor f) : _ ⟶ (transported.{u,v,t} k (target A B C q)).toCommDGAlgebra)).map
      Y.associator.inv

variable (T : ModuleTensor.{u,max v t} k) (M : Model globalLeg)

/-- All columns and factor maps are chosen at once. The equations on
components are strict equalities of the underlying chain maps of the
semilinear maps. The scalar map on the left is the ordinary scalar change
on the right coefficient of every pure tensor. -/
structure Diagram where
  flatPower (p : ℕ) : Module.Flat A (power A C p)
  column (p : ℕ) : Column (C := C) T M p
  map {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) : ColumnMap (column p) (column q) f
  resolutionId (p : ℕ) : (map (id : Fin (p + 1) → Fin (p + 1))).algebraMap = 𝟙 _
  resolutionComp {p q r : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (g : Fin (q + 1) → Fin (r + 1)) :
    (map (g ∘ f)).algebraMap = (map f).algebraMap ≫ (map g).algebraMap
  cotangentId (p : ℕ) (i : ℤ) (x : term ((column p).model.module T) i) :
    ((map (id : Fin (p + 1) → Fin (p + 1))).cotangentMap.app ()).f i x = x
  cotangentComp {p q r : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (g : Fin (q + 1) → Fin (r + 1))
      (i : ℤ) (x : term ((column p).model.module T) i) :
    ((map (g ∘ f)).cotangentMap.app ()).f i x =
      ((map g).cotangentMap.app ()).f i (((map f).cotangentMap.app ()).f i x)
  extensionPures {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1))
      (i h n : ℤ) (hn : i + h = n) (x : term (M.module T) i)
      (z : (transported.{u,v,t} k (target A B C p)).complex.X h) :
    ((map f).extensionMap.app ()).f n
      (T.tmul ((toTarget p) : _ ⟶ (transported.{u,v,t} k (target A B C p)).toCommDGAlgebra)
        (N := regular (transported.{u,v,t} k (target A B C p)).toCommDGAlgebra) i h n hn x z) =
      T.tmul ((toTarget q) : _ ⟶ (transported.{u,v,t} k (target A B C q)).toCommDGAlgebra)
        (N := regular (transported.{u,v,t} k (target A B C q)).toCommDGAlgebra)
        i h n hn x ((targetFactor f).chainMap.f h z)

/-- This applies to the model supplied by LiftedModel.model from A08,
as well as to any strict model at the same bound. The tensor hypotheses
are the signed tensor formulas supplied by ATensor. -/
def FlatCotangentDiagram : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A B] [Algebra A C]
    [IsScalarTower k A B] [IsScalarTower k A C] [Module.FaithfullyFlat A C]
    (T : ModuleTensor.{u,max v t} k),
    (∀ {P Q : CommDGAlgebra.{u,max v t} k} (f : P ⟶ Q) (N : Q.Module), T.Formulas f N) →
    ∀ (M : Model globalLeg),
      Nonempty (Diagram (C := C) T M)

end

end Specs.DerivedFormalization.Affine.FlatCotangentAmitsurDiagram
