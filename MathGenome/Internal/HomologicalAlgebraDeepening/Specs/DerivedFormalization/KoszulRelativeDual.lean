import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedCoinduction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.KoszulCochainResolution
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainCoefficientLift
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
import Mathlib.RingTheory.Ideal.Cotangent

/-! The relative dual of a quotient by a regular sequence. -/

noncomputable section

namespace Specs.DerivedFormalization.KoszulRelativeDual

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open CochainComplex.HomComplex
open Cochains (compValue derivedValue qValue stalkValue derivedStalkValue
  derivedCohomologyValue cohomologyFactorsValue shiftValue)
open CochainModels (internalHomValue internalHomMapValue isKInjectiveValue)
open CoinductionComplex (coinduceValue)
open DerivedRestriction (restrictScalarsValue restrictScalarsComplexValue
  restrictScalarsCohomologyIsoValue)
open KoszulCochainResolution (cochainValue termIsoValue augmentationValue)
open _root_.AdvCommAlg.Koszul
open scoped TensorProduct

universe u v
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]
variable (J : Ideal A)

abbrev QuotientRing := A ⧸ J

/-- The ordinary dual of the determinant of the actual conormal module. -/
abbrev determinantDual (c : ℕ) :=
  Module.Dual (QuotientRing J) (⋀[QuotientRing J]^c J.Cotangent)

def generator (a : List A) (h : listIdeal a = J) (i : Fin a.length) : J.Cotangent :=
  J.toCotangent ⟨a.get i, h ▸ Ideal.subset_span (List.get_mem a i)⟩

/-- The quotient-basis map that sends the ith vector to the class of aᵢ. -/
def conormalMap (a : List A) (h : listIdeal a = J) :
    (Fin a.length → QuotientRing J) →ₗ[QuotientRing J] J.Cotangent :=
  (Pi.basisFun (QuotientRing J) (Fin a.length)).constr (QuotientRing J) (generator J a h)

/-- Reduction of a free Koszul vector to the conormal module. -/
def reduceVector (a : List A) (h : listIdeal a = J) :
    (Fin a.length → A) →ₗ[A] J.Cotangent :=
  J.toCotangent.comp ((listForm a).codRestrict J fun x => h ▸ listForm_mem a x)

/-- Reduction on exterior products, using the A-module underlying the
exterior power over A/J. -/
def reduceWedge (a : List A) (h : listIdeal a = J) (c : ℕ) :
    (⋀[A]^c (Fin a.length → A)) →ₗ[A] (⋀[QuotientRing J]^c J.Cotangent) :=
  exteriorPower.alternatingMapLinearEquiv
    (({ toMultilinearMap :=
          (exteriorPower.ιMulti (QuotientRing J) c (M := J.Cotangent)).toMultilinearMap.restrictScalars A
        map_eq_zero_of_eq' := fun x _i _j hij hne =>
          (exteriorPower.ιMulti (QuotientRing J) c (M := J.Cotangent)).map_eq_zero_of_eq x hij hne
      } : J.Cotangent [⋀^Fin c]→ₗ[A] (⋀[QuotientRing J]^c J.Cotangent)).compLinearMap
        (reduceVector J a h))

def conormalBasisType : Prop :=
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (a : List A) (h : listIdeal a = J), RingTheory.Sequence.IsRegular A a →
    Function.Bijective (conormalMap J a h)

abbrev freeDeterminant (a : List A) := ⋀[A]^a.length (Fin a.length → A)

/-- The cochain complex K[-c] with each term tensored with the ordinary dual
of the free determinant line. Its differential is (-1)^c d_K. -/
def shiftedKoszul (a : List A) : compValue.{u} A :=
  ((tensorRight (ModuleCat.of A (Module.Dual A (freeDeterminant a)))).mapHomologicalComplex
    (.up ℤ)).obj ((shiftValue A (-(a.length : ℤ))).obj (cochainValue a))

def wedgeIntoShift (a : List A) (p q : ℕ) (h : p + q = a.length)
    (z : ⋀[A]^p (Fin a.length → A)) (φ : Module.Dual A (freeDeterminant a)) :
    (shiftedKoszul a).X (q : ℤ) :=
  have he : (q : ℤ) + -(a.length : ℤ) = -(p : ℤ) := by omega
  ((eqToIso (congrArg (cochainValue a).X he)).inv ((termIsoValue a p).inv z)) ⊗ₜ[A] φ

def topWedge (a : List A) (p q : ℕ) (h : p + q = a.length)
    (z : ⋀[A]^p (Fin a.length → A)) (x : ⋀[A]^q (Fin a.length → A)) :
    freeDeterminant a :=
  (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[A]^n (Fin a.length → A)) h))
    (exteriorPower.wedge A _ p q z x)

/-- The exterior pairing sends z ⊗ φ to x ↦ φ(z ∧ x) and is a chain
isomorphism with the stated signed shift. -/
def signedPairingType : Prop :=
  ∀ {A : Type u} [CommRing A] (a : List A),
    ∃ e : shiftedKoszul a ≅ internalHomValue (cochainValue a)
          ((stalkValue A).obj (ModuleCat.of A A)),
      ∀ (p q : ℕ) (h : p + q = a.length)
        (z : ⋀[A]^p (Fin a.length → A)) (x : ⋀[A]^q (Fin a.length → A))
        (φ : Module.Dual A (freeDeterminant a)),
        (singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).hom
          ((e.hom.f (q : ℤ) (wedgeIntoShift a p q h z φ)).v (-(q : ℤ)) 0
            (neg_add_cancel (q : ℤ)) ((termIsoValue a q).inv x)) =
          φ (topWedge a p q h z x)

/-- A lift of a generator change preserves the contraction form. Every such
lift acts on the complexes by its exterior powers and respects reduction to
the intrinsic conormal module. -/
def generatorChangeType : Prop :=
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (a b : List A) (ha : listIdeal a = J) (hb : listIdeal b = J),
    RingTheory.Sequence.IsRegular A a → RingTheory.Sequence.IsRegular A b →
    a.length = b.length ∧
    (∃ m : (Fin b.length → A) →ₗ[A] (Fin a.length → A), (listForm a).comp m = listForm b) ∧
    ∀ (m : (Fin b.length → A) →ₗ[A] (Fin a.length → A)),
      (listForm a).comp m = listForm b →
      ∃ k : cochainValue b ⟶ cochainValue a,
        k ≫ augmentationValue a ≫ (stalkValue A).map
          ((Submodule.quotEquivOfEq (listIdeal a) J ha).toModuleIso.hom) =
            augmentationValue b ≫ (stalkValue A).map
              ((Submodule.quotEquivOfEq (listIdeal b) J hb).toModuleIso.hom) ∧
        (∀ n : ℕ, (termIsoValue b n).inv ≫ k.f (-(n : ℤ)) ≫ (termIsoValue a n).hom =
            ModuleCat.ofHom (exteriorPower.map n m)) ∧
        ∀ n : ℕ, (reduceWedge J a ha n).comp (exteriorPower.map n m) = reduceWedge J b hb n

/-- Multiplication by an element of the defining ideal is null-homotopic
on the Koszul complex. -/
def idealMultiplicationType : Prop :=
  ∀ {A : Type u} [CommRing A] (a : List A) (r : A), r ∈ listIdeal a →
    Nonempty (Homotopy (r • 𝟙 (cochainValue a)) 0)

abbrev liftedKoszul (a : List A) : compValue.{max u v} A :=
  (CochainCoefficientLift.lift.{v, u} A).obj (cochainValue a)

def liftedWedge (a : List A) (n : ℕ) (x : ⋀[A]^n (Fin a.length → A)) :
    (liftedKoszul.{u, v} a).X (-(n : ℤ)) :=
  CochainCoefficientLift.termEquiv.{v} (cochainValue a) _ ((termIsoValue a n).inv x)

abbrev scalarStalk : compValue.{max u v} A :=
  (stalkValue A).obj (ModuleCat.of A (ULift.{v} A))

abbrev coinduced (I : compValue.{max u v} A) : compValue.{max u v} (QuotientRing J) :=
  (coinduceValue.{v} (Ideal.Quotient.mk J)).obj I

abbrev dualKoszul (a : List A) : compValue.{max u v} A :=
  internalHomValue (liftedKoszul.{u, v} a) (scalarStalk.{u, v} (A := A))

/-- The value of the quotient augmentation in degree zero, in the shared
exterior-power coordinates. -/
def augmentationAtZero (a : List A)
    (x : (liftedKoszul.{u, v} a).X 0) : QuotientRing J :=
  Ideal.Quotient.mk J <| exteriorPower.zeroEquiv A (Fin a.length → A)
    ((termIsoValue a 0).hom ((CochainCoefficientLift.termEquiv.{v} (cochainValue a) 0).symm x))

/-- The comparison through Hom_A(K,I). The map from coinduction is
precomposition by the quotient augmentation. The map from the Koszul dual
is postcomposition by the replacement. -/
structure ModelComparison (a : List A) (h : listIdeal a = J)
    {I : compValue.{max u v} A} (i : scalarStalk.{u, v} (A := A) ⟶ I) where
  pre : (restrictScalarsComplexValue (Ideal.Quotient.mk J)).obj (coinduced J I) ⟶
    internalHomValue (liftedKoszul.{u, v} a) I
  pre_quasiIso : QuasiIso pre
  post_quasiIso : QuasiIso (internalHomMapValue (𝟙 (liftedKoszul.{u, v} a)) i)
  pre_at_zero : ∀ (n : ℤ) (z : (coinduced J I).X n) (x : (liftedKoszul.{u, v} a).X 0),
    (pre.f n z).v 0 n (zero_add n) x =
      (ModuleCat.CoextendScalars.equiv (Ideal.Quotient.mk J) (I.X n) z)
        (augmentationAtZero J a x)
  pre_away_zero : ∀ (n j k : ℤ) (e : j + n = k) (_hj : j ≠ 0)
      (z : (coinduced J I).X n),
    (pre.f n z).v j k e = 0
  scalar_lift : ∀ (n : ℤ) (r : A) (z : (coinduced J I).X n)
      (j k : ℤ) (e : j + n = k),
    (pre.f n (Ideal.Quotient.mk J r • z)).v j k e =
      (r • 𝟙 ((liftedKoszul.{u, v} a).X j)) ≫ (pre.f n z).v j k e

def modelComparisonType : Prop :=
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (a : List A) (h : listIdeal a = J), RingTheory.Sequence.IsRegular A a →
    ∀ (I : compValue.{max u v} A) (i : scalarStalk.{u, v} (A := A) ⟶ I),
      QuasiIso i → isKInjectiveValue I → Nonempty (ModelComparison J a h i)

/-- The canonical comparison of underlying A-cohomology modules, from the
Koszul dual to coinduction. -/
def modelHomologyIso {a : List A} {h : listIdeal a = J}
    {I : compValue.{max u v} A} {i : scalarStalk.{u, v} (A := A) ⟶ I}
    (C : ModelComparison J a h i) (n : ℤ) :
    (dualKoszul.{u, v} a).homology n ≅
      (restrictScalarsValue (Ideal.Quotient.mk J)).obj ((coinduced J I).homology n) :=
  letI := C.pre_quasiIso
  letI := C.post_quasiIso
  asIso (homologyMap (internalHomMapValue (𝟙 (liftedKoszul.{u, v} a)) i) n) ≪≫
    (asIso (homologyMap C.pre n)).symm ≪≫
    (restrictScalarsCohomologyIsoValue (Ideal.Quotient.mk J) n).app (coinduced J I)

/-- In top degree, evaluate a Koszul cocycle on a determinant vector and
reduce the resulting scalar modulo the defining ideal. -/
def TopIdentification {a : List A} {h : listIdeal a = J}
    {I : compValue.{max u v} A} {i : scalarStalk.{u, v} (A := A) ⟶ I}
    (C : ModelComparison J a h i)
    (e : (coinduced J I).homology (a.length : ℤ) ≅
      ModuleCat.of (QuotientRing J) (ULift.{v} (determinantDual J a.length))) : Prop :=
  ∀ (z : (dualKoszul.{u, v} a).cycles (a.length : ℤ))
    (x : freeDeterminant a),
    (e.hom ((modelHomologyIso J C (a.length : ℤ)).hom
      ((dualKoszul.{u, v} a).homologyπ _ z))).down (reduceWedge J a h _ x) =
      Ideal.Quotient.mk J
        (((singleObjXSelf (.up ℤ) 0 (ModuleCat.of A (ULift.{v} A))).hom
          ((((dualKoszul.{u, v} a).iCycles _ z).v (-(a.length : ℤ)) 0
            (neg_add_cancel (a.length : ℤ))) (liftedWedge.{u, v} a a.length x))).down)

def coinducedCohomologyType : Prop :=
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (a : List A) (_h : listIdeal a = J), RingTheory.Sequence.IsRegular A a →
    ∀ (I : compValue.{max u v} A) (i : scalarStalk.{u, v} (A := A) ⟶ I),
      QuasiIso i → isKInjectiveValue I →
      (∀ n : ℤ, n ≠ (a.length : ℤ) → IsZero ((coinduced J I).homology n)) ∧
      ∃! e : (coinduced J I).homology (a.length : ℤ) ≅
          ModuleCat.of (QuotientRing J) (ULift.{v} (determinantDual J a.length)),
        ∀ (b : List A) (hb : listIdeal b = J) (hlen : b.length = a.length),
          RingTheory.Sequence.IsRegular A b →
          ∀ C : ModelComparison J b hb i, TopIdentification J C (hlen ▸ e)

/-- The relative dual in the same derived category as the coinduction
adjunction, evaluated on the regular A-module in degree zero. -/
abbrev relativeDual (G : DerivedCoinduction.Coinduction.{max u v} (Ideal.Quotient.mk J)) :
    derivedValue.{max u v} (QuotientRing J) :=
  G.functor.obj ((derivedStalkValue A).obj (ModuleCat.of A (ULift.{v} A)))

abbrev determinantModule (c : ℕ) : ModuleCat.{max u v} (QuotientRing J) :=
  ModuleCat.of (QuotientRing J) (ULift.{v} (determinantDual J c))

/-- A module placed in degree c is the degree-zero stalk shifted by -c. -/
def singleShift (c : ℕ) :
    DerivedCategory.singleFunctor (ModuleCat.{max u v} (QuotientRing J)) (c : ℤ) ≅
    derivedStalkValue.{max u v} (QuotientRing J) ⋙
      CategoryTheory.shiftFunctor (derivedValue.{max u v} (QuotientRing J)) (-(c : ℤ)) :=
  ((DerivedCategory.singleFunctors (ModuleCat.{max u v} (QuotientRing J))).shiftIso
    (-(c : ℤ)) (c : ℤ) 0 (by omega)).symm

/-- Identification after truncation in degree c. The isomorphism induces
the canonical evaluation pairing on cohomology in every coinduction model. -/
def relativeDualType : Prop :=
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (G : DerivedCoinduction.Coinduction.{max u v} (Ideal.Quotient.mk J))
    (a : List A) (_h : listIdeal a = J), RingTheory.Sequence.IsRegular A a →
    (∀ n : ℤ, n ≠ (a.length : ℤ) →
      IsZero ((derivedCohomologyValue (QuotientRing J) n).obj (relativeDual J G))) ∧
    ∃! e : relativeDual J G ≅
        ((derivedStalkValue.{max u v} (QuotientRing J)).obj
          (determinantModule.{u, v} J a.length))⟦-(a.length : ℤ)⟧,
      ∀ (b : List A) (hb : listIdeal b = J) (hlen : b.length = a.length),
        RingTheory.Sequence.IsRegular A b →
      ∀ (I : compValue.{max u v} A) (i : scalarStalk.{u, v} (A := A) ⟶ I)
        (hi : QuasiIso i) (hI : isKInjectiveValue I)
        (C : ModelComparison J b hb i),
        let c : ℤ := a.length
        let M := determinantModule.{u, v} J a.length
        let H := derivedCohomologyValue (QuotientRing J) c
        let ei := @asIso _ _ _ _ ((qValue A).map i)
          ((DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} A) i).2 hi)
        let eI : relativeDual J G ≅ (qValue (QuotientRing J)).obj (coinduced J I) :=
          G.modelIso (Ideal.Quotient.mk J) I ei hI
        let eTop := ((cohomologyFactorsValue (QuotientRing J) c).app (coinduced J I)).symm ≪≫
          (H.mapIso eI).symm ≪≫ H.mapIso (e ≪≫ ((singleShift J a.length).app M).symm) ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso
            (ModuleCat.{max u v} (QuotientRing J)) c).app M
        TopIdentification J C (hlen ▸ eTop)

end Specs.DerivedFormalization.KoszulRelativeDual
