import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedHomComparisonMaps
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.PerfectDuals

/-! The perfect-source case of the canonical derived Hom base-change comparison. -/

namespace Specs.DerivedFormalization.PerfectHomBaseChange

open CategoryTheory
open Cochains (derivedValue)
open CochainTensorTransport (AdequateModel)
open DerivedHomAdjunction (Closed)
open DerivedHomModels (Models)
open DerivedScalarExtension (Extension MonoidalExtension)
open ScalarExtensionTransport (MonoidalChange)
open PerfectComplex (isPerfectValue)
open DerivedHomComparisonMaps (baseChangeValue)

universe u w a v t

attribute [local instance] HasDerivedCategory.standard

/-- For any ring map, the comparison defined by the derived evaluation
counits is an isomorphism for a perfect first argument. -/
def BaseChangeIso : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    {A B : Type a} [CommRing A] [CommRing B] {e : R ≃+* A} {d : S ≃+* B}
    {MR : AdequateModel e} {MS : AdequateModel d}
    {TR : DerivedTensor.Model MR} {TS : DerivedTensor.Model MS}
    {HR : Models.{u,a} R} {HS : Models.{w,a} S}
    {f : R →+* S} {F : MonoidalChange e d f MR MS} {L : Extension d f}
    (cR : Closed TR HR) (cS : Closed TS HS)
    (m : MonoidalExtension TR.toDescent TS.toDescent F L)
    (P Y : derivedValue.{a} R), isPerfectValue P → IsIso (baseChangeValue cR cS m P Y)

/-- The same comparison on the exact coefficient lifts of independently sized
original inputs, in one adequate derived category over each original ring. -/
def LiftedBaseChangeIso : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    {A B : Type (max u w a v t)} [CommRing A] [CommRing B] {e : R ≃+* A} {d : S ≃+* B}
    {MR : AdequateModel e} {MS : AdequateModel d}
    {TR : DerivedTensor.Model MR} {TS : DerivedTensor.Model MS}
    {HR : Models.{u,max u w a v t} R} {HS : Models.{w,max u w a v t} S}
    {f : R →+* S} {F : MonoidalChange e d f MR MS} {L : Extension d f}
    (cR : Closed TR HR) (cS : Closed TS HS)
    (m : MonoidalExtension TR.toDescent TS.toDescent F L)
    (P : derivedValue.{v} R) (Y : derivedValue.{t} R), isPerfectValue P →
    IsIso (baseChangeValue cR cS m
      ((CochainCoefficientLift.liftD.{max u w a t,v} R).obj P)
      ((CochainCoefficientLift.liftD.{max u w a v,t} R).obj Y))

end Specs.DerivedFormalization.PerfectHomBaseChange
