import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedHomAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedScalarExtension

/-! Evaluation and the canonical derived Hom comparisons of U11 and U13. -/

namespace Specs.DerivedFormalization.DerivedHomComparisonMaps

open CategoryTheory MonoidalCategory Opposite
open Cochains (derivedValue)
open CochainTensorTransport (AdequateModel)
open DerivedHomAdjunction (Closed)
open DerivedHomModels (Models rHomValue)
open DerivedScalarExtension (Extension MonoidalExtension)
open ScalarExtensionTransport (MonoidalChange)

universe u w a

attribute [local instance] HasDerivedCategory.standard

noncomputable section

set_option linter.checkUnivs false

section Projection

/-- Evaluation for the actual derived tensor--Hom adjunction. -/
abbrev EvaluationType :=
  ∀ {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e} {T : DerivedTensor.Model M} {H : Models.{u,a} R},
    Closed T H → ∀ X Y : derivedValue.{a} R,
    letI := T.monoidal
    (rHomValue H).obj (op X, Y) ⊗ X ⟶ Y

def evaluationValue : EvaluationType :=
  fun c X Y => (c.equiv _ X Y).symm (𝟙 _)

/-- Move the left tensor factor past the closed adjunction by tensoring evaluation. -/
abbrev ProjectionComparisonType :=
  ∀ {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e} {T : DerivedTensor.Model M} {H : Models.{u,a} R},
    Closed T H → ∀ P X Y : derivedValue.{a} R,
    letI := T.monoidal
    P ⊗ (rHomValue H).obj (op X, Y) ⟶ (rHomValue H).obj (op X, P ⊗ Y)

def projectionComparisonValue : ProjectionComparisonType :=
  fun {_ _ _ _ _ _ T H} c P X Y =>
    letI := T.monoidal
    c.equiv _ X (P ⊗ Y) ((α_ P ((rHomValue H).obj (op X, Y)) X).hom ≫
      (𝟙 P ⊗ₘ evaluationValue c X Y))

/-- Naturality in the tensor factor and both variables of internal Hom. -/
def ProjectionNaturality : Prop :=
  ∀ {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e} {T : DerivedTensor.Model M} {H : Models.{u,a} R}
    (c : Closed T H) {P P' X X' Y Y' : derivedValue.{a} R}
    (p : P ⟶ P') (x : X' ⟶ X) (y : Y ⟶ Y'),
    letI := T.monoidal
    (p ⊗ₘ (rHomValue H).map (Prod.mkHom x.op y)) ≫ projectionComparisonValue c P' X' Y' =
      projectionComparisonValue c P X Y ≫ (rHomValue H).map (Prod.mkHom x.op (p ⊗ₘ y))

end Projection

section BaseChange

/-- The comparison uses the tensorator of derived scalar extension. -/
abbrev BaseChangeType :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    {A B : Type a} [CommRing A] [CommRing B] {e : R ≃+* A} {d : S ≃+* B}
    {MR : AdequateModel e} {MS : AdequateModel d}
    {TR : DerivedTensor.Model MR} {TS : DerivedTensor.Model MS}
    {HR : Models.{u,a} R} {HS : Models.{w,a} S}
    {f : R →+* S} {F : MonoidalChange e d f MR MS} {L : Extension d f},
    Closed TR HR → Closed TS HS →
    MonoidalExtension TR.toDescent TS.toDescent F L → ∀ X Y : derivedValue.{a} R,
      L.derived.obj ((rHomValue HR).obj (op X, Y)) ⟶
        (rHomValue HS).obj (op (L.derived.obj X), L.derived.obj Y)

def baseChangeValue : BaseChangeType :=
  fun {_ _ _ _ _ _ _ _ _ _ _ _ TR TS HR _ _ _ L} cR cS m X Y =>
    letI := TR.monoidal
    letI := TS.monoidal
    letI := TR.symmetric
    letI := TS.symmetric
    letI := m.braided
    cS.equiv _ (L.derived.obj X) (L.derived.obj Y)
      (Functor.LaxMonoidal.μ L.derived ((rHomValue HR).obj (op X, Y)) X ≫
        L.derived.map (evaluationValue cR X Y))

/-- Naturality in both variables for each scalar extension. -/
def BaseChangeNaturality : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    {A B : Type a} [CommRing A] [CommRing B] {e : R ≃+* A} {d : S ≃+* B}
    {MR : AdequateModel e} {MS : AdequateModel d}
    {TR : DerivedTensor.Model MR} {TS : DerivedTensor.Model MS}
    {HR : Models.{u,a} R} {HS : Models.{w,a} S}
    {f : R →+* S} {F : MonoidalChange e d f MR MS} {L : Extension d f}
    (cR : Closed TR HR) (cS : Closed TS HS)
    (m : MonoidalExtension TR.toDescent TS.toDescent F L) {X X' Y Y' : derivedValue.{a} R}
    (x : X' ⟶ X) (y : Y ⟶ Y'),
    L.derived.map ((rHomValue HR).map (Prod.mkHom x.op y)) ≫ baseChangeValue cR cS m X' Y' =
      baseChangeValue cR cS m X Y ≫
        (rHomValue HS).map (Prod.mkHom (L.derived.map x).op (L.derived.map y))

end BaseChange

end

end Specs.DerivedFormalization.DerivedHomComparisonMaps
