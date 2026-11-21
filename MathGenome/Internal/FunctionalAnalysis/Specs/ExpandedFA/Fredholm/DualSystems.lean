import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.Star
import Mathlib.Algebra.Module.RingHom

/-!
Independent interface for the dual systems in paper.tex 10386–10406 and
10529–10539. The pairing is algebraically bilinear, in the same orientation
`B y x` as the earlier weak-pairing interface. Neither norm boundedness nor
continuity of this pairing is part of the data. No completeness is required.

For the sesquilinear variant we use the manuscript convention: conjugate
linear in X, linear in Y. On the conjugate of X the action is
`a •conj x = conj a • x`, and the norm and additive structure are unchanged.
The structures below are canonical shared data, not assumed theorems.
-/

namespace ExpandedFA.Fredholm.DualSystemsSpec

universe u v u₁ v₁ u₂ v₂
noncomputable section

/-- Nondegeneracy is imposed separately on both sides. -/
structure DualSystemData (X : Type u) (Y : Type v)
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] where
  pairing : Y →ₗ[ℂ] X →ₗ[ℂ] ℂ
  separatesLeft : ∀ x, (∀ y, pairing y x = 0) → x = 0
  separatesRight : ∀ y, (∀ x, pairing y x = 0) → y = 0

/-- A type copy carrying the conjugated complex scalar action. -/
def ConjugateSpaceData (X : Type u) : Type u := X

instance {X : Type u} [NormedAddCommGroup X] :
    NormedAddCommGroup (ConjugateSpaceData X) :=
  inferInstanceAs (NormedAddCommGroup X)

instance {X : Type u} [NormedAddCommGroup X] [Module ℂ X] :
    Module ℂ (ConjugateSpaceData X) := Module.compHom X (starRingEnd ℂ)

instance {X : Type u} [NormedAddCommGroup X] [h : NormedSpace ℂ X] :
    NormedSpace ℂ (ConjugateSpaceData X) where
  toModule := instModuleComplexConjugateSpaceData
  norm_smul_le := fun a (x : X) => by
    change ‖star a • x‖ ≤ ‖a‖ * ‖x‖
    simpa only [norm_star] using (@NormedSpace.norm_smul_le ℂ X _ _ h (star a) x)

/-- The manuscript's conjugate-linear-first convention, with no continuity. -/
structure SesquilinearSystemData (X : Type u) (Y : Type v)
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] where
  pairing : Y →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ
  separatesLeft : ∀ x, (∀ y, pairing y x = 0) → x = 0
  separatesRight : ∀ y, (∀ x, pairing y x = 0) → y = 0

def DualSystemType :=
  ∀ (X : Type u) (Y : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y], Type (max u v)

def DualSystemValue : DualSystemType := fun X Y _ _ _ _ => DualSystemData X Y

def SesquilinearSystemType :=
  ∀ (X : Type u) (Y : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y], Type (max u v)

def SesquilinearSystemValue : SesquilinearSystemType :=
  fun X Y _ _ _ _ => SesquilinearSystemData X Y

def ConjugateSpaceType := Type u → Type u
def ConjugateSpaceValue : ConjugateSpaceType := ConjugateSpaceData

section OneSystem

variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

def BracketType := DualSystemData X Y → X → Y → ℂ
def BracketValue : BracketType (X := X) (Y := Y) := fun D x y => D.pairing y x

def OfPairingType :=
  ∀ (B : Y →ₗ[ℂ] X →ₗ[ℂ] ℂ),
    (∀ x, (∀ y, B y x = 0) → x = 0) →
    (∀ y, (∀ x, B y x = 0) → y = 0) → DualSystemData X Y

def OfPairingValue : OfPairingType (X := X) (Y := Y) :=
  fun B hX hY => ⟨B, hX, hY⟩

def Separation : Prop :=
  ∀ (D : DualSystemData X Y),
    (∀ x, (∀ y, D.pairing y x = 0) ↔ x = 0) ∧
    (∀ y, (∀ x, D.pairing y x = 0) ↔ y = 0)

def WeakTopologyType := DualSystemData X Y → TopologicalSpace X
def WeakTopologyValue : WeakTopologyType (X := X) (Y := Y) :=
  fun D => ExpandedFA.P1.C12DualPairSpec.DualPairTopologyValue ℂ X Y D.pairing

def WeakTopologyCompatibility : Prop :=
  ∀ (D : DualSystemData X Y), WeakTopologyValue D =
    ExpandedFA.P1.C12DualPairSpec.DualPairTopologyValue ℂ X Y D.pairing

def FlipType := DualSystemData X Y → DualSystemData Y X
def FlipValue : FlipType (X := X) (Y := Y) :=
  fun D => ⟨D.pairing.flip, D.separatesRight, D.separatesLeft⟩

def SesquilinearTransportType :=
  SesquilinearSystemData X Y → DualSystemData (ConjugateSpaceData X) Y

def SesquilinearTransportValue : SesquilinearTransportType (X := X) (Y := Y) :=
  fun S => {
    pairing := {
      toFun := fun y => {
        toFun := fun x => S.pairing y (x : X)
        map_add' := fun x z => (S.pairing y).map_add x z
        map_smul' := fun a (x : X) => by
          change S.pairing y (star a • x) = a • S.pairing y x
          simp only [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star] }
      map_add' := fun y z => by
        ext x
        exact LinearMap.congr_fun (S.pairing.map_add y z) (x : X)
      map_smul' := fun a y => by
        ext x
        exact LinearMap.congr_fun (S.pairing.map_smul a y) (x : X) }
    separatesLeft := S.separatesLeft
    separatesRight := S.separatesRight }

def SesquilinearTransportEvaluation : Prop :=
  ∀ (S : SesquilinearSystemData X Y) (x : X) (y : Y),
    (SesquilinearTransportValue S).pairing y (show ConjugateSpaceData X from x) =
      S.pairing y x

end OneSystem

section Conjugation

variable {X : Type u₁} {Z : Type u₂}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

def ConjugateScalarAction : Prop :=
  ∀ (a : ℂ) (x : X),
    (a • (show ConjugateSpaceData X from x) : ConjugateSpaceData X) =
      (show ConjugateSpaceData X from star a • x)

def ConjugateNorm : Prop :=
  ∀ (x : X), ‖(show ConjugateSpaceData X from x)‖ = ‖x‖

def ConjugateLinearMapType :=
  (X →ₗ[ℂ] Z) → (ConjugateSpaceData X →ₗ[ℂ] ConjugateSpaceData Z)

def ConjugateLinearMapValue : ConjugateLinearMapType (X := X) (Z := Z) :=
  fun T => {
    toFun := fun x => T (x : X)
    map_add' := fun x z => T.map_add x z
    map_smul' := fun a x => T.map_smul (star a) (x : X) }

def ConjugateContinuousLinearMapType :=
  (X →L[ℂ] Z) → (ConjugateSpaceData X →L[ℂ] ConjugateSpaceData Z)

def ConjugateContinuousLinearMapValue : ConjugateContinuousLinearMapType (X := X) (Z := Z) :=
  fun T => { ConjugateLinearMapValue T.toLinearMap with cont := T.cont }

def ConjugateMapEvaluation : Prop :=
  (∀ (T : X →ₗ[ℂ] Z) (x : X),
    ConjugateLinearMapValue T (show ConjugateSpaceData X from x) =
      (show ConjugateSpaceData Z from T x)) ∧
  (∀ (T : X →L[ℂ] Z) (x : X),
    ConjugateContinuousLinearMapValue T (show ConjugateSpaceData X from x) =
      (show ConjugateSpaceData Z from T x))

end Conjugation

section Adjoint

variable {X₁ : Type u₁} {Y₁ : Type v₁} {X₂ : Type u₂} {Y₂ : Type v₂}
  [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
  [NormedAddCommGroup X₂] [NormedSpace ℂ X₂]
  [NormedAddCommGroup Y₂] [NormedSpace ℂ Y₂]

/-- Algebraic maps suffice for defining the adjoint relation. Bounded maps
are passed through their underlying linear maps; no adjoint existence is assumed. -/
def PairedAdjointType :=
  DualSystemData X₁ Y₁ → DualSystemData X₂ Y₂ →
    (X₁ →ₗ[ℂ] X₂) → (Y₂ →ₗ[ℂ] Y₁) → Prop

def PairedAdjointValue :
    PairedAdjointType (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂) :=
  fun D₁ D₂ T U => ∀ x y, D₂.pairing y (T x) = D₁.pairing (U y) x

def PairedAdjointEquation : Prop :=
  ∀ (D₁ : DualSystemData X₁ Y₁) (D₂ : DualSystemData X₂ Y₂)
    (T : X₁ →ₗ[ℂ] X₂) (U : Y₂ →ₗ[ℂ] Y₁),
    PairedAdjointValue D₁ D₂ T U ↔
      ∀ x y, BracketValue D₂ (T x) y = BracketValue D₁ x (U y)

def PairedAdjointUnique : Prop :=
  ∀ (D₁ : DualSystemData X₁ Y₁) (D₂ : DualSystemData X₂ Y₂)
    (T : X₁ →ₗ[ℂ] X₂) (U V : Y₂ →ₗ[ℂ] Y₁),
    PairedAdjointValue D₁ D₂ T U → PairedAdjointValue D₁ D₂ T V → U = V

def SesquilinearAdjointTransport : Prop :=
  ∀ (S₁ : SesquilinearSystemData X₁ Y₁) (S₂ : SesquilinearSystemData X₂ Y₂)
    (T : X₁ →ₗ[ℂ] X₂) (U : Y₂ →ₗ[ℂ] Y₁),
    PairedAdjointValue (SesquilinearTransportValue S₁) (SesquilinearTransportValue S₂)
      (ConjugateLinearMapValue T) U ↔
        ∀ x y, S₂.pairing y (T x) = S₁.pairing (U y) x

end Adjoint

/- Closed expected types quantify every space and instance independently. -/

def BracketTypeAll :=
  ∀ {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y], BracketType (X := X) (Y := Y)

def OfPairingTypeAll :=
  ∀ {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y], OfPairingType (X := X) (Y := Y)

def WeakTopologyTypeAll :=
  ∀ {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y], WeakTopologyType (X := X) (Y := Y)

def FlipTypeAll :=
  ∀ {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y], FlipType (X := X) (Y := Y)

def SesquilinearTransportTypeAll :=
  ∀ {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y], SesquilinearTransportType (X := X) (Y := Y)

def SeparationAll : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y], Separation (X := X) (Y := Y)

def WeakTopologyCompatibilityAll : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y], WeakTopologyCompatibility (X := X) (Y := Y)

def SesquilinearTransportEvaluationAll : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y], SesquilinearTransportEvaluation (X := X) (Y := Y)

def ConjugateLinearMapTypeAll :=
  ∀ {X : Type u₁} {Z : Type u₂}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z], ConjugateLinearMapType (X := X) (Z := Z)

def ConjugateContinuousLinearMapTypeAll :=
  ∀ {X : Type u₁} {Z : Type u₂}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z], ConjugateContinuousLinearMapType (X := X) (Z := Z)

def ConjugateScalarActionAll : Prop :=
  ∀ {X : Type u₁}
    [NormedAddCommGroup X] [NormedSpace ℂ X], ConjugateScalarAction (X := X)

def ConjugateNormAll : Prop :=
  ∀ {X : Type u₁}
    [NormedAddCommGroup X] [NormedSpace ℂ X], ConjugateNorm (X := X)

def ConjugateMapEvaluationAll : Prop :=
  ∀ {X : Type u₁} {Z : Type u₂}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z], ConjugateMapEvaluation (X := X) (Z := Z)

def PairedAdjointTypeAll :=
  ∀ {X₁ : Type u₁} {Y₁ : Type v₁} {X₂ : Type u₂} {Y₂ : Type v₂}
    [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
    [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    [NormedAddCommGroup X₂] [NormedSpace ℂ X₂]
    [NormedAddCommGroup Y₂] [NormedSpace ℂ Y₂], PairedAdjointType (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂)

def PairedAdjointEquationAll : Prop :=
  ∀ {X₁ : Type u₁} {Y₁ : Type v₁} {X₂ : Type u₂} {Y₂ : Type v₂}
    [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
    [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    [NormedAddCommGroup X₂] [NormedSpace ℂ X₂]
    [NormedAddCommGroup Y₂] [NormedSpace ℂ Y₂], PairedAdjointEquation (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂)

def PairedAdjointUniqueAll : Prop :=
  ∀ {X₁ : Type u₁} {Y₁ : Type v₁} {X₂ : Type u₂} {Y₂ : Type v₂}
    [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
    [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    [NormedAddCommGroup X₂] [NormedSpace ℂ X₂]
    [NormedAddCommGroup Y₂] [NormedSpace ℂ Y₂], PairedAdjointUnique (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂)

def SesquilinearAdjointTransportAll : Prop :=
  ∀ {X₁ : Type u₁} {Y₁ : Type v₁} {X₂ : Type u₂} {Y₂ : Type v₂}
    [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
    [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    [NormedAddCommGroup X₂] [NormedSpace ℂ X₂]
    [NormedAddCommGroup Y₂] [NormedSpace ℂ Y₂], SesquilinearAdjointTransport (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂)

end
end ExpandedFA.Fredholm.DualSystemsSpec
