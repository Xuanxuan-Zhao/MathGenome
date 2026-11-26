import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisDualFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Proposition M01: the socle, exactness and detection for the residue-field hull. -/

noncomputable section

open CategoryTheory

namespace CommutativeAlgebraNotes.MatlisDualExactDetectionSpecs

open MatlisDualFunctorSpecs

universe u v w z

def envelopeSocle : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R),
    AdvCommAlg.Depth.Socle R E.carrier = LinearMap.range E.inclusion

def envelopeSocleEquiv : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R),
    ∃ e : IsLocalRing.ResidueField R ≃ₗ[IsLocalRing.ResidueField R]
        AdvCommAlg.Depth.Socle R E.carrier,
      ∀ a, (e a).val = E.inclusion a

def existsEnvelopeWithSocle : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R],
    ∃ E : residueFieldEnvelopeValue R,
      AdvCommAlg.Depth.Socle R E.carrier = LinearMap.range E.inclusion

def dualMapSurjective : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y), Function.Injective f → Function.Surjective (matlisDualMapValue E f)

def dualMapShortExact : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    {X : Type v} {Y : Type w} {Z : Type z}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
      Function.Injective (matlisDualMapValue E g) ∧
      Function.Exact (matlisDualMapValue E g) (matlisDualMapValue E f) ∧
      Function.Surjective (matlisDualMapValue E f)

local instance {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R) :
    (matlisDualValue E).PreservesZeroMorphisms where
  map_zero _ _ :=
    ModuleCat.hom_ext (LinearMap.ext fun f => LinearMap.ext fun _ => f.map_zero)

def dualShortExact : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (S : ShortComplex (ModuleCat.{u} R)),
    S.ShortExact → (S.op.map (matlisDualValue E)).ShortExact

def dualSeparates : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    {X : Type v} [AddCommGroup X] [Module R X] (x : X),
    x ≠ 0 → ∃ f : matlisDualModuleValue E X, f x ≠ 0

def dualNontrivialIff : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (X : Type v) [AddCommGroup X] [Module R X],
    Nontrivial (matlisDualModuleValue E X) ↔ Nontrivial X

def evaluationInjective : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (X : Type v) [AddCommGroup X] [Module R X], Function.Injective (matlisEvaluationValue E X)

end CommutativeAlgebraNotes.MatlisDualExactDetectionSpecs
