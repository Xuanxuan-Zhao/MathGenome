import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisDualFunctor
import Mathlib.RingTheory.Length

/-! The finite-length part of Proposition M02. The base ring can be any commutative local ring. -/

namespace CommutativeAlgebraNotes.FiniteLengthMatlisDualitySpecs

open MatlisDualFunctorSpecs

universe u v w

def dualLength : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (X : Type v) [AddCommGroup X] [Module R X],
    IsFiniteLength R X → Module.length R (matlisDualModuleValue E X) = Module.length R X

def dualFiniteLength : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (X : Type v) [AddCommGroup X] [Module R X],
    IsFiniteLength R X → IsFiniteLength R (matlisDualModuleValue E X)

def evaluationEquiv : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (X : Type v) [AddCommGroup X] [Module R X], IsFiniteLength R X →
    ∃ e : X ≃ₗ[R] matlisDualModuleValue E (matlisDualModuleValue E X),
      e.toLinearMap = matlisEvaluationValue E X

def evaluationNaturality : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y),
    (matlisDualMapValue E (matlisDualMapValue E f)).comp (matlisEvaluationValue E X) =
      (matlisEvaluationValue E Y).comp f

end CommutativeAlgebraNotes.FiniteLengthMatlisDualitySpecs
