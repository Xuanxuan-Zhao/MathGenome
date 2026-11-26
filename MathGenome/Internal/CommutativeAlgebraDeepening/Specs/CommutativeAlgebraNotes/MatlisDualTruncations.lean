import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.InjectiveHullTruncations
import Mathlib.RingTheory.Length

/-! The statement of Proposition M02. -/

namespace CommutativeAlgebraNotes.MatlisDualTruncationsSpecs

open IsLocalRing MatlisDualFunctorSpecs InjectiveHullTruncationSpecs

universe u v w

def finiteLengthTruncations : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue R),
    (⋃ n : {n : ℕ // 1 ≤ n}, (hullTruncation E n.val : Set E.carrier)) = Set.univ ∧
    (∀ (n : ℕ) (hn : 1 ≤ n),
      letI := truncationResidueModule (R := R) n hn
      AdvCommAlg.Gorenstein.IsInjectiveEnvelope (truncationResidueInclusion E n hn)) ∧
    (∀ (X : Type v) [AddCommGroup X] [Module R X], IsFiniteLength R X →
      Module.length R (matlisDualModuleValue E X) = Module.length R X ∧
      IsFiniteLength R (matlisDualModuleValue E X) ∧
      ∃ e : X ≃ₗ[R] matlisDualModuleValue E (matlisDualModuleValue E X),
        e.toLinearMap = matlisEvaluationValue E X) ∧
    (∀ {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X]
      [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y),
      (matlisDualMapValue E (matlisDualMapValue E f)).comp (matlisEvaluationValue E X) =
        (matlisEvaluationValue E Y).comp f)

end CommutativeAlgebraNotes.MatlisDualTruncationsSpecs
