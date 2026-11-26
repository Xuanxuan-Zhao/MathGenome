import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.InjectiveHullTruncations

/-! The scalar isomorphism for a residue-field injective hull and its truncations. -/

namespace Specs.CommutativeAlgebraNotes.EndomorphismsOfResidueHull

open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs (residueFieldEnvelopeValue)
open _root_.CommutativeAlgebraNotes.InjectiveHullTruncationSpecs (TruncationRing hullTruncation)
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (Completion IsPowerTorsion scalar)

universe u

/-- Scalar multiplication by the completion identifies it with the endomorphism algebra of
the hull. At every positive stage, the corresponding scalar isomorphism for the quotient
agrees with restriction after reduction. -/
def residueHullEndomorphismsType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue R),
    ∃ (h : IsPowerTorsion R E.carrier)
      (e : Completion R ≃ₐ[R] Module.End R E.carrier)
      (eₙ : ∀ n : ℕ, 1 ≤ n → TruncationRing R n ≃ₐ[R] Module.End R (hullTruncation E n)),
      (∀ s x, e s x = scalar h s x) ∧
      (∀ n hn a x, eₙ n hn a x = a • x) ∧
      (∀ n hn s (x : hullTruncation E n),
        e s x.val = (eₙ n hn (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) n s) x).val)

end Specs.CommutativeAlgebraNotes.EndomorphismsOfResidueHull
