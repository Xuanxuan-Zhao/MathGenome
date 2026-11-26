import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.Algebra.Module.Injective
import Mathlib.RingTheory.Noetherian.Defs

/-! Lemma 1.3: ideal-power torsion of an injective module is injective. -/

namespace Specs.CommutativeAlgebraNotes.TorsionOfInjectives

universe u v

def idealTorsionInjectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) {Q : Type v} [AddCommGroup Q] [Module R Q],
    Module.Injective R Q → Module.Injective R (IdealTorsion.idealTorsion I Q)

end Specs.CommutativeAlgebraNotes.TorsionOfInjectives
