import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Noetherian.Defs

namespace Specs.CommutativeAlgebraNotes.CoefficientRings.CoefficientField

open IsLocalRing

universe u

/-- An equal-characteristic complete Noetherian local ring has a coefficient field
that maps isomorphically to its residue field. -/
def exists_coefficientField : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R],
    ringChar (ResidueField R) = ringChar R →
      ∃ σ : ResidueField R →+* R,
        (residue R).comp σ = RingHom.id (ResidueField R) ∧ Function.Injective σ

end Specs.CommutativeAlgebraNotes.CoefficientRings.CoefficientField
