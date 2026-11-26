import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs

namespace Specs.CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing

universe u

/-- Every complete Noetherian local ring admits a complete regular local cover
whose map on residue fields is the specified identification. -/
def CompleteRegularCover : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R],
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S),
      IsAdicComplete (maximalIdeal S) S ∧
        ∃ f : S →+* R, IsLocalHom f ∧ Function.Surjective f ∧
          ∃ e : ResidueField S ≃+* ResidueField R,
            (residue R).comp f = e.toRingHom.comp (residue S)

end Specs.CommutativeAlgebraNotes.CoefficientRings
