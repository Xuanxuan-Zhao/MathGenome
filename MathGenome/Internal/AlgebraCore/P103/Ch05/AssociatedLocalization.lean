import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.AssociatedLocalization
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Localization.Submodule

namespace P103.Ch05.AssociatedLocalization

universe u v
open P103.Specs.Ch05.AssociatedPrimesInterface
open P103.Specs.Ch05.AssociatedLocalization

/-- On a Noetherian base Mathlib's radical formulation agrees with the
source's exact-annihilator definition. No finiteness of the module is needed. -/
theorem associatedPrimes_eq_library (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    associatedPrimesValue R M = _root_.associatedPrimes R M := by
  ext p
  exact isAssociatedPrime_iff.symm

theorem contraction : contractionType.{u,v} := by
  intro R _ _ M _ _ _ S q
  rw [associatedPrimes_eq_library, associatedPrimes_eq_library]
  exact (Set.ext_iff.mp
    (Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
      S (Localization S) (LocalizedModule.mkLinearMap S M)) q).symm

theorem localization : localizationType.{u,v} := by
  intro R _ _ M _ _ _ S
  ext q
  constructor
  · intro hq
    have hp := (contraction R M S q).mp hq
    have hprime : q.IsPrime := hq.1
    refine ⟨q.comap (algebraMap R (Localization S)), ⟨hp, ?_⟩, ?_⟩
    · exact (IsLocalization.disjoint_under_iff S (Localization S) q).mpr hprime.ne_top
    · exact IsLocalization.map_under S (Localization S) q
  · rintro ⟨p, ⟨hp, hd⟩, rfl⟩
    apply (contraction R M S _).mpr
    simpa only [IsLocalization.under_map_of_isPrime_disjoint S (Localization S) hp.1 hd]
      using hp

end P103.Ch05.AssociatedLocalization
