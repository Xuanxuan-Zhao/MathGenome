import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.ExtLocalization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Localization
import Mathlib.RingTheory.LocalProperties.InjectiveDimension

/-!
GC-07: localization of a local Gorenstein ring at any prime.

Over a Noetherian ring localization preserves injective modules and is
exact. Thus a finite injective-dimension bound survives module localization
(`ModuleCat.localizedModule_hasInjectiveDimensionLE`). Apply this to the
regular module R, and identify its localization with the regular module of
R_p using the canonical localized-ring isomorphism from GC's Ext interfaces.
This proves the assertion directly from finite self-injective dimension.
-/

universe u
open CategoryTheory

namespace AdvCommAlg.Gorenstein

/-- Prime localization preserves the local Gorenstein condition. -/
theorem localGorenstein_atPrime (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hR : LocalGorenstein R)
    (p : Ideal R) [p.IsPrime] : LocalGorenstein (Localization.AtPrime p) := by
  obtain ⟨n, hn⟩ := (finiteInjectiveDimension_iff_exists_bound R R).mp hR
  have := hn
  have := ModuleCat.localizedModule_hasInjectiveDimensionLE n p.primeCompl
    (ModuleCat.of R R)
  apply (finiteInjectiveDimension_iff_exists_bound
    (Localization.AtPrime p) (Localization.AtPrime p)).mpr
  exact ⟨n, hasInjectiveDimensionLT_of_iso
    (ExtLocalization.localizedRingIso p.primeCompl) (n + 1)⟩

end AdvCommAlg.Gorenstein
