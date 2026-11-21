import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions

/-!
GC-07, prime localization assertion (paper.tex:4594–4621).
The local Gorenstein condition is finite self-injective dimension, using
GC-01's actual categorical injective dimension. No Cohen–Macaulay or
regularity assumption is imposed.
-/

universe u

namespace AdvCommAlg.Gorenstein.Specs

/-- Every prime localization of a nonzero Noetherian Gorenstein local ring
has finite injective dimension over itself. -/
def localGorenstein_atPrimeType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    LocalGorensteinValue R →
    ∀ (p : Ideal R) [p.IsPrime], LocalGorensteinValue (Localization.AtPrime p)

end AdvCommAlg.Gorenstein.Specs
