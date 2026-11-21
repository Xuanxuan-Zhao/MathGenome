import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Prime.Topology

namespace Specs.P103.Ch04.LocalizationSpectrumNonopen

/-- A localization can have non-open image on prime spectra: invert the
nonzero integers to obtain the fraction field of ℤ. -/
def integerFractionRingImageNotOpen : Prop :=
  ¬ IsOpen (Set.range
    (PrimeSpectrum.comap (algebraMap ℤ (FractionRing ℤ))))

end Specs.P103.Ch04.LocalizationSpectrumNonopen
