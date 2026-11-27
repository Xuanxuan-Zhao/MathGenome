import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.LocalizationCoverFaithfulness

universe u v

namespace DerivedFormalization.Descent

/-- The product of the localizations in a finite principal-open cover is faithfully flat. -/
theorem localizationCover_faithfullyFlat :
    Specs.Descent.localizationCoverFaithfullyFlat.{u, v} := by
  classical
  intro A _ ι _ f hf
  let S (i : ι) := Localization.Away (f i)
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective, RingHom.flat_algebraMap_iff]
  constructor
  · let : Fintype ι := Fintype.ofFinite ι
    let : ∀ i, Module.Flat A (S i) := fun i =>
      IsLocalization.flat (S i) (Submonoid.powers (f i))
    exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype A ι S).symm
  · intro p
    have hcover : (⨆ i, PrimeSpectrum.basicOpen (f i)) = ⊤ :=
      PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hf
    have hp : p ∈ ⨆ i, PrimeSpectrum.basicOpen (f i) := by
      rw [hcover]
      exact TopologicalSpace.Opens.mem_top p
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    have hi' : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (S i))) := by
      rw [PrimeSpectrum.localization_away_comap_range (S i) (f i)]
      exact hi
    obtain ⟨q, hq⟩ := hi'
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom S i) q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply]
    exact hq

end DerivedFormalization.Descent
