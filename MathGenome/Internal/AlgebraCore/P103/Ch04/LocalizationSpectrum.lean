import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.LocalizationSpectrum
import MathGenome.Internal.AlgebraCore.P103.Ch04.RingLocalization
import MathGenome.Internal.AlgebraCore.P103.Ch04.SpectrumFunctorQuotient

universe u

namespace P103.Ch04.LocalizationSpectrum

theorem order_correspondence : Specs.P103.Ch04.LocalizationSpectrum.order_correspondence := by
  intro R _ S
  exact ⟨IsLocalization.primeSpectrumOrderIso S (Localization S),
    (fun _ => rfl), (fun _ => rfl)⟩

theorem fraction_membership : Specs.P103.Ch04.LocalizationSpectrum.fraction_membership := by
  intro R _ S p hp a s
  rw [Localization.mk_eq_mk', IsLocalization.mk'_mem_iff]
  change a ∈ (p.asIdeal.map (algebraMap R (Localization S))).under R ↔ a ∈ p.asIdeal
  rw [IsLocalization.under_map_of_isPrime_disjoint S (Localization S) p.isPrime hp]

theorem contraction_range : Specs.P103.Ch04.LocalizationSpectrum.contraction_range := by
  intro R _ S
  exact PrimeSpectrum.localization_comap_range (Localization S) S

theorem localization_homeomorphism :
    Specs.P103.Ch04.LocalizationSpectrum.localization_homeomorphism := by
  intro R _ S
  let e := (IsLocalization.primeSpectrumOrderIso S (Localization S)).toEquiv
  have he : Topology.IsInducing e := by
    apply Topology.IsInducing.subtypeVal.of_comp_iff.mp
    exact PrimeSpectrum.localization_comap_isInducing (Localization S) S
  exact ⟨e.toHomeomorphOfIsInducing he, (fun _ => rfl), (fun _ => rfl)⟩

theorem principal_homeomorphism :
    Specs.P103.Ch04.LocalizationSpectrum.principal_homeomorphism := by
  intro R _ f
  let e₀ := IsLocalization.primeSpectrumOrderIso (Submonoid.powers f) (Localization.Away f)
  have hp (p : PrimeSpectrum R) :
      Disjoint (Submonoid.powers f : Set R) (p.asIdeal : Set R) ↔
        p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    Ideal.disjoint_powers_iff_notMem_of_isPrime f
  let e := e₀.toEquiv.trans (Equiv.subtypeEquivRight hp)
  have he : Topology.IsInducing e := by
    apply Topology.IsInducing.subtypeVal.of_comp_iff.mp
    exact PrimeSpectrum.localization_comap_isInducing (Localization.Away f) (Submonoid.powers f)
  exact ⟨e.toHomeomorphOfIsInducing he, (fun _ => rfl), (fun _ => rfl)⟩

theorem zero_in_submonoid : Specs.P103.Ch04.LocalizationSpectrum.zero_in_submonoid := by
  intro R _ S hS
  let : Subsingleton (Localization S) := (RingLocalization.zeroRingCriterion R S).mpr hS
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro p
  exact Set.disjoint_left.mp p.property hS p.val.asIdeal.zero_mem

end P103.Ch04.LocalizationSpectrum
