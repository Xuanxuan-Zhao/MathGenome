import MathGenome.Internal.Specs.D07.Ch22.LocalizationIdeals
import MathGenome.Internal.D07.Ch22.LocalizationIdealsExtensionSaturation
import MathGenome.Internal.D07.Ch09.Contraction
import MathGenome.Internal.D07.Ch22.LocalizationUniversal
import Mathlib.RingTheory.Localization.Ideal

/-! K07.22.localization_ideals: localized ideals and the full prime
correspondence, including zero denominators and zero base rings. -/

universe u

namespace D07.Ch22.LocalizationIdeals

open Specs.D07.Ch22.LocalizationIdeals

theorem idealFormulas : IdealFormulas.{u} :=
  ⟨LocalizationIdealsExtensionSaturation.extendedIdealFractions,
    LocalizationIdealsExtensionSaturation.contractionSaturation,
    LocalizationIdealsExtensionSaturation.everyIdealExtended,
    LocalizationIdealsExtensionSaturation.extensionTopIffMeets⟩

theorem primeExtension : PrimeExtension.{u} := by
  intro R _ S P hP hS
  exact IsLocalization.isPrime_of_isPrime_disjoint S (Localization S) P hP hS

theorem primeContraction : PrimeContraction.{u} := by
  intro R _ S Q hQ
  refine ⟨D07.Ch09.Contraction.prime_contraction R (Localization S)
    (algebraMap R (Localization S)) Q hQ, ?_⟩
  apply Set.disjoint_left.mpr
  intro s hs hmem
  exact hQ.ne_top (Q.eq_top_of_isUnit_mem hmem
    (IsLocalization.map_units (Localization S) ⟨s, hs⟩))

theorem contractionExtension : ContractionExtension.{u} := by
  intro R _ S P hP hS
  apply le_antisymm
  · intro r hr
    obtain ⟨s, hsr⟩ :=
      (LocalizationIdealsExtensionSaturation.contractionSaturation R S P r).mp hr
    exact (hP.mem_or_mem hsr).resolve_left
      (fun hs => Set.disjoint_left.mp hS s.property hs)
  · exact Ideal.le_comap_map

theorem primeCorrespondence : PrimeCorrespondence.{u} := by
  intro R _ S
  let e : {P : Ideal R // P.IsPrime ∧ Disjoint (S : Set R) (P : Set R)} ≃o
      {Q : Ideal (Localization S) // Q.IsPrime} :=
    { toFun := fun P => ⟨Ideal.map (algebraMap R (Localization S)) P.val,
        primeExtension R S P.val P.property.1 P.property.2⟩
      invFun := fun Q => ⟨Ideal.comap (algebraMap R (Localization S)) Q.val,
        primeContraction R S Q.val Q.property⟩
      left_inv := fun P => Subtype.ext
        (contractionExtension R S P.val P.property.1 P.property.2)
      right_inv := fun Q => Subtype.ext
        (LocalizationIdealsExtensionSaturation.everyIdealExtended R S Q.val)
      map_rel_iff' := by
        intro P P'
        constructor
        · intro h
          change Ideal.map (algebraMap R (Localization S)) P.val ≤
            Ideal.map (algebraMap R (Localization S)) P'.val at h
          have hc := Ideal.comap_mono (f := algebraMap R (Localization S)) h
          rwa [contractionExtension R S P.val P.property.1 P.property.2,
            contractionExtension R S P'.val P'.property.1 P'.property.2] at hc
        · exact Ideal.map_mono }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

theorem zeroDenominatorPrimes : ZeroDenominatorPrimes.{u} := by
  intro R _ S hzero
  have hempty : IsEmpty
      {P : Ideal R // P.IsPrime ∧ Disjoint (S : Set R) (P : Set R)} :=
    ⟨fun P => Set.disjoint_left.mp P.property.2 hzero P.val.zero_mem⟩
  refine ⟨hempty, ?_, (LocalizationUniversal.zeroRingIff R S).mpr hzero⟩
  exact ⟨fun Q => hempty.false ⟨Ideal.comap (algebraMap R (Localization S)) Q.val,
    primeContraction R S Q.val Q.property⟩⟩

end D07.Ch22.LocalizationIdeals
