import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.PowerSeriesEvaluation
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import Mathlib.RingTheory.MvPowerSeries.Evaluation

namespace CommutativeAlgebraNotes.PowerSeriesEvaluation

open IsLocalRing

private theorem continuous_adic_of_isLocalHom {A B : Type*}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    @Continuous A B (maximalIdeal A).adicTopology (maximalIdeal B).adicTopology f := by
  let : WithIdeal A := ⟨maximalIdeal A⟩
  let : WithIdeal B := ⟨maximalIdeal B⟩
  exact (WithIdeal.uniformContinuous_of_map_le (map_maximalIdeal_le f)).continuous

/-- Evaluate formal power series at elements of the target maximal ideal,
using the maximal-ideal adic topologies on the two local rings. -/
theorem evaluation : Specs.CommutativeAlgebraNotes.PowerSeriesEvaluation.Evaluation := by
  intro D R _ _ _ _ _ _ φ _ hφ s x hx
  let S := MvPowerSeries (Fin s) D
  let : WithIdeal D := ⟨maximalIdeal D⟩
  let : WithIdeal R := ⟨maximalIdeal R⟩
  have hcomplete : IsAdicComplete (maximalIdeal R) R := inferInstance
  have hAdic : IsAdic (maximalIdeal R) := by rfl
  have htop := hAdic.isAdicComplete_iff.mp hcomplete
  have : CompleteSpace R := htop.1
  have : T2Space R := htop.2
  have hφcont : Continuous φ := continuous_adic_of_isLocalHom φ
  have hEval : MvPowerSeries.HasEval x := by
    refine ⟨fun i => WithIdeal.isTopologicallyNilpotent_of_mem (hx i), ?_⟩
    rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot
  let F : S →+* R := MvPowerSeries.eval₂Hom hφcont hEval
  have hC (d : D) : F (MvPowerSeries.C d) = φ d := by
    change MvPowerSeries.eval₂Hom hφcont hEval (MvPowerSeries.C d) = _
    rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C]
  have hX (i : Fin s) : F (MvPowerSeries.X i) = x i := by
    change MvPowerSeries.eval₂Hom hφcont hEval (MvPowerSeries.X i) = _
    rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]
  have hmap : (maximalIdeal S).map F =
      (maximalIdeal D).map φ ⊔ Ideal.span (Set.range x) := by
    have hconst : F.comp MvPowerSeries.C = φ := RingHom.ext hC
    have hvars : F ∘ MvPowerSeries.X = x := funext hX
    rw [CompleteRegularPowerSeries.maximalIdeal_eq_span_sup, Ideal.map_sup,
      Ideal.map_span, ← Set.range_comp, Ideal.map_map, hconst, hvars, sup_comm]
  have hle : (maximalIdeal S).map F ≤ maximalIdeal R := by
    rw [hmap]
    exact sup_le (map_maximalIdeal_le φ)
      (Ideal.span_le.mpr (Set.range_subset_iff.mpr hx))
  have hF : IsLocalHom F := ((local_hom_TFAE F).out 3 1).mp hle
  have hres (f : S) : ResidueField.map F (residue S f) =
      ResidueField.map φ (residue D (MvPowerSeries.constantCoeff f)) := by
    have hf : f - MvPowerSeries.C (MvPowerSeries.constantCoeff f) ∈ maximalIdeal S := by
      rw [mem_maximalIdeal]
      change ¬IsUnit (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f))
      rw [MvPowerSeries.isUnit_iff_constantCoeff, map_sub,
        MvPowerSeries.constantCoeff_C, sub_self]
      exact not_isUnit_zero
    have hzero := (residue_eq_zero_iff _).mpr (hle (Ideal.mem_map_of_mem F hf))
    rw [map_sub, map_sub, hC, sub_eq_zero] at hzero
    simpa only [ResidueField.map_residue] using hzero
  have hsurj : Function.Surjective (ResidueField.map F) := by
    intro y
    obtain ⟨z, rfl⟩ := hφ.2 y
    obtain ⟨d, rfl⟩ := residue_surjective z
    exact ⟨residue S (MvPowerSeries.C d), by
      rw [hres, MvPowerSeries.constantCoeff_C]⟩
  exact ⟨F, hF, continuous_adic_of_isLocalHom F, hC, hX,
    ⟨(ResidueField.map F).injective, hsurj⟩, hres, hmap⟩

end CommutativeAlgebraNotes.PowerSeriesEvaluation
