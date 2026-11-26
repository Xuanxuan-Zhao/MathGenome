import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularCover
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.AdicFiniteGeneration
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CoefficientField
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CohenRingExistence
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CohenRingMap
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.PowerSeriesEvaluation

namespace CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing

private theorem surjectiveEvaluation
    {D R : Type*} [CommRing D] [IsLocalRing D] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (φ : D →+* R) [IsLocalHom φ] (hφ : Function.Bijective (ResidueField.map φ))
    {s : ℕ} (x : Fin s → R) (hx : Ideal.span (Set.range x) = maximalIdeal R)
    [IsNoetherianRing (MvPowerSeries (Fin s) D)]
    [IsAdicComplete (maximalIdeal (MvPowerSeries (Fin s) D)) (MvPowerSeries (Fin s) D)] :
    let S := MvPowerSeries (Fin s) D
    ∃ f : S →+* R, IsLocalHom f ∧ Function.Surjective f ∧
      ∃ e : ResidueField S ≃+* ResidueField R,
        (residue R).comp f = e.toRingHom.comp (residue S) := by
  let S := MvPowerSeries (Fin s) D
  have hxmem (i : Fin s) : x i ∈ maximalIdeal R :=
    hx ▸ Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨f, hf, _, _, _, hres, _, hmap⟩ :=
    PowerSeriesEvaluation.evaluation D R φ hφ s x hxmem
  have : IsLocalHom f := hf
  let : Algebra S R := f.toAlgebra
  have : IsLocalHom (algebraMap S R) := hf
  have hJ : (maximalIdeal S).map f = maximalIdeal R := by
    rw [hmap, hx, sup_eq_right.mpr (map_maximalIdeal_le φ)]
  have hsurj : Function.Surjective f :=
    surjectiveOfMaximalIdealAndResidue (A := S) (B := R) hJ hres.2
  let e := RingEquiv.ofBijective (ResidueField.map f) hres
  exact ⟨f, hf, hsurj, e, (ResidueField.map_comp_residue f).symm⟩

/-- The complete regular local cover in the Cohen structure theorem. -/
theorem completeRegularCover :
    _root_.Specs.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularCover := by
  intro R _ _ _ _
  obtain ⟨s, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing (maximalIdeal R))
  change Ideal.span (Set.range x) = maximalIdeal R at hx
  by_cases hchar : ringChar (ResidueField R) = ringChar R
  · obtain ⟨σ, hσ, _⟩ := exists_coefficientField R hchar
    have hsection (a : ResidueField R) : residue R (σ a) = a :=
      RingHom.congr_fun hσ a
    have : IsLocalHom σ := isLocalHom_of_leftInverse (residue R) hsection
    have hres : Function.Bijective (ResidueField.map σ) :=
      ⟨(ResidueField.map σ).injective, fun a ↦
        ⟨residue (ResidueField R) a, (ResidueField.map_residue σ a).trans (hsection a)⟩⟩
    obtain ⟨_, hregular, hcomplete, _⟩ :=
      CompleteRegularPowerSeries.overField (ResidueField R) s
    have := hregular
    have := hcomplete
    exact ⟨MvPowerSeries (Fin s) (ResidueField R), inferInstance, hregular, hcomplete,
      surjectiveEvaluation σ hres x hx⟩
  · let p := ringChar (ResidueField R)
    have : CharP (ResidueField R) p := ringChar.charP _
    have hp : p.Prime := by
      rcases CharP.char_is_prime_or_zero (ResidueField R) p with hp | hp
      · exact hp
      · have : CharZero (ResidueField R) :=
          (CharP.ringChar_zero_iff_CharZero (R := ResidueField R)).mp hp
        have : CharZero R := RingHom.charZero (residue R)
        exact (hchar (hp.trans (ringChar.eq_zero (R := R)).symm)).elim
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨Λ, _, _, _, _, hcomplete, hgen, ⟨e⟩⟩ :=
      cohenRingExistence p hp (ResidueField R)
    have := hcomplete
    let e' : (Λ ⧸ Ideal.span {(p : Λ)}) ≃+* ResidueField R :=
      (Ideal.quotEquivOfEq hgen.symm).trans e
    obtain ⟨φ, hφ, _, hφres, _⟩ := cohenRingMap R Λ p hgen.symm e'
    have : IsLocalHom φ := hφ
    have hres : Function.Bijective (ResidueField.map φ) := by
      refine ⟨(ResidueField.map φ).injective, fun a ↦ ?_⟩
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e'.symm a)
      exact ⟨residue Λ b, by
        rw [ResidueField.map_residue, show residue R (φ b) = e' (Ideal.Quotient.mk _ b) from
          RingHom.congr_fun hφres b, hb, e'.apply_symm_apply]⟩
    have hπ : Irreducible (p : Λ) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hgen
    obtain ⟨_, hregular, hcompleteS, _⟩ :=
      CompleteRegularPowerSeries.overCompleteDVR Λ (p : Λ) hπ s
    have := hregular
    have := hcompleteS
    exact ⟨MvPowerSeries (Fin s) Λ, inferInstance, hregular, hcompleteS,
      surjectiveEvaluation φ hres x hx⟩

end CommutativeAlgebraNotes.CoefficientRings
