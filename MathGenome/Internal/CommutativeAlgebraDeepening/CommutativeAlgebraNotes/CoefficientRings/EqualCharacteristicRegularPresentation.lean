import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.EqualCharacteristicRegularPresentation
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.AdicFiniteGeneration
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CoefficientField
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.PowerSeriesEvaluation
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

namespace CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing
open Specs.CommutativeAlgebraNotes.CoefficientRings.EqualCharacteristicRegularPresentation
  (Presentation PresentationOfGenerators)

/-- Evaluation at generators of the maximal ideal indexed by the Krull
dimension gives an isomorphism extending the chosen coefficient section. -/
theorem equalCharacteristicRegularPresentationOfGenerators : PresentationOfGenerators := by
  intro R _ _ _ d hd σ hσ x hx
  let k := ResidueField R
  let S := MvPowerSeries (Fin d) k
  have hsection (a : k) : residue R (σ a) = a := RingHom.congr_fun hσ a
  have : IsLocalHom σ := ⟨fun a ha => by
    simpa only [hsection] using ha.map (residue R)⟩
  have hσres : Function.Bijective (ResidueField.map σ) := by
    refine ⟨(ResidueField.map σ).injective, fun a => ⟨residue k a, ?_⟩⟩
    rw [ResidueField.map_residue, hsection]
  have hxmem (i : Fin d) : x i ∈ maximalIdeal R :=
    hx ▸ Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨F, hF, _, hC, hX, hFres, hres, hmap⟩ :=
    PowerSeriesEvaluation.evaluation k R σ hσres d x hxmem
  obtain ⟨hdom, hreg, hcomplete, _, hdim, _, _, _⟩ :=
    CompleteRegularPowerSeries.overField k d
  have : IsDomain S := hdom
  have : IsRegularLocalRing S := hreg
  have : IsAdicComplete (maximalIdeal S) S := hcomplete
  have hmax : (maximalIdeal S).map F = maximalIdeal R := by
    rw [hmap, maximalIdeal_eq_bot, Ideal.map_bot, bot_sup_eq, hx]
  have hsurj : Function.Surjective F := by
    let : Algebra S R := F.toAlgebra
    exact surjectiveOfMaximalIdealAndResidue (A := S) (B := R) hmax hFres.2
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero F]
    intro a ha
    by_contra hne
    have hdrop := ringKrullDim_succ_le_of_surjective F hsurj
      (mem_nonZeroDivisors_iff_ne_zero.mpr hne) ha
    rw [hd, hdim] at hdrop
    exact (not_le_of_gt (by exact_mod_cast Nat.lt_succ_self d)) hdrop
  refine ⟨RingEquiv.ofBijective F ⟨hinj, hsurj⟩, hC, hX, fun f => ?_⟩
  change residue R (F f) = MvPowerSeries.constantCoeff f
  simpa only [ResidueField.map_residue, hsection] using hres f

/-- A complete regular local ring of equal characteristic has a power-series
presentation over its residue field. -/
theorem equalCharacteristicRegularPresentation : Presentation := by
  intro R _ _ _ d hd hchar
  obtain ⟨σ, hσ, _⟩ := exists_coefficientField R hchar
  have hfg := IsNoetherian.noetherian (maximalIdeal R : Submodule R R)
  obtain ⟨s, hcard, hspan⟩ := hfg.exists_span_finset_card_eq_spanFinrank
  have hsize := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [hd] at hsize
  have hsd : s.card = d := hcard.trans (by exact_mod_cast hsize)
  let index := (Finset.equivFinOfCardEq hsd).symm
  let x : Fin d → R := Subtype.val ∘ index
  have hxrange : Set.range x = (s : Set R) := by
    change Set.range (Subtype.val ∘ index) = (s : Set R)
    rw [index.surjective.range_comp]
    exact Subtype.range_coe_subtype
  have hx : Ideal.span (Set.range x) = maximalIdeal R := by
    rw [hxrange]
    exact hspan
  obtain ⟨e, hC, _, hres⟩ := equalCharacteristicRegularPresentationOfGenerators R d hd σ hσ x hx
  exact ⟨σ, hσ, e, hC, hres⟩

end CommutativeAlgebraNotes.CoefficientRings
