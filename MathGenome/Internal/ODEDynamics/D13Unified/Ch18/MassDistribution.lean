import MathGenome.Internal.ODEDynamics.D13Unified.Ch18.HausdorffDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.MassDistribution
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open Set MeasureTheory Metric
open scoped ENNReal

noncomputable section
namespace D13Unified.Ch18.MassDistribution

/-- Extend a uniform short-interval bound to arbitrary small-diameter sets.
For nonempty sets the closed hull preserves diameter exactly. No measurability
of the set being bounded is needed. -/
theorem measure_le_diameter_pow (ν : Measure ℝ) (s C δ δ₀ : ℝ)
    (hδ : 0 ≤ δ) (hδ₀ : δ < δ₀)
    (hinterval : ∀ a b : ℝ, a ≤ b → b - a < δ₀ →
      ν (Icc a b) ≤ ENNReal.ofReal C * (ENNReal.ofReal (b - a)) ^ s)
    (U : Set ℝ) (hU : ediam U ≤ ENNReal.ofReal δ) :
    ν U ≤ ENNReal.ofReal C * (ediam U) ^ s := by
  rcases eq_empty_or_nonempty U with rfl | hne
  · simp only [measure_empty]
    exact bot_le
  have hb : Bornology.IsBounded U := isBounded_iff_ediam_ne_top.mpr
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hU)
  have hlength : sSup U - sInf U ≤ δ := by
    apply (ENNReal.ofReal_le_ofReal_iff hδ).mp
    rwa [← Real.ediam_eq hb]
  have hbound := hinterval (sInf U) (sSup U)
    (Real.sInf_le_sSup U hb.bddBelow hb.bddAbove) (hlength.trans_lt hδ₀)
  rw [← Real.ediam_eq hb] at hbound
  exact (measure_mono hb.subset_Icc_sInf_sSup).trans hbound

/-- A fine countable cover has diameter cost at least the reciprocal constant. -/
theorem reciprocal_le_cover_cost (ν : Measure ℝ) (E : Set ℝ) (s C δ δ₀ : ℝ)
    (hC : 0 < C) (hmass : ν E = 1) (hδ : 0 ≤ δ) (hδ₀ : δ < δ₀)
    (hinterval : ∀ a b : ℝ, a ≤ b → b - a < δ₀ →
      ν (Icc a b) ≤ ENNReal.ofReal C * (ENNReal.ofReal (b - a)) ^ s)
    (U : ℕ → Set ℝ) (hcover : E ⊆ ⋃ i, U i)
    (hdiam : ∀ i, ediam (U i) ≤ ENNReal.ofReal δ) :
    (ENNReal.ofReal C)⁻¹ ≤ ∑' i, (ediam (U i)) ^ s := by
  have hsum : 1 ≤ ENNReal.ofReal C * ∑' i, (ediam (U i)) ^ s := by
    calc
      1 = ν E := hmass.symm
      _ ≤ ν (⋃ i, U i) := measure_mono hcover
      _ ≤ ∑' i, ν (U i) := measure_iUnion_le U
      _ ≤ ∑' i, ENNReal.ofReal C * (ediam (U i)) ^ s :=
        ENNReal.tsum_le_tsum fun i =>
          measure_le_diameter_pow ν s C δ δ₀ hδ hδ₀ hinterval (U i) (hdiam i)
      _ = ENNReal.ofReal C * ∑' i, (ediam (U i)) ^ s := ENNReal.tsum_mul_left
  exact (ENNReal.inv_le_iff_le_mul
    (fun _ => (ENNReal.ofReal_pos.mpr hC).ne')
    (fun h => (ENNReal.ofReal_ne_top h).elim)).mpr hsum

/-- The mass-distribution estimate with the source's exact normalization. -/
theorem mass_distribution :
    Specs.D13Unified.Ch18.MassDistribution.mass_distribution_type := by
  intro E s C _hs hC ν _hprob hmass hshort
  obtain ⟨δ₀, hδ₀, hinterval⟩ := hshort
  have hδ : 0 < δ₀ / 2 := half_pos hδ₀
  have hsmall : δ₀ / 2 < δ₀ := half_lt_self hδ₀
  have hcontent : (ENNReal.ofReal C)⁻¹ ≤
      D13Unified.Ch18.HausdorffDefinitions.hausdorffContent s (δ₀ / 2) E := by
    change _ ≤ ⨅ (U : ℕ → Set ℝ) (_ : E ⊆ ⋃ i, U i)
      (_ : ∀ i, ediam (U i) ≤ ENNReal.ofReal (δ₀ / 2)), ∑' i, (ediam (U i)) ^ s
    refine le_iInf fun U => le_iInf fun hcover => le_iInf fun hdiam => ?_
    exact reciprocal_le_cover_cost ν E s C (δ₀ / 2) δ₀ hC hmass hδ.le hsmall
      hinterval U hcover hdiam
  rw [ENNReal.ofReal_inv_of_pos hC]
  change (ENNReal.ofReal C)⁻¹ ≤ ⨆ (δ : ℝ) (_ : 0 < δ),
    D13Unified.Ch18.HausdorffDefinitions.hausdorffContent s δ E
  exact hcontent.trans (le_iSup_of_le (δ₀ / 2) (le_iSup_of_le hδ le_rfl))

/-- Zero outer mass outside `E` supplies the full mass needed in the estimate. -/
theorem mass_distribution_supported :
    Specs.D13Unified.Ch18.MassDistribution.mass_distribution_supported_type := by
  intro E s C hs hC ν hprob hsupport hshort
  let : IsProbabilityMeasure ν := hprob
  have hmass : ν E = 1 := by
    apply le_antisymm prob_le_one
    simpa only [measure_univ, hsupport, add_zero] using
      (measure_univ_le_add_compl (μ := ν) E)
  exact mass_distribution E s C hs hC ν hprob hmass hshort

end D13Unified.Ch18.MassDistribution
