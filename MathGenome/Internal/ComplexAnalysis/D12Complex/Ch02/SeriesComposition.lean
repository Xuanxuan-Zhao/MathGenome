import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.SeriesComposition
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.SeriesAlgebra
import Mathlib.Analysis.Analytic.Composition

open Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace D12Complex.SeriesComposition

/- The canonical coefficient definitions live in the independent Spec, so
other Specs may reuse them. These exports verify their expected values. -/
namespace Definitions

abbrev substitutionTerm : Specs.D12Complex.Ch02.SeriesComposition.substitutionTerm_type :=
  @_root_.D12Complex.SeriesComposition.substitutionTerm

abbrev substitutedCoefficients : Specs.D12Complex.Ch02.SeriesComposition.substitutedCoefficients_type :=
  _root_.D12Complex.SeriesComposition.substitutedCoefficients

abbrev innerMajorant : Specs.D12Complex.Ch02.SeriesComposition.innerMajorant_type :=
  _root_.D12Complex.SeriesComposition.innerMajorant

end Definitions

/-- The scalar contribution of each ordered composition is precisely the
coefficient in Mathlib's formal multilinear substitution. -/
theorem compAlongComposition_one (c d : ℕ → ℂ) {n : ℕ} (k : Composition n) :
    (FormalMultilinearSeries.ofScalars ℂ d).compAlongComposition
      (FormalMultilinearSeries.ofScalars ℂ c) k (1 : Fin n → ℂ) =
        substitutionTerm c d k := by
  rw [FormalMultilinearSeries.compAlongComposition_apply]
  simp only [FormalMultilinearSeries.ofScalars, smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, smul_eq_mul, List.prod_ofFn]
  unfold substitutionTerm
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp [FormalMultilinearSeries.applyComposition, FormalMultilinearSeries.ofScalars,
    Function.comp_def]

theorem comp_scalar (c d : ℕ → ℂ) :
    (FormalMultilinearSeries.ofScalars ℂ d).comp (FormalMultilinearSeries.ofScalars ℂ c) =
      FormalMultilinearSeries.ofScalars ℂ (substitutedCoefficients c d) := by
  apply FormalMultilinearSeries.ext
  intro n
  apply ContinuousMultilinearMap.ext
  intro v
  rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  congr 1
  rw [FormalMultilinearSeries.coeff_ofScalars]
  simp only [FormalMultilinearSeries.coeff, FormalMultilinearSeries.comp,
    sum_apply, compAlongComposition_one, substitutedCoefficients]

/-- An absolutely summable expansion exists on a positive disk; this is a
statement about the individual substituted terms before collection by degree. -/
theorem expanded_majorant_exists (c d : ℕ → ℂ)
    (hc : 0 < powerSeriesRadius c) (hd : 0 < powerSeriesRadius d) :
    ∃ R : ℝ, 0 < R ∧
      Summable (fun i : Σ n, Composition n => ‖substitutionTerm c d i.2‖ * R ^ i.1) := by
  rw [PowerSeriesRadius.radius_eq_formal] at hc hd
  obtain ⟨R, hR, hs⟩ := (FormalMultilinearSeries.ofScalars ℂ d).comp_summable_nnreal
    (FormalMultilinearSeries.ofScalars ℂ c) hd hc
  refine ⟨R, hR, ?_⟩
  apply (NNReal.summable_coe.mpr hs).of_nonneg_of_le (fun _ => by positivity)
  intro i
  simp only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm]
  gcongr
  rw [← compAlongComposition_one]
  simpa using ((FormalMultilinearSeries.ofScalars ℂ d).compAlongComposition
    (FormalMultilinearSeries.ofScalars ℂ c) i.2).le_opNorm (1 : Fin i.1 → ℂ)

private def majorantCoefficients (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (‖c n‖ : ℂ)

private theorem majorant_radius (c : ℕ → ℂ) :
    powerSeriesRadius c ≤ powerSeriesRadius (majorantCoefficients c) := by
  simp only [PowerSeriesRadius.radius_eq_formal]
  apply FormalMultilinearSeries.radius_le_of_le
  intro n
  simp only [FormalMultilinearSeries.ofScalars_norm, majorantCoefficients]
  split_ifs <;> simp

private theorem majorant_sum_real (c : ℕ → ℂ) (r : ℝ) :
    PowerSeriesCalculus.seriesSum (majorantCoefficients c) 0 (r : ℂ) =
      (innerMajorant c r : ℂ) := by
  simp only [PowerSeriesCalculus.seriesSum, sub_zero, innerMajorant,
    Complex.ofReal_tsum, majorantCoefficients]
  apply tsum_congr
  intro n
  split_ifs <;> simp

private theorem majorant_continuous (c : ℕ → ℂ) (hc : 0 < powerSeriesRadius c) :
    ContinuousAt (innerMajorant c) 0 := by
  have hp : 0 < (FormalMultilinearSeries.ofScalars ℂ (majorantCoefficients c)).radius := by
    rw [← PowerSeriesRadius.radius_eq_formal]
    exact hc.trans_le (majorant_radius c)
  have hh := (FormalMultilinearSeries.ofScalars ℂ (majorantCoefficients c)).hasFPowerSeriesOnBall hp
  have hcplx : ContinuousAt (PowerSeriesCalculus.seriesSum (majorantCoefficients c) 0) 0 := by
    have heq : (FormalMultilinearSeries.ofScalars ℂ (majorantCoefficients c)).sum =
        PowerSeriesCalculus.seriesSum (majorantCoefficients c) 0 := by
      funext z
      simp [FormalMultilinearSeries.sum,
        PowerSeriesCalculus.seriesSum, smul_eq_mul, mul_comm]
    rw [← heq]
    exact hh.hasFPowerSeriesAt.continuousAt
  have h : ContinuousAt (fun r : ℝ =>
      (PowerSeriesCalculus.seriesSum (majorantCoefficients c) 0 (r : ℂ)).re) 0 :=
    Complex.continuous_re.continuousAt.comp
      (hcplx.comp (f := Complex.ofReal) (x := (0 : ℝ)) (Complex.continuous_ofReal.continuousAt :
        ContinuousAt (fun r : ℝ => (r : ℂ)) 0))
  simpa only [Function.comp_def, majorant_sum_real, Complex.ofReal_re] using h

/-- Formal substitution of two actual local convergent series, including
absolute uniform convergence before and after regrouping by degree. -/
theorem composition : Specs.D12Complex.Ch02.SeriesComposition.composition_type := by
  intro F G a b c d hab hF hG
  have hf : HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ c) a := by
    rw [hasFPowerSeriesAt_iff']
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using hF
  have hg : HasFPowerSeriesAt G (FormalMultilinearSeries.ofScalars ℂ d) (F a) := by
    rw [hab, hasFPowerSeriesAt_iff']
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using hG
  have hc : 0 < powerSeriesRadius c := by
    rw [PowerSeriesRadius.radius_eq_formal]; exact hf.radius_pos
  have hd : 0 < powerSeriesRadius d := by
    rw [PowerSeriesRadius.radius_eq_formal]; exact hg.radius_pos
  obtain ⟨ρ, hρ⟩ := hg.comp hf
  rw [comp_scalar] at hρ
  obtain ⟨U, hU, hUρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_min hρ.r_pos hc)
  have hUreal : (0 : ℝ) < U := by exact_mod_cast hU
  obtain ⟨v, hv, hvd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hd
  have hvreal : (0 : ℝ) < v := by exact_mod_cast hv
  have hzero : innerMajorant c 0 = 0 := by
    unfold innerMajorant
    calc
      _ = ∑' _n : ℕ, (0 : ℝ) := by
        apply tsum_congr
        intro n
        by_cases hn : n = 0 <;> simp [hn]
      _ = 0 := tsum_zero
  have hH : ∀ᶠ t in 𝓝 (0 : ℝ), innerMajorant c t < (v : ℝ) := by
    exact (majorant_continuous c hc).eventually (p := fun y : ℝ => y < (v : ℝ))
      (by simpa only [hzero] using (gt_mem_nhds hvreal))
  obtain ⟨δ, hδ, hδall⟩ := Metric.eventually_nhds_iff.mp hH
  obtain ⟨R, hR, hRs⟩ := expanded_majorant_exists c d hc hd
  obtain ⟨r, hr, hrlt⟩ := exists_between (lt_min hδ (lt_min hR hUreal))
  have hrδ : r < δ := hrlt.trans_le (min_le_left _ _)
  have hrR : r < R := hrlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrU : r < U := hrlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hrUe : ENNReal.ofReal r < (U : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hrU, hUreal⟩
  have hrc : ENNReal.ofReal r < powerSeriesRadius c :=
    hrUe.trans (hUρ.trans_le (min_le_right _ _))
  have hrρ : ENNReal.ofReal r < ρ := hrUe.trans (hUρ.trans_le (min_le_left _ _))
  have hsmall : ENNReal.ofReal (innerMajorant c r) < powerSeriesRadius d := by
    apply lt_trans _ hvd
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_lt_ofReal_iff'.mpr
      ⟨hδall (by simpa [Real.dist_eq, abs_of_pos hr] using hrδ), hvreal⟩
  have hins : Summable (fun n => if n = 0 then 0 else ‖c n‖ * r ^ n) := by
    apply (PowerSeriesRadius.uniform_closedDisk c a r hr.le hrc).1.of_nonneg_of_le
      (fun n => by split_ifs <;> positivity)
    intro n
    split_ifs <;> first | positivity | exact le_rfl
  have hm : Summable (fun i : Σ n, Composition n => ‖substitutionTerm c d i.2‖ * r ^ i.1) := by
    apply hRs.of_nonneg_of_le (fun _ => by positivity)
    intro i
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrR.le i.1) (norm_nonneg _)
  have hb (i : Σ n, Composition n) (z : ℂ) (hz : z ∈ Metric.closedBall a r) :
      ‖substitutionTerm c d i.2 * (z - a) ^ i.1‖ ≤
        ‖substitutionTerm c d i.2‖ * r ^ i.1 := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (by simpa [dist_eq_norm] using hz) _) (norm_nonneg _)
  have hgrouped (z : ℂ) (hz : z ∈ Metric.closedBall a r) :
      HasSum (fun n => substitutedCoefficients c d n * (z - a) ^ n) (G (F z)) := by
    have he : z - a ∈ Metric.eball (0 : ℂ) ρ := by
      rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
      apply lt_of_le_of_lt _ hrρ
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      simpa [dist_eq_norm] using hz
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using hρ.hasSum he
  have hexpanded (z : ℂ) (hz : z ∈ Metric.closedBall a r) :
      HasSum (fun i : Σ n, Composition n => substitutionTerm c d i.2 * (z - a) ^ i.1)
        (G (F z)) := by
    apply (hgrouped z hz).sigma_of_hasSum
    · intro n
      simpa only [substitutedCoefficients, Finset.sum_mul] using
        hasSum_fintype (fun k : Composition n => substitutionTerm c d k * (z - a) ^ n)
    · exact (hm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hb i z hz)).of_norm
  have hgm : Summable (fun n => ‖substitutedCoefficients c d n‖ * r ^ n) := by
    have hs : Summable (fun n => ∑ k : Composition n, ‖substitutionTerm c d k‖ * r ^ n) := by
      simpa only [tsum_fintype] using hm.sigma
    apply hs.of_nonneg_of_le (fun _ => by positivity)
    intro n
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hr.le _)
  have hgb (n : ℕ) (z : ℂ) (hz : z ∈ Metric.closedBall a r) :
      ‖substitutedCoefficients c d n * (z - a) ^ n‖ ≤
        ‖substitutedCoefficients c d n‖ * r ^ n := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (by simpa [dist_eq_norm] using hz) _) (norm_nonneg _)
  refine ⟨r, hr, hins, hsmall, hm, hexpanded, ?_, ?_, hgrouped, hgm, ?_, ?_⟩
  · exact (tendstoUniformlyOn_tsum hm hb).congr_right (fun z hz => (hexpanded z hz).tsum_eq)
  · exact tendstoUniformlyOn_tsum hm (by simpa only [norm_norm] using hb)
  · exact (tendstoUniformlyOn_tsum_nat hgm hgb).congr_right (fun z hz => (hgrouped z hz).tsum_eq)
  · exact tendstoUniformlyOn_tsum_nat hgm (by simpa only [norm_norm] using hgb)

end D12Complex.SeriesComposition
