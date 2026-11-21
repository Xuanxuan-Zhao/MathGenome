import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.AbsoluteSeries
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import MathGenome.Internal.RealAnalysis.D11.Ch06.DominatedConvergence
import MathGenome.Internal.RealAnalysis.D11.Ch06.LinearityOrder

/-! Absolute series under the integral (paper.tex:1949–1973).
The sum of pointwise norms has finite nonnegative integral. Its real finite
version dominates the partial sums almost everywhere. Dominated convergence
then gives absolute-integral convergence. Measurability of the exact zero-reset
sum is proved on the original sigma-algebra, with no completion of the space. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u
noncomputable section
namespace D11.Ch06.AbsoluteSeries
open ScalarIntegral
open D11.Ch05.NonnegativeIntegral
open D11.Ch04.AeCommonException

def absoluteSeriesSum {X : Type u} {𝕜 : Type} [RCLike 𝕜]
    (F : ℕ → X → 𝕜) (x : X) : 𝕜 := by
  classical
  exact if Summable (fun n => ‖F n x‖) then ∑' n, F n x else 0

theorem measurable_absoluteSeriesSum {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {F : ℕ → X → 𝕜} (hF : ∀ n, Measurable (F n)) :
    Measurable (absoluteSeriesSum F) := by
  have hm : Measurable (fun x => ∑' n, ‖F n x‖ₑ) :=
    Measurable.tsum (fun n => (hF n).enorm)
  have hs : MeasurableSet {x | Summable (fun n => ‖F n x‖)} := by
    simp_rw [← tsum_enorm_ne_top_iff_summable_norm]
    exact (measurableSet_eq_fun hm measurable_const).compl
  exact (Measurable.tsum hF).piecewise hs measurable_const

theorem absolute_series_interchange :
    Specs.D11.Ch06.AbsoluteSeries.absolute_series_interchange := by
  intro X 𝕜 _ _ _ _ μ F hFm hfin
  classical
  change (∑' n, nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖F n x‖)) < ∞ at hfin
  let h : X → ℝ≥0∞ := fun x => ∑' n, ‖F n x‖ₑ
  have hm : Measurable h := Measurable.tsum (fun n => (hFm n).enorm)
  have hi : (∫⁻ x, h x ∂μ) < ∞ := by
    change (∫⁻ x, ∑' n, ‖F n x‖ₑ ∂μ) < ∞
    rw [lintegral_tsum (fun n => (hFm n).enorm.aemeasurable)]
    simpa only [integral_eq_lintegral, ofReal_norm] using hfin
  have hae : ∀ᵐ x ∂μ, h x < ∞ := ae_lt_top hm hi.ne
  have hsae : ∀ᵐ x ∂μ, Summable (fun n => ‖F n x‖) :=
    hae.mono (fun x hx => tsum_enorm_ne_top_iff_summable_norm.mp hx.ne)
  have hfm : Measurable (absoluteSeriesSum F) := measurable_absoluteSeriesSum hFm
  let g : X → ℝ := fun x => (h x).toReal
  have hgi : scalarIntegrable μ g := (scalarIntegrable_iff μ g).mpr
    ⟨hm.ennreal_toReal, integrable_toReal_of_lintegral_ne_top hm.aemeasurable hi.ne⟩
  have hg_eq (x : X) : g x = ∑' n, ‖F n x‖ := by
    dsimp [g, h]
    rw [ENNReal.tsum_toReal_eq (fun n => enorm_ne_top)]
    simp
  let S : ℕ → X → 𝕜 := fun N x => ∑ n ∈ Finset.range N, F n x
  have hSm : ∀ N, Measurable (S N) := fun N =>
    Finset.measurable_sum _ (fun n _ => hFm n)
  have hbound : ∀ N, almostEverywhere μ (fun x => ‖S N x‖ ≤ g x) := by
    intro N
    apply (almostEverywhere_iff_native μ _).mpr
    filter_upwards [hsae] with x hx
    rw [hg_eq]
    exact (norm_sum_le _ _).trans (hx.sum_le_tsum _ (fun n _ => norm_nonneg _))
  have hlim : almostEverywhere μ
      (fun x => Tendsto (fun N => S N x) atTop (𝓝 (absoluteSeriesSum F x))) := by
    apply (almostEverywhere_iff_native μ _).mpr
    filter_upwards [hsae] with x hx
    simpa only [absoluteSeriesSum, ite_eq_left hx] using hx.of_norm.tendsto_sum_tsum_nat
  obtain ⟨hSi, hfi, herri, hL1, hInt⟩ :=
    DominatedConvergence.dominated_convergence μ S (absoluteSeriesSum F) g
      hSm hfm hgi (fun x => ENNReal.toReal_nonneg) hbound hlim
  have hFi : ∀ n, scalarIntegrable μ (F n) := by
    intro n
    refine ⟨hFm n, lt_of_le_of_lt
      (ENNReal.le_tsum (f := fun n => nonnegativeIntegral μ
        (fun x => ENNReal.ofReal ‖F n x‖)) n) hfin⟩
  have hsum : HasSum (fun n => scalarIntegral μ (F n) (hFi n))
      (scalarIntegral μ (absoluteSeriesSum F) hfi) := by
    change HasSum (fun n => ∫ x, F n x ∂μ) (∫ x, absoluteSeriesSum F x ∂μ)
    have heq : (fun x => absoluteSeriesSum F x) =ᵐ[μ] (fun x => ∑' n, F n x) := by
      filter_upwards [hsae] with x hx
      simp only [absoluteSeriesSum, ite_eq_left hx]
    rw [integral_congr_ae heq]
    apply hasSum_integral_of_summable_integral_norm
    · exact fun n => ((scalarIntegrable_iff μ (F n)).mp (hFi n)).2
    · have hs := ENNReal.summable_toReal hfin.ne
      convert hs using 1
      funext n
      simp only [integral_eq_lintegral, ofReal_norm]
      exact integral_norm_eq_lintegral_enorm (hFm n).aestronglyMeasurable
  have hnorm : Summable (fun n => ‖scalarIntegral μ (F n) (hFi n)‖) := by
    have hs := ENNReal.summable_toReal hfin.ne
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n =>
      LinearityOrder.absolute_value_bound μ (F n) (hFi n)) hs
  refine ⟨(almostEverywhere_iff_native μ _).mpr hsae, hfm,
    hFi, hfi, hSi, herri, ?_, hL1, hnorm, hsum, hsum.tsum_eq.symm⟩
  apply (almostEverywhere_iff_native μ _).mpr
  filter_upwards [hsae] with x hx
  change HasSum (fun n => F n x) (absoluteSeriesSum F x)
  simpa only [absoluteSeriesSum, ite_eq_left hx] using hx.of_norm.hasSum

end D11.Ch06.AbsoluteSeries
