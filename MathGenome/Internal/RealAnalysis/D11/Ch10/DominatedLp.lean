import MathGenome.Internal.RealAnalysis.D11.Ch10.LpDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch07.SubsequenceUniqueness
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.DominatedLp
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u v
noncomputable section
namespace D11.Ch10.DominatedLp
open D11.Ch10.LpDefinition D11.Ch07.ConvergenceDefinitions
open D11.Ch07.SubsequenceUniqueness D11.Ch04.AeCommonException

/-- Domination passes to the pointwise limit on one ordinary conull set. -/
private theorem limit_bound {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (F : ℕ → X → E) (f : X → E) (g : X → ℝ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ g x)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ g x := by
  filter_upwards [ae_all_iff.mpr hb, hl] with x hx hlim
  exact le_of_tendsto' hlim.norm hx

/-- DCT for the p-power errors, followed by continuity of the positive root. -/
theorem dominated_ae : Specs.D11.Ch10.DominatedLp.dominated_ae := by
  intro X E _ _ _ _ _ μ p F f g hp hFm hfm hg hg0 hbound hlim
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hb : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ g x :=
    fun n => (almostEverywhere_iff_native μ _).mp (hbound n)
  have hl : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
    (almostEverywhere_iff_native μ _).mp hlim
  have hfb := limit_bound μ F f g hb hl
  have hgm : Measurable g := hg.1
  have hgi : MemLp g (ENNReal.ofReal p) μ := (rawLp_iff_memLp μ p g hp).mp hg |>.2
  have hFi : ∀ n, MemLp (F n) (ENNReal.ofReal p) μ :=
    fun n => hgi.mono' (hFm n).aestronglyMeasurable (hb n)
  have hfi : MemLp f (ENNReal.ofReal p) μ :=
    hgi.mono' hfm.aestronglyMeasurable hfb
  refine ⟨fun n => (rawLp_iff_memLp μ p (F n) hp).mpr ⟨hFm n, hFi n⟩,
    (rawLp_iff_memLp μ p f hp).mpr ⟨hfm, hfi⟩,
    fun n => (rawLp_iff_memLp μ p _ hp).mpr ⟨(hFm n).sub hfm, (hFi n).sub hfi⟩, ?_⟩
  let B : X → ℝ≥0∞ := fun x => ENNReal.ofReal ((2 : ℝ) ^ p) * ENNReal.ofReal (g x ^ p)
  have hgp : Measurable (fun x => ENNReal.ofReal (g x ^ p)) := by fun_prop
  have hBfin : (∫⁻ x, B x ∂μ) ≠ ∞ := by
    dsimp [B]
    rw [lintegral_const_mul _ hgp]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    have h := (rawLp_iff_finite_integral μ p g hp).mp hg |>.2
    change D11.Ch05.NonnegativeIntegral.nonnegativeIntegral μ
      (fun x => ENNReal.ofReal (‖g x‖ ^ p)) < ∞ at h
    rw [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral] at h
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using h.ne
  have herror : ∀ n, (fun x => ENNReal.ofReal (‖F n x - f x‖ ^ p)) ≤ᵐ[μ] B := by
    intro n
    filter_upwards [hb n, hfb] with x hx hfx
    have he : ‖F n x - f x‖ ≤ 2 * g x :=
      (norm_sub_le _ _).trans (by linarith)
    calc
      ENNReal.ofReal (‖F n x - f x‖ ^ p) ≤ ENNReal.ofReal ((2 * g x) ^ p) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) he hp0.le)
      _ = B x := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (hg0 x),
          ENNReal.ofReal_mul (by positivity)]
  have hpowlim : ∀ᵐ x ∂μ, Tendsto
      (fun n => ENNReal.ofReal (‖F n x - f x‖ ^ p)) atTop (𝓝 (0 : ℝ≥0∞)) := by
    filter_upwards [hl] with x hx
    have h := (hx.sub (tendsto_const_nhds (x := f x))).norm.rpow_const (Or.inr hp0.le)
    simpa [Function.comp_def, Real.zero_rpow hp0.ne'] using (ENNReal.continuous_ofReal.tendsto _).comp h
  have hInt : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (‖F n x - f x‖ ^ p) ∂μ)
      atTop (𝓝 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence B
      (fun n => by fun_prop) herror hBfin hpowlim
  have hroot := (ENNReal.continuous_rpow_const (y := 1 / p)).tendsto (0 : ℝ≥0∞) |>.comp hInt
  simpa only [Function.comp_def, powerNorm_formula μ p _ hp,
    ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)] using hroot

/-- The global in-measure case uses the subsequence principle on arbitrary spaces. -/
theorem dominated_inMeasure : Specs.D11.Ch10.DominatedLp.dominated_inMeasure := by
  intro X E _ _ _ _ _ μ p F f g hp hFm hfm hg hg0 hbound hlim
  obtain ⟨ns, _, hns⟩ := exists_ae_subsequence μ F f hlim
  have hsub := dominated_ae μ p (fun n => F (ns n)) f g hp
    (fun n => hFm (ns n)) hfm hg hg0 (fun n => hbound (ns n)) hns
  have hgi := (rawLp_iff_memLp μ p g hp).mp hg |>.2
  have hFi : ∀ n, F n ∈ rawLp μ p := fun n =>
    (rawLp_iff_memLp μ p (F n) hp).mpr ⟨hFm n,
      hgi.mono' (hFm n).aestronglyMeasurable
        ((almostEverywhere_iff_native μ _).mp (hbound n))⟩
  refine ⟨hFi, hsub.2.1, fun n => (rawLp_iff_memLp μ p _ hp).mpr
    ⟨(hFm n).sub hfm, ((rawLp_iff_memLp μ p _ hp).mp (hFi n)).2.sub
      ((rawLp_iff_memLp μ p f hp).mp hsub.2.1).2⟩, ?_⟩
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hs : inMeasureConverges μ (fun n => F (ns n)) f := fun ε hε =>
    (hlim ε hε).comp hns
  obtain ⟨ms, _, hms⟩ := exists_ae_subsequence μ _ f hs
  exact ⟨ms, (dominated_ae μ p (fun n => F (ns (ms n))) f g hp
    (fun n => hFm (ns (ms n))) hfm hg hg0
    (fun n => hbound (ns (ms n))) hms).2.2.2⟩

end D11.Ch10.DominatedLp
