import MathGenome.Internal.LinearPDE.P201.Hyperbolic.WaveMultipliers
import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.EnergyWaveCauchy
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity

noncomputable section
open MeasureTheory Set Filter Topology
open P201Specs.Wave (WholeL2 WholeH1 WaveOperators WaveFamilyLaws)
open P201Specs.Wave.Cauchy
namespace P201.Wave.Cauchy

/-- A strongly continuous family with a continuous operator-norm majorant
has jointly continuous evaluation. No operator-norm continuity is assumed. -/
theorem continuous_family_apply {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : ℝ → E →L[𝕜] F) (B : ℝ → ℝ) (hB : Continuous B)
    (hbound : ∀ t, ‖A t‖ ≤ B t) (hA : ∀ v, Continuous (fun t => A t v)) :
    Continuous (fun p : ℝ × E => A p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  change Tendsto (fun q : ℝ × E => A q.1 q.2) (𝓝 p) (𝓝 (A p.1 p.2))
  have hz : Tendsto (fun q : ℝ × E => A q.1 (q.2 - p.2)) (𝓝 p) (𝓝 0) := by
    apply squeeze_zero_norm (fun q : ℝ × E =>
      (A q.1).le_opNorm (q.2 - p.2) |>.trans
        (mul_le_mul_of_nonneg_right (hbound q.1) (norm_nonneg _)))
    have hb : Tendsto (fun q : ℝ × E => B q.1) (𝓝 p) (𝓝 (B p.1)) :=
      (hB.comp continuous_fst).continuousAt
    have hv : Tendsto (fun q : ℝ × E => ‖q.2 - p.2‖) (𝓝 p) (𝓝 0) := by
      simpa using ((continuous_snd.sub (continuous_const (y := p.2))).norm.continuousAt (x := p)).tendsto
    simpa using hb.mul hv
  have hfixed : Tendsto (fun q : ℝ × E => A q.1 p.2) (𝓝 p) (𝓝 (A p.1 p.2)) :=
    (hA p.2).continuousAt.tendsto.comp continuous_fst.continuousAt.tendsto
  have h := hz.add hfixed
  simpa only [map_sub, sub_add_cancel, zero_add] using h

/-- Initial values require no representative regularity of the forcing. -/
theorem duhamelInitial : P201Specs.Wave.Cauchy.duhamelInitialStatement := by
  intro n 𝕜 _ c κ W hW g h f
  rcases hW with ⟨_, _, _, _, _, _, _, _, _, _, _, hC0, hC1, hS, hD⟩
  constructor
  · simp [displacement, hC1, hS]
  · simp [velocity, hC0, hD]

/-- Time regularity and strong derivative of the homogeneous formula. -/
theorem homogeneousRegularity : P201Specs.Wave.Cauchy.homogeneousRegularityStatement := by
  intro n 𝕜 _ c κ W hW g h
  have hi := duhamelInitial c κ W hW g h 0
  rcases hW with ⟨_, _, _, _, _, hC0cont, hC1cont, hScont, hDcont,
    hCderiv, hSderiv, _, _, _, _⟩
  have hd (t : ℝ) : displacement W g h 0 t = W.C1 t g + W.S t h := by
    simp [displacement]
  have hv (t : ℝ) : velocity W g h 0 t = W.D t g + W.C0 t h := by
    simp [velocity]
  refine ⟨?_, ?_, ?_, hi⟩
  · change Continuous (fun t => displacement W g h 0 t)
    simp_rw [hd]
    exact (hC1cont g).add (hScont h)
  · change Continuous (fun t => velocity W g h 0 t)
    simp_rw [hv]
    exact (hDcont g).add (hC0cont h)
  · intro t
    simpa [displacement, velocity, map_add] using! (hCderiv t g).add (hSderiv t h)

/-- Bochner integrability for every original forcing on every finite interval. -/
theorem duhamelIntegrable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W) (f : ℝ → WholeL2 n 𝕜)
    (hf : LocallyIntegrableForcing f) (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun s => W.S (t - s) (f s)) (Icc 0 t) ∧
    IntegrableOn (fun s => W.C0 (t - s) (f s)) (Icc 0 t) := by
  rcases hW with ⟨_, _, _, _, hB, hC0, _, hS, _, _, _, _, _, _, _⟩
  have hSjoint := continuous_family_apply W.S
    (fun r => Real.sqrt (r ^ 2 + c⁻¹ ^ 2)) (by fun_prop)
    (fun r => (hB r).2.2.1) hS
  have hCjoint := continuous_family_apply W.C0 (fun _ => 1) continuous_const
    (fun r => (hB r).1) hC0
  have hm := (((continuous_const (y := t)).sub continuous_id).aestronglyMeasurable
    (μ := volume.restrict (Icc 0 t))).prodMk (hf t ht).aestronglyMeasurable
  constructor
  · apply ((hf t ht).norm.const_mul (Real.sqrt (t ^ 2 + c⁻¹ ^ 2))).mono'
      (hSjoint.comp_aestronglyMeasurable hm)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    refine ((W.S (t - s)).le_opNorm (f s)).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (hB (t - s)).2.2.1.trans
    apply Real.sqrt_le_sqrt
    have hts : 0 ≤ t - s := sub_nonneg.mpr hs.2
    nlinarith [hs.1]
  · apply (hf t ht).norm.mono' (hCjoint.comp_aestronglyMeasurable hm)
    filter_upwards [] with s
    calc
      ‖W.C0 (t - s) (f s)‖ ≤ ‖W.C0 (t - s)‖ * ‖f s‖ := (W.C0 _).le_opNorm _
      _ ≤ 1 * ‖f s‖ := mul_le_mul_of_nonneg_right (hB _).1 (norm_nonneg _)
      _ = ‖f s‖ := one_mul _

/-- A fixed-interval representation of the causal sine convolution. -/
def sineConvolutionOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (W : WaveOperators n 𝕜) (T : ℝ) (f : ℝ → WholeL2 n 𝕜) (t : ℝ) : WholeH1 n 𝕜 :=
  ∫ s in Icc 0 T, W.S (max (t - s) 0) (f s)

/-- On a finite positive interval the fixed-interval representation agrees
with the actual Duhamel term, because S(0)=0. -/
theorem sineConvolutionOn_eq {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (W : WaveOperators n 𝕜) (hS : W.S 0 = 0) (T : ℝ)
    (f : ℝ → WholeL2 n 𝕜) (t : ℝ) (ht : t ∈ Icc 0 T) :
    sineConvolutionOn W T f t = ∫ s in Icc 0 t, W.S (t - s) (f s) := by
  unfold sineConvolutionOn
  calc
    (∫ s in Icc 0 T, W.S (max (t - s) 0) (f s)) =
        ∫ s in Icc 0 T, (Icc 0 t).indicator (fun s => W.S (t - s) (f s)) s := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      by_cases hst : s ≤ t
      · rw [max_eq_left (sub_nonneg.mpr hst), indicator_of_mem (show s ∈ Icc 0 t from ⟨hs.1, hst⟩)]
      · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hst)), hS,
          zero_apply, indicator_of_notMem (by simp [hst])]
    _ = ∫ s in Icc 0 t, W.S (t - s) (f s) := by
      rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
      rw [inter_eq_left.mpr (Icc_subset_Icc_right ht.2)]

/-- Full H¹ continuity of the causal convolution, with only local L¹ forcing. -/
theorem sineConvolutionOn_continuousOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → WholeL2 n 𝕜) (hf : IntegrableOn f (Icc 0 T)) :
    ContinuousOn (sineConvolutionOn W T f) (Icc 0 T) := by
  rcases hW with ⟨_, _, _, _, hB, _, _, hS, _, _, _, _, _, _, _⟩
  have hSjoint := continuous_family_apply W.S
    (fun r => Real.sqrt (r ^ 2 + c⁻¹ ^ 2)) (by fun_prop)
    (fun r => (hB r).2.2.1) hS
  apply continuousOn_of_dominated (bound := fun s => Real.sqrt (T ^ 2 + c⁻¹ ^ 2) * ‖f s‖)
  · intro t ht
    exact hSjoint.comp_aestronglyMeasurable
      (((((continuous_const (y := t)).sub continuous_id).max continuous_const).aestronglyMeasurable
        (μ := volume.restrict (Icc 0 T))).prodMk hf.aestronglyMeasurable)
  · intro t ht
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    refine ((W.S (max (t - s) 0)).le_opNorm (f s)).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (hB _).2.2.1.trans
    apply Real.sqrt_le_sqrt
    have hm0 : 0 ≤ max (t - s) 0 := le_max_right _ _
    have hmT : max (t - s) 0 ≤ T := max_le (by linarith [ht.2, hs.1]) hT
    nlinarith
  · exact hf.norm.const_mul _
  · filter_upwards [] with s
    exact ((hS (f s)).comp (((continuous_id.sub continuous_const).max continuous_const))).continuousOn

/-- Full H¹ continuity on the half-line, including the zero-time limit. -/
theorem sineConvolution_continuousOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W) (f : ℝ → WholeL2 n 𝕜)
    (hf : LocallyIntegrableForcing f) :
    ContinuousOn (fun t => ∫ s in Icc 0 t, W.S (t - s) (f s)) (Ici 0) := by
  have hS : W.S 0 = 0 := hW.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro t ht
  change 0 ≤ t at ht
  have hT : 0 ≤ t + 1 := by linarith [ht]
  have hc := sineConvolutionOn_continuousOn c κ W hW (t + 1) hT f (hf _ hT)
  have hmem : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
    have hright : Iic (t + 1) ∈ 𝓝[Ici (0 : ℝ)] t :=
      mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith))
    simpa only [Ici_inter_Iic] using inter_mem self_mem_nhdsWithin hright
  have hct := (hc t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin hmem
  apply hct.congr_of_eventuallyEq
  · filter_upwards [hmem] with r hr
    exact (sineConvolutionOn_eq W hS (t + 1) f r hr).symm
  · exact (sineConvolutionOn_eq W hS (t + 1) f t ⟨ht, by linarith⟩).symm

/-- The causal cosine kernel is only discontinuous at t=s. -/
def causalCosine {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (W : WaveOperators n 𝕜) (f : ℝ → WholeL2 n 𝕜) (t s : ℝ) : WholeL2 n 𝕜 :=
  if s < t then W.C0 (t - s) (f s) else 0

theorem causalCosine_continuousAt {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (W : WaveOperators n 𝕜) (hC : ∀ v, Continuous (fun t => W.C0 t v))
    (f : ℝ → WholeL2 n 𝕜) (t s : ℝ) (hne : s ≠ t) :
    ContinuousAt (fun r => causalCosine W f r s) t := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have he : (fun r => causalCosine W f r s) =ᶠ[𝓝 t]
        (fun r => W.C0 (r - s) (f s)) := by
      filter_upwards [Ioi_mem_nhds hlt] with r hr
      change s < r at hr
      simp [causalCosine, hr]
    exact (((hC (f s)).comp (continuous_id.sub continuous_const)).continuousAt).congr
      he.symm
  · have he : (fun r => causalCosine W f r s) =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds hgt] with r hr
      change r < s at hr
      simp [causalCosine, not_lt.mpr hr.le]
    exact continuousAt_const.congr he.symm

/-- Continuity of the cosine source term on a fixed interval follows by
ignoring the single exceptional diagonal point in the dominated limit. -/
theorem cosineConvolutionOn_continuous {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W) (T : ℝ)
    (f : ℝ → WholeL2 n 𝕜) (hf : IntegrableOn f (Icc 0 T)) :
    Continuous (fun t => ∫ s in Icc 0 T, causalCosine W f t s) := by
  rcases hW with ⟨_, _, _, _, hB, hC, _, _, _, _, _, _, _, _, _⟩
  have hCjoint := continuous_family_apply W.C0 (fun _ => 1) continuous_const
    (fun r => (hB r).1) hC
  rw [continuous_iff_continuousAt]
  intro t
  apply continuousAt_of_dominated (bound := fun s => ‖f s‖)
  · filter_upwards [] with r
    have hm := hCjoint.comp_aestronglyMeasurable
      ((((continuous_const (y := r)).sub continuous_id).aestronglyMeasurable
        (μ := volume.restrict (Icc 0 T))).prodMk hf.aestronglyMeasurable)
    simpa only [causalCosine, indicator, mem_Iio, Pi.sub_apply, id_eq] using!
      hm.indicator measurableSet_Iio
  · filter_upwards [] with r
    filter_upwards [] with s
    unfold causalCosine
    split_ifs
    · exact ((W.C0 _).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (hB _).1 (norm_nonneg _)).trans_eq (one_mul _))
    · simp
  · exact hf.norm
  · have hn : ∀ᵐ s ∂volume.restrict (Icc 0 T), s ≠ t := by
      rw [ae_iff]
      simp only [not_not]
      change (volume.restrict (Icc 0 T)) {t} = 0
      exact measure_singleton t
    filter_upwards [hn] with s hs
    exact causalCosine_continuousAt W hC f t s hs

/-- The causal sine kernel has the expected derivative away from its
single diagonal point; no pointwise regularity of f is used. -/
theorem causalSine_hasDerivAt {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W) (f : ℝ → WholeL2 n 𝕜)
    (t s : ℝ) (hne : s ≠ t) :
    HasDerivAt (fun r => hUnderlying (⊤ : Domain n) 1
      (W.S (max (r - s) 0) (f s))) (causalCosine W f t s) t := by
  rcases hW with ⟨_, _, _, _, _, _, _, _, _, _, hSD, _, _, _, _⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have he : (fun r => hUnderlying (⊤ : Domain n) 1
        (W.S (max (r - s) 0) (f s))) =ᶠ[𝓝 t]
        (fun r => hUnderlying (⊤ : Domain n) 1 (W.S (r - s) (f s))) := by
      filter_upwards [Ioi_mem_nhds hlt] with r hr
      change s < r at hr
      rw [max_eq_left (sub_nonneg.mpr hr.le)]
    have hd := (hSD (t - s) (f s)).scomp t ((hasDerivAt_id t).sub_const s)
    have hd' : HasDerivAt (fun r => hUnderlying (⊤ : Domain n) 1 (W.S (r - s) (f s)))
        (W.C0 (t - s) (f s)) t := by
      simpa only [Function.comp_def, one_smul] using! hd
    simpa only [causalCosine, ite_eq_left hlt] using! hd'.congr_of_eventuallyEq he
  · have he : (fun r => hUnderlying (⊤ : Domain n) 1
        (W.S (max (r - s) 0) (f s))) =ᶠ[𝓝 t]
        (fun _ => hUnderlying (⊤ : Domain n) 1 (W.S 0 (f s))) := by
      filter_upwards [Iio_mem_nhds hgt] with r hr
      change r < s at hr
      rw [max_eq_right (sub_nonpos.mpr hr.le)]
    have hd := (hasDerivAt_const t (hUnderlying (⊤ : Domain n) 1 (W.S 0 (f s)))).congr_of_eventuallyEq he
    simpa only [causalCosine, ite_eq_right (not_lt.mpr hgt.le)] using! hd

/-- Uniform L² Lipschitz control permits dominated differentiation with L¹
forcing, even though the H¹-valued sine family is only strongly continuous. -/
theorem causalSine_lipschitz {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W) (v : WholeL2 n 𝕜) (s : ℝ) :
    LipschitzWith ‖v‖₊ (fun r => hUnderlying (⊤ : Domain n) 1
      (W.S (max (r - s) 0) v)) := by
  rcases hW with ⟨_, _, _, _, hB, _, _, _, _, _, hSD, _, _, _, _⟩
  have hlip : LipschitzWith ‖v‖₊ (fun r => hUnderlying (⊤ : Domain n) 1 (W.S r v)) := by
    rw [← lipschitzOnWith_univ]
    apply convex_univ.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun r _ => (hSD r v).hasDerivWithinAt)
    intro r hr
    apply NNReal.coe_le_coe.mp
    change ‖W.C0 r v‖ ≤ ‖v‖
    exact ((W.C0 r).le_opNorm v).trans
      ((mul_le_mul_of_nonneg_right (hB r).1 (norm_nonneg _)).trans_eq (one_mul _))
  have hshift : LipschitzWith 1 (fun r : ℝ => r - s) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    have he : (x - s) - (y - s) = x - y := by ring
    simp only [dist_eq_norm, he, NNReal.coe_one, one_mul, le_refl]
  simpa only [Function.comp_def, mul_one] using hlip.comp (hshift.max_const 0)

theorem sineConvolutionOn_integrable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W) (T : ℝ)
    (f : ℝ → WholeL2 n 𝕜) (hf : IntegrableOn f (Icc 0 T)) (t : ℝ) :
    IntegrableOn (fun s => W.S (max (t - s) 0) (f s)) (Icc 0 T) := by
  rcases hW with ⟨_, _, _, _, hB, _, _, hS, _, _, _, _, _, _, _⟩
  have hSjoint := continuous_family_apply W.S
    (fun r => Real.sqrt (r ^ 2 + c⁻¹ ^ 2)) (by fun_prop)
    (fun r => (hB r).2.2.1) hS
  apply (hf.norm.const_mul (Real.sqrt ((max t 0) ^ 2 + c⁻¹ ^ 2))).mono'
  · exact hSjoint.comp_aestronglyMeasurable
      (((((continuous_const (y := t)).sub continuous_id).max continuous_const).aestronglyMeasurable
        (μ := volume.restrict (Icc 0 T))).prodMk hf.aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    refine ((W.S _).le_opNorm _).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (hB _).2.2.1.trans
    apply Real.sqrt_le_sqrt
    have hm0 : 0 ≤ max (t - s) 0 := le_max_right _ _
    have hmT : max (t - s) 0 ≤ max t 0 := max_le_max_right 0 (by linarith [hs.1])
    have ht0 : 0 ≤ max t 0 := le_max_right _ _
    nlinarith

/-- Differentiation of the Duhamel source term on a fixed interval under
exactly the Bochner L¹ hypothesis. -/
theorem sineConvolutionOn_hasDerivAt {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W) (T : ℝ)
    (f : ℝ → WholeL2 n 𝕜) (hf : IntegrableOn f (Icc 0 T)) (t : ℝ) :
    HasDerivAt (fun r => hUnderlying (⊤ : Domain n) 1 (sineConvolutionOn W T f r))
      (∫ s in Icc 0 T, causalCosine W f t s) t := by
  let U := hUnderlying (𝕜 := 𝕜) (⊤ : Domain n) 1
  have hi r := sineConvolutionOn_integrable c κ W hW T f hf r
  have hUI r := U.integrable_comp (hi r)
  have he r : U (sineConvolutionOn W T f r) =
      ∫ s in Icc 0 T, U (W.S (max (r - s) 0) (f s)) :=
    (U.integral_comp_comm (hi r)).symm
  have hC := hW.2.2.2.2.2.1
  have hB := hW.2.2.2.2.1
  have hCjoint := continuous_family_apply W.C0 (fun _ => 1) continuous_const
    (fun r => (hB r).1) hC
  have hm : AEStronglyMeasurable (fun s => causalCosine W f t s)
      (volume.restrict (Icc 0 T)) := by
    have hm' := hCjoint.comp_aestronglyMeasurable
      ((((continuous_const (y := t)).sub continuous_id).aestronglyMeasurable
        (μ := volume.restrict (Icc 0 T))).prodMk hf.aestronglyMeasurable)
    simpa only [causalCosine, indicator, mem_Iio, Pi.sub_apply, id_eq] using!
      hm'.indicator measurableSet_Iio
  have hd := hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume.restrict (Icc 0 T))
    (F := fun r s => U (W.S (max (r - s) 0) (f s)))
    (F' := fun s => causalCosine W f t s) (bound := fun s => ‖f s‖)
    (s := univ) (by simp)
    (Eventually.of_forall fun r => (hUI r).aestronglyMeasurable)
    (hUI t) hm (by
      filter_upwards [] with s
      have hn : Real.nnabs ‖f s‖ = ‖f s‖₊ := by
        ext
        exact abs_of_nonneg (norm_nonneg _)
      rw [hn]
      exact (causalSine_lipschitz c κ W hW (f s) s).lipschitzOnWith)
    hf.norm (by
      have hn : ∀ᵐ s ∂volume.restrict (Icc 0 T), s ≠ t := by
        rw [ae_iff]
        simp only [not_not]
        change (volume.restrict (Icc 0 T)) {t} = 0
        exact measure_singleton t
      filter_upwards [hn] with s hs
      exact causalSine_hasDerivAt c κ W hW f t s hs)
  change HasDerivAt (fun r => U (sineConvolutionOn W T f r)) _ t
  simp_rw [he]
  exact hd.2

theorem cosineConvolutionOn_eq {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (W : WaveOperators n 𝕜) (T : ℝ) (f : ℝ → WholeL2 n 𝕜)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫ s in Icc 0 T, causalCosine W f t s) =
      ∫ s in Icc 0 t, W.C0 (t - s) (f s) := by
  change (∫ s in Icc 0 T, (Iio t).indicator (fun s => W.C0 (t - s) (f s)) s) = _
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hset : Iio t ∩ Icc 0 T = Ico 0 t := by
    ext s
    simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, h.2.le.trans ht.2⟩
  rw [hset, ← integral_Icc_eq_integral_Ico]

/-- The L² cosine convolution is continuous even for merely L¹ forcing. -/
theorem cosineConvolution_continuousOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W) (f : ℝ → WholeL2 n 𝕜)
    (hf : LocallyIntegrableForcing f) :
    ContinuousOn (fun t => ∫ s in Icc 0 t, W.C0 (t - s) (f s)) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  have hT : 0 ≤ t + 1 := by linarith
  have hc := cosineConvolutionOn_continuous c κ W hW (t + 1) f (hf _ hT)
  have hmem : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
    have hright : Iic (t + 1) ∈ 𝓝[Ici (0 : ℝ)] t :=
      mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith))
    simpa only [Ici_inter_Iic] using inter_mem self_mem_nhdsWithin hright
  apply hc.continuousAt.continuousWithinAt.congr_of_eventuallyEq
  · filter_upwards [hmem] with r hr
    exact (cosineConvolutionOn_eq W (t + 1) f r hr).symm
  · exact (cosineConvolutionOn_eq W (t + 1) f t ⟨ht, by linarith⟩).symm

/-- The strong L² derivative, including the one-sided derivative at zero. -/
theorem sineConvolution_hasDerivWithinAt {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W) (f : ℝ → WholeL2 n 𝕜)
    (hf : LocallyIntegrableForcing f) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => hUnderlying (⊤ : Domain n) 1
      (∫ s in Icc 0 r, W.S (r - s) (f s)))
      (∫ s in Icc 0 t, W.C0 (t - s) (f s)) (Ici 0) t := by
  have hT : 0 ≤ t + 1 := by linarith
  have hd := sineConvolutionOn_hasDerivAt c κ W hW (t + 1) f (hf _ hT) t
  rw [cosineConvolutionOn_eq W (t + 1) f t ⟨ht, by linarith⟩] at hd
  have hS : W.S 0 = 0 := hW.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmem : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
    have hright : Iic (t + 1) ∈ 𝓝[Ici (0 : ℝ)] t :=
      mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith))
    simpa only [Ici_inter_Iic] using inter_mem self_mem_nhdsWithin hright
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [hmem] with r hr
  exact congrArg (hUnderlying (⊤ : Domain n) 1)
    (sineConvolutionOn_eq W hS (t + 1) f r hr).symm

/-- Complete time regularity of the Bochner formula for the original data.
The distributional PDE and comparison uniqueness are separate obligations. -/
theorem duhamelRegularity {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W) (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
    (f : ℝ → WholeL2 n 𝕜) (hf : LocallyIntegrableForcing f) :
    ContinuousOn (displacement W g h f) (Ici 0) ∧
    ContinuousOn (velocity W g h f) (Ici 0) ∧
    (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun r => hUnderlying (⊤ : Domain n) 1
      (displacement W g h f r)) (velocity W g h f t) (Ici 0) t) ∧
    displacement W g h f 0 = g ∧ velocity W g h f 0 = h := by
  have hi := duhamelInitial c κ W hW g h f
  have hSin := sineConvolution_continuousOn c κ W hW f hf
  have hCos := cosineConvolution_continuousOn c κ W hW f hf
  have hDer := sineConvolution_hasDerivWithinAt c κ W hW f hf
  rcases hW with ⟨_, _, _, _, _, hC0cont, hC1cont, hScont, hDcont,
    hCderiv, hSderiv, _, _, _, _⟩
  refine ⟨?_, ?_, ?_, hi⟩
  · change ContinuousOn (fun t => displacement W g h f t) _
    exact ((hC1cont g).continuousOn.add (hScont h).continuousOn).add hSin
  · change ContinuousOn (fun t => velocity W g h f t) _
    exact ((hDcont g).continuousOn.add (hC0cont h).continuousOn).add hCos
  · intro t ht
    have hd := ((hCderiv t g).hasDerivWithinAt.add (hSderiv t h).hasDerivWithinAt).add (hDer t ht)
    simpa only [displacement, velocity, map_add] using! hd

/-- Unconditional real and complex construction of the original Bochner
formula and all its time regularity under precisely local L¹ forcing. -/
theorem waveTimeRegularity : P201Specs.Wave.Cauchy.waveTimeRegularityStatement := by
  intro n hn c hc
  obtain ⟨⟨WC, hWC⟩, ⟨WR, hWR⟩⟩ := P201.Wave.waveMultipliers n hn c hc
  constructor
  · refine ⟨WR, hWR, ?_⟩
    intro g h f hf
    exact ⟨fun t ht => duhamelIntegrable c _ WR hWR f hf t ht,
      duhamelRegularity c _ WR hWR g h f hf⟩
  · refine ⟨WC, hWC, ?_⟩
    intro g h f hf
    exact ⟨fun t ht => duhamelIntegrable c _ WC hWC f hf t ht,
      duhamelRegularity c _ WC hWC g h f hf⟩

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set
open P201Specs.Wave
namespace P201.Wave.Cauchy

/-- Equality of positions in the original comparison class determines velocities,
including at the one-sided initial endpoint. -/
theorem velocity_eq_of_position_eq {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u₁ u₂ : ℝ → WholeH1 n 𝕜} {v₁ v₂ : ℝ → WholeL2 n 𝕜}
    (h₁ : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt
      (fun s => hUnderlying (⊤ : Domain n) 1 (u₁ s)) (v₁ t) (Ici 0) t)
    (h₂ : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt
      (fun s => hUnderlying (⊤ : Domain n) 1 (u₂ s)) (v₂ t) (Ici 0) t)
    (hu : ∀ t ∈ Ici (0 : ℝ), u₁ t = u₂ t) :
    ∀ t ∈ Ici (0 : ℝ), v₁ t = v₂ t := by
  intro t ht
  have hd := (h₁ t ht).congr_of_mem
    (fun s hs => congrArg (hUnderlying (⊤ : Domain n) 1) (hu s hs).symm) ht
  exact UniqueDiffWithinAt.eq_deriv (Ici 0) (uniqueDiffOn_Ici 0 t ht) hd (h₂ t ht)

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform SchwartzMap
open LineDeriv
open P201 P201Specs.Wave
namespace P201.Wave.Cauchy

def coordinateFourierSymbol (n : ℕ) (j : Fin n) (ξ : Space n) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)

theorem coordinateFourierSymbol_temperate (n : ℕ) (j : Fin n) :
    (coordinateFourierSymbol n j).HasTemperateGrowth := by
  have hcoord : (fun ξ : Space n => (inner ℝ ξ (coordinate n j) : ℂ)) =
      fun ξ => (ξ j : ℂ) := by
    funext ξ
    rw [coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.inner_basisFun_real]
  have hg : (fun ξ : Space n => (ξ j : ℂ)).HasTemperateGrowth := by
    rw [← hcoord]
    fun_prop
  exact Function.HasTemperateGrowth.mul (Function.HasTemperateGrowth.const _) hg

theorem fourier_coordinate_derivative {n : ℕ} (j : Fin n)
    (T : 𝓢'(Space n, ℂ)) :
    𝓕 (∂_{coordinate n j} T) =
      TemperedDistribution.smulLeftCLM ℂ (coordinateFourierSymbol n j) (𝓕 T) := by
  have hcoord : (fun ξ : Space n => (inner ℝ ξ (coordinate n j) : ℂ)) =
      fun ξ => (ξ j : ℂ) := by
    funext ξ
    rw [coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.inner_basisFun_real]
  have hg : (fun ξ : Space n => (ξ j : ℂ)).HasTemperateGrowth := by
    rw [← hcoord]
    fun_prop
  rw [TemperedDistribution.fourier_lineDerivOp_eq, hcoord]
  exact (congrArg (fun L : 𝓢'(Space n, ℂ) →L[ℂ] 𝓢'(Space n, ℂ) => L (𝓕 T))
    (TemperedDistribution.smulLeftCLM_smul (F := ℂ) hg
      (2 * (Real.pi : ℂ) * Complex.I))).symm

/-- The Laplacian on tempered distributions in the shared coordinate frame. -/
def temperedLaplacian {n : ℕ} (T : 𝓢'(Space n, ℂ)) : 𝓢'(Space n, ℂ) :=
  ∑ j : Fin n, ∂_{coordinate n j} (∂_{coordinate n j} T)

theorem temperedLaplacian_test {n : ℕ} (f : FrequencyL2 n)
    (φ : P102.U4.WholeTests n ℂ) :
    temperedLaplacian (f : 𝓢'(Space n, ℂ)) (P102.U4.testToSchwartz n ℂ φ) =
      distributionLaplacian (regularDistribution ⊤ f) φ := by
  simp only [temperedLaplacian,
    distributionLaplacian, P201Specs.distributionLaplacian,
    _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    ← P201.Wave.testToSchwartz_coordinateDerivative,
    TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    ← P201.Wave.testToSchwartz_coordinateDerivative,
    P201.Wave.l2_tempered_test]
  have hsort : ((j ::ₘ {j} : Multiset (Fin n)).sort (· ≤ ·)) = [j, j] := by
    simp [Multiset.sort_cons]
  simp [P201Specs.distributionDerivative, P102.U4.distributionPartial,
    hsort, P102.U4.testPartialWord]

theorem laplacian_iff_tempered {n : ℕ} (f v : FrequencyL2 n) :
    distributionLaplacian (regularDistribution ⊤ f) = regularDistribution ⊤ v ↔
      temperedLaplacian (f : 𝓢'(Space n, ℂ)) = (v : 𝓢'(Space n, ℂ)) := by
  constructor
  · intro h
    apply DFunLike.coe_injective
    apply (P102.U4.testToSchwartz_denseRange n ℂ).equalizer
      (temperedLaplacian (f : 𝓢'(Space n, ℂ))).continuous
      (v : 𝓢'(Space n, ℂ)).continuous
    funext φ
    simp only [Function.comp_apply]
    exact (temperedLaplacian_test f φ).trans
      ((congrArg (fun T => T φ) h).trans (P201.Wave.l2_tempered_test v φ).symm)
  · intro h
    ext φ
    exact (temperedLaplacian_test f φ).symm.trans
      ((congrArg (fun T : 𝓢'(Space n, ℂ) => T (P102.U4.testToSchwartz n ℂ φ)) h).trans
        (P201.Wave.l2_tempered_test v φ))

theorem fourier_temperedLaplacian {n : ℕ} (T : 𝓢'(Space n, ℂ)) :
    𝓕 (temperedLaplacian T) =
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ => ∑ j : Fin n, coordinateFourierSymbol n j ξ ^ 2) (𝓕 T) := by
  rw [temperedLaplacian]
  change (FourierTransform.fourierCLM ℂ 𝓢'(Space n, ℂ)) (∑ j : Fin n,
    ∂_{coordinate n j} (∂_{coordinate n j} T)) = _
  rw [map_sum]
  change (∑ j : Fin n, 𝓕 (∂_{coordinate n j} (∂_{coordinate n j} T))) = _
  simp_rw [fourier_coordinate_derivative]
  have h (j : Fin n) :
      TemperedDistribution.smulLeftCLM ℂ (coordinateFourierSymbol n j)
        (TemperedDistribution.smulLeftCLM ℂ (coordinateFourierSymbol n j) (𝓕 T)) =
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ => coordinateFourierSymbol n j ξ ^ 2) (𝓕 T) := by
    calc
      _ = TemperedDistribution.smulLeftCLM ℂ
          (coordinateFourierSymbol n j * coordinateFourierSymbol n j) (𝓕 T) :=
        TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
          (coordinateFourierSymbol_temperate n j) (coordinateFourierSymbol_temperate n j) (𝓕 T)
      _ = _ := congrArg (fun a : Space n → ℂ =>
          TemperedDistribution.smulLeftCLM ℂ a (𝓕 T))
        (funext fun ξ => (pow_two (coordinateFourierSymbol n j ξ)).symm)
  simp_rw [h]
  have hs := TemperedDistribution.smulLeftCLM_sum (F := ℂ)
    (g := fun j : Fin n => fun ξ => coordinateFourierSymbol n j ξ ^ 2)
    (s := Finset.univ) (fun j _ => (coordinateFourierSymbol_temperate n j).pow 2)
  simpa only [_root_.sum_apply] using
    (congrArg (fun L : 𝓢'(Space n, ℂ) →L[ℂ] 𝓢'(Space n, ℂ) => L (𝓕 T)) hs).symm

theorem laplacian_iff_fourier {n : ℕ} (f v : FrequencyL2 n) :
    distributionLaplacian (regularDistribution ⊤ f) = regularDistribution ⊤ v ↔
      (𝓕 v : FrequencyL2 n) =ᵐ[volume]
        fun ξ => (∑ j : Fin n, coordinateFourierSymbol n j ξ ^ 2) *
          (𝓕 f : FrequencyL2 n) ξ := by
  have ha : (fun ξ => ∑ j : Fin n, coordinateFourierSymbol n j ξ ^ 2).HasTemperateGrowth := by
    exact Function.HasTemperateGrowth.sum (fun j _ =>
      (coordinateFourierSymbol_temperate n j).pow 2)
  rw [laplacian_iff_tempered]
  constructor
  · intro h
    apply (P201.Wave.tempered_mul_iff_ae _ ha (𝓕 f) (𝓕 v)).mp
    rw [← MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
      ← MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
      ← fourier_temperedLaplacian, h]
  · intro h
    have he := (P201.Wave.tempered_mul_iff_ae _ ha (𝓕 f) (𝓕 v)).mpr h
    have he' : 𝓕 (temperedLaplacian (f : 𝓢'(Space n, ℂ))) =
        𝓕 (v : 𝓢'(Space n, ℂ)) := by
      rw [fourier_temperedLaplacian, MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
        MeasureTheory.Lp.fourier_toTemperedDistribution_eq, ← he]
    have := congrArg (fun T : 𝓢'(Space n, ℂ) => 𝓕⁻ T) he'
    simpa only [FourierTransform.fourierInv_fourier_eq] using this

theorem laplacianFourierSymbol_eq {n : ℕ} (ξ : Space n) :
    (∑ j : Fin n, coordinateFourierSymbol n j ξ ^ 2) =
      -((2 * Real.pi) ^ 2 : ℝ) * (‖ξ‖ ^ 2 : ℝ) := by
  have hξ := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) ξ
  simp only [Real.norm_eq_abs, sq_abs] at hξ
  rw [hξ, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [coordinateFourierSymbol, mul_pow, Complex.I_sq,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

theorem laplacian_iff_radial_fourier {n : ℕ} (f v : FrequencyL2 n) :
    distributionLaplacian (regularDistribution ⊤ f) = regularDistribution ⊤ v ↔
      (𝓕 v : FrequencyL2 n) =ᵐ[volume]
        fun ξ => (-((2 * Real.pi) ^ 2 : ℝ) * (‖ξ‖ ^ 2 : ℝ) : ℂ) *
          (𝓕 f : FrequencyL2 n) ξ := by
  simpa only [laplacianFourierSymbol_eq] using laplacian_iff_fourier f v

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set TopologicalSpace Topology Filter
open scoped ENNReal ContDiff
open P201Specs P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201.Wave.Cauchy.TestSlices

theorem norm_sq_L2 {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜] {μ : Measure α}
    (f : MeasureTheory.Lp 𝕜 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]

theorem tendsto_toL2_of_dominated {α 𝕜 ι : Type*} [MeasurableSpace α] [RCLike 𝕜]
    {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → α → 𝕜) (hF : ∀ i, MemLp (F i) 2 μ)
    (G : α → 𝕜) (hG : MemLp G 2 μ) (B : α → ℝ) (hB : Integrable B μ)
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x - G x‖^2 ≤ B x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (G x))) :
    Tendsto (fun i => (hF i).toLp (F i)) l (𝓝 (hG.toLp G)) := by
  have hsq (i : ι) :
      ‖(hF i).toLp (F i) - hG.toLp G‖^2 = ∫ x, ‖F i x-G x‖^2 ∂μ := by
    rw [norm_sq_L2]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Lp.coeFn_sub ((hF i).toLp (F i)) (hG.toLp G),
      (hF i).coeFn_toLp, hG.coeFn_toLp] with x hs hi h₀
    simp only [hs, Pi.sub_apply, hi, h₀]
  have hlim' : Tendsto (fun i => ∫ x, ‖F i x - G x‖^2 ∂μ) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (l := l) (μ := μ)
      (F := fun i x => ‖F i x-G x‖^2) (f := fun _ => (0 : ℝ)) B
    simp only [integral_zero] at h
    apply h
    · exact Eventually.of_forall fun i =>
        (((hF i).aestronglyMeasurable.sub hG.aestronglyMeasurable).norm.pow 2)
    · exact hb.mono fun i hi => hi.mono fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hx
    · exact hB
    · filter_upwards [hlim] with x hx
      simpa using (hx.sub_const (G x)).norm.pow 2
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hlim'
  simp only [Real.sqrt_zero] at hsqrt
  convert hsqrt using 1
  ext i
  rw [Function.comp_apply, ← hsq, Real.sqrt_sq (norm_nonneg _)]

private theorem closedEmbedding_slice {n : ℕ} (t : ℝ) :
    IsClosedEmbedding (fun x : Space n => (t,x)) := by
  refine ⟨isEmbedding_prodMkRight t, ?_⟩
  have hr : range (fun x : Space n => (t,x)) = Prod.fst ⁻¹' {t} := by
    ext p
    constructor
    · rintro ⟨x,rfl⟩
      rfl
    · intro hp
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
  rw [hr]
  exact isClosed_singleton.preimage continuous_fst

def spatialSlice {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) : Test 𝕜 (⊤ : Domain n) where
  toFun x := φ (t,x)
  contDiff' := φ.contDiff.comp (contDiff_const.prodMk contDiff_id)
  hasCompactSupport' := φ.hasCompactSupport.comp_isClosedEmbedding (closedEmbedding_slice t)
  tsupport_subset' := subset_univ _

@[simp] theorem spatialSlice_apply {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) (x : Space n) : spatialSlice φ t x = φ (t,x) := rfl

def timeDerivTest {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) : SpacetimeTest n 𝕜 :=
  TestFunction.lineDerivCLM ℝ (1, (0 : Space n)) φ

theorem timeDerivTest_apply {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) (x : Space n) :
    timeDerivTest φ (t,x) = deriv (fun s => φ (s,x)) t := by
  unfold timeDerivTest
  rw [TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ (by simp)]
  have hd := ((φ.contDiff.differentiable (by simp)).differentiableAt
      (x := (t,x))).hasFDerivAt
  exact (hd.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv.symm

def laplacianTest {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ψ : Test 𝕜 (⊤ : Domain n)) : Test 𝕜 (⊤ : Domain n) :=
  ∑ i : Fin n, P102.U4.testPartialWord ⊤ (({i,i} : MultiIndex n).sort (· ≤ ·)) ψ

@[simp] theorem laplacianTest_apply {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ψ : Test 𝕜 (⊤ : Domain n)) (x : Space n) :
    laplacianTest ψ x = P201Specs.laplacian ψ x := by
  change ((FunLike.coeAddMonoidHom (Test 𝕜 (⊤ : Domain n)) (Space n) 𝕜)
    (∑ i : Fin n, P102.U4.testPartialWord ⊤ (({i,i} : MultiIndex n).sort (· ≤ ·)) ψ)) x = _
  rw [map_sum, Finset.sum_apply]
  simp only [FunLike.coeAddMonoidHom_apply, P102.U4.testPartialWord_coe]
  rfl

def waveOperatorSlice {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (φ : SpacetimeTest n 𝕜) (t : ℝ) : Test 𝕜 (⊤ : Domain n) :=
  spatialSlice (timeDerivTest (timeDerivTest φ)) t - c^2 • laplacianTest (spatialSlice φ t)

@[simp] theorem waveOperatorSlice_apply {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (φ : SpacetimeTest n 𝕜) (t : ℝ) (x : Space n) :
    waveOperatorSlice c φ t x = testWaveOperator c φ t x := by
  simp only [waveOperatorSlice, sub_apply, smul_apply,
    spatialSlice_apply, timeDerivTest_apply, laplacianTest_apply, testWaveOperator]
  rfl

 theorem memLp_spatialSlice {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) (p : ℝ≥0∞) :
    MemLp (fun x => φ (t,x)) p (volume : Measure (Space n)) :=
  (spatialSlice φ t).continuous.memLp_of_hasCompactSupport (spatialSlice φ t).hasCompactSupport

theorem memLp_testWaveOperator {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (φ : SpacetimeTest n 𝕜) (t : ℝ) (p : ℝ≥0∞) :
    MemLp (testWaveOperator c φ t) p (volume : Measure (Space n)) := by
  have he : ⇑(waveOperatorSlice c φ t) = testWaveOperator c φ t :=
    funext (waveOperatorSlice_apply c φ t)
  rw [← he]
  exact (waveOperatorSlice c φ t).continuous.memLp_of_hasCompactSupport
    (waveOperatorSlice c φ t).hasCompactSupport

 theorem integrable_L2_mul_spatialSlice {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : WholeL2 n 𝕜) (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    Integrable (fun x => f x * φ (t,x)) := by
  have hf : MemLp f 2 (volume : Measure (Space n)) := by
    simpa only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] using MeasureTheory.Lp.memLp f
  exact hf.integrable_mul (memLp_spatialSlice φ t 2)

 theorem integrable_L2_mul_testWaveOperator {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : WholeL2 n 𝕜) (c : ℝ) (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    Integrable (fun x => f x * testWaveOperator c φ t x) := by
  have hf : MemLp f 2 (volume : Measure (Space n)) := by
    simpa only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] using MeasureTheory.Lp.memLp f
  exact hf.integrable_mul (memLp_testWaveOperator c φ t 2)

def standardSliceL2 {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) : MeasureTheory.Lp 𝕜 2 (volume : Measure (Space n)) :=
  (memLp_spatialSlice φ t 2).toLp (fun x => φ (t,x))

 theorem standardSliceL2_ae {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    ⇑(standardSliceL2 φ t) =ᵐ[volume] (fun x => φ (t,x)) :=
  (memLp_spatialSlice φ t 2).coeFn_toLp

private theorem spatial_zero_off_support {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) (x : Space n)
    (hx : x ∉ Prod.snd '' tsupport φ) : φ (t,x) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  exact hx ⟨(t,x),ht,rfl⟩

private theorem hasDerivAt_slice {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) (x : Space n) :
    HasDerivAt (fun s => φ (s,x)) (timeDerivTest φ (t,x)) t := by
  rw [timeDerivTest_apply]
  exact ((φ.contDiff.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t).hasDerivAt

private theorem integrable_indicator_compact {n : ℕ} (K : Set (Space n))
    (hK : IsCompact K) (B : ℝ) : Integrable (K.indicator (fun _ => B)) := by
  exact (integrable_indicator_iff hK.measurableSet).mpr
    (integrableOn_const hK.measure_lt_top.ne)

 theorem standardSliceL2_hasDerivAt {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    HasDerivAt (standardSliceL2 φ) (standardSliceL2 (timeDerivTest φ) t) t := by
  let dφ := timeDerivTest φ
  let K := Prod.snd '' tsupport φ ∪ Prod.snd '' tsupport dφ
  have hK : IsCompact K :=
    (φ.hasCompactSupport.image continuous_snd).union (dφ.hasCompactSupport.image continuous_snd)
  let B := ‖(dφ : BoundedContinuousFunction (ℝ × Space n) 𝕜)‖
  have hB : 0 ≤ B := norm_nonneg _
  have hdb (s : ℝ) (x : Space n) : ‖dφ (s,x)‖ ≤ B := by
    exact BoundedContinuousFunction.norm_coe_le_norm
      (dφ : BoundedContinuousFunction (ℝ × Space n) 𝕜) (s,x)
  have hslope (s : ℝ) (x : Space n) :
      ‖slope (fun r => φ (r,x)) t s‖ ≤ B := by
    by_cases hst : s = t
    · subst s
      simp [hB]
    · have hn := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun r _ => (hasDerivAt_slice φ r x).hasDerivWithinAt)
          (fun r _ => hdb r x) (mem_univ t) (mem_univ s)
      rw [slope_def_module, norm_smul, norm_inv]
      exact (inv_mul_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hst))).mpr (by simpa only [mul_comm] using hn)
  let F : ℝ → Space n → 𝕜 := fun s x => slope (fun r => φ (r,x)) t s
  have hF (s : ℝ) : MemLp (F s) 2 (volume : Measure (Space n)) := by
    exact ((memLp_spatialSlice φ s 2).sub (memLp_spatialSlice φ t 2)).const_smul ((s-t)⁻¹)
  have htend := tendsto_toL2_of_dominated (l := 𝓝[≠] t) F hF (fun x => dφ (t,x))
    (memLp_spatialSlice dφ t 2) (K.indicator (fun _ => (2*B)^2))
    (integrable_indicator_compact K hK _)
  apply hasDerivAt_iff_tendsto_slope.mpr
  have he (s : ℝ) : (hF s).toLp (F s) = slope (standardSliceL2 φ) t s := by
    apply MeasureTheory.Lp.ext
    filter_upwards [(hF s).coeFn_toLp,
      MeasureTheory.Lp.coeFn_smul ((s-t)⁻¹) (standardSliceL2 φ s - standardSliceL2 φ t),
      MeasureTheory.Lp.coeFn_sub (standardSliceL2 φ s) (standardSliceL2 φ t),
      standardSliceL2_ae φ s, standardSliceL2_ae φ t] with x hfx hsm hsub hs ht
    simp only [slope_def_module]
    rw [hfx, hsm]
    simp only [Pi.smul_apply, hsub, Pi.sub_apply, hs, ht]
    rfl
  simp_rw [he] at htend
  apply htend
  · exact Eventually.of_forall fun s => Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        exact (norm_sub_le _ _).trans (by linarith [hslope s x,hdb t x])
      · have hxφ : x ∉ Prod.snd '' tsupport φ := fun hxφ => hx (Or.inl hxφ)
        have hxd : x ∉ Prod.snd '' tsupport dφ := fun hxd => hx (Or.inr hxd)
        simp only [F, slope_def_module, spatial_zero_off_support φ s x hxφ,
          spatial_zero_off_support φ t x hxφ, sub_self, smul_zero,
          spatial_zero_off_support dφ t x hxd, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
          indicator_of_notMem hx, le_refl]
  · exact Eventually.of_forall fun x => (hasDerivAt_slice φ t x).tendsto_slope


theorem standardSliceL2_continuous {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) : Continuous (standardSliceL2 φ) :=
  continuous_iff_continuousAt.mpr (fun t => (standardSliceL2_hasDerivAt φ t).continuousAt)

def wholeSliceL2 {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) : WholeL2 n 𝕜 :=
  (wholeL2Standard n 𝕜).symm (standardSliceL2 φ t)

theorem wholeSliceL2_hasDerivAt {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    HasDerivAt (wholeSliceL2 φ) (wholeSliceL2 (timeDerivTest φ) t) t := by
  let J := (wholeL2Standard n 𝕜).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  exact J.hasFDerivAt.comp_hasDerivAt t (standardSliceL2_hasDerivAt φ t)

theorem wholeSliceL2_continuous {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) : Continuous (wholeSliceL2 φ) :=
  (wholeL2Standard n 𝕜).symm.continuous.comp (standardSliceL2_continuous φ)


theorem wholeSliceL2_ae {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    ⇑(wholeSliceL2 φ t) =ᵐ[volume] (fun x => φ (t,x)) := by
  have he : ⇑(wholeSliceL2 φ t) =ᵐ[volume] ⇑(standardSliceL2 φ t) := by
    have h : ⇑(wholeSliceL2 φ t) =ᵐ[volume.restrict (univ : Set (Space n))]
        (fun x => standardSliceL2 φ t x) := by
      exact MeasureTheory.Lp.coeFn_compMeasurePreserving (standardSliceL2 φ t) _
    simpa only [Measure.restrict_univ] using h

  exact he.trans (standardSliceL2_ae φ t)

private theorem standardSliceL2_eq_zero_off_timeSupport {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) (ht : t ∉ Prod.fst '' tsupport φ) :
    standardSliceL2 φ t = 0 := by
  apply MeasureTheory.Lp.ext
  filter_upwards [standardSliceL2_ae φ t, MeasureTheory.Lp.coeFn_zero 𝕜 2 (volume : Measure (Space n))] with x hx hz
  rw [hx,hz]
  apply image_eq_zero_of_notMem_tsupport
  intro hp
  exact ht ⟨(t,x),hp,rfl⟩

theorem standardSliceL2_hasCompactSupport {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) : HasCompactSupport (standardSliceL2 φ) := by
  apply HasCompactSupport.of_support_subset_isCompact (φ.hasCompactSupport.image continuous_fst)
  intro t ht
  by_contra hn
  exact ht (standardSliceL2_eq_zero_off_timeSupport φ t hn)

theorem wholeSliceL2_hasCompactSupport {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) : HasCompactSupport (wholeSliceL2 φ) :=
  (standardSliceL2_hasCompactSupport φ).comp_left (map_zero (wholeL2Standard n 𝕜).symm)

theorem wholeSliceL2_zero_nonpos {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) (ht : t ≤ 0) : wholeSliceL2 φ t = 0 := by
  have htφ : t ∉ Prod.fst '' tsupport φ := by
    rintro ⟨⟨s,x⟩,hs,hst⟩
    have hs0 := (φ.tsupport_subset hs).1
    dsimp only at hst
    change 0 < s at hs0
    linarith
  unfold wholeSliceL2
  rw [standardSliceL2_eq_zero_off_timeSupport φ t htφ, map_zero]


abbrev TimeTest (T : ℝ) := TestFunction (⟨Ioo 0 T, isOpen_Ioo⟩ : Opens ℝ) ℝ ⊤

private theorem tensor_tsupport_subset {n : ℕ} {T : ℝ} {𝕜 : Type} [RCLike 𝕜]
    (η : TimeTest T) (ψ : Test 𝕜 (⊤ : Domain n)) :
    tsupport (fun p : ℝ × Space n => η p.1 • ψ p.2) ⊆ tsupport η ×ˢ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport η |>.prod (isClosed_tsupport ψ))
  intro p hp
  exact ⟨subset_tsupport η (smul_ne_zero_iff.mp hp).1,
    subset_tsupport ψ (smul_ne_zero_iff.mp hp).2⟩

def tensorTest {n : ℕ} {T : ℝ} {𝕜 : Type} [RCLike 𝕜]
    (η : TimeTest T) (ψ : Test 𝕜 (⊤ : Domain n)) : SpacetimeTest n 𝕜 where
  toFun p := η p.1 • ψ p.2
  contDiff' := (η.contDiff.comp contDiff_fst).smul (ψ.contDiff.comp contDiff_snd)
  hasCompactSupport' := (η.hasCompactSupport.prod ψ.hasCompactSupport).of_isClosed_subset
    (isClosed_tsupport _) (tensor_tsupport_subset η ψ)
  tsupport_subset' := by
    intro p hp
    exact ⟨(η.tsupport_subset ((tensor_tsupport_subset η ψ) hp).1).1, mem_univ _⟩

@[simp] theorem tensorTest_apply {n : ℕ} {T : ℝ} {𝕜 : Type} [RCLike 𝕜]
    (η : TimeTest T) (ψ : Test 𝕜 (⊤ : Domain n)) (t : ℝ) (x : Space n) :
    tensorTest η ψ (t,x) = η t • ψ x := rfl

theorem laplacianTest_smul {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : 𝕜) (ψ : Test 𝕜 (⊤ : Domain n)) :
    laplacianTest (a • ψ) = a • laplacianTest ψ := by
  simp only [laplacianTest, map_smul, Finset.smul_sum]

theorem laplacian_smul_test {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : 𝕜) (ψ : Test 𝕜 (⊤ : Domain n)) (x : Space n) :
    P201Specs.laplacian (fun y => a * ψ y) x = a * P201Specs.laplacian ψ x := by
  change P201Specs.laplacian (⇑(a • ψ)) x = _
  rw [← laplacianTest_apply, laplacianTest_smul]
  change a * laplacianTest ψ x = _
  rw [laplacianTest_apply]

theorem laplacianTest_real_smul {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : ℝ) (ψ : Test 𝕜 (⊤ : Domain n)) :
    laplacianTest (a • ψ) = a • laplacianTest ψ := by
  simp only [laplacianTest, ContinuousLinearMap.map_smul_of_tower, Finset.smul_sum]

theorem laplacian_real_smul_test {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : ℝ) (ψ : Test 𝕜 (⊤ : Domain n)) (x : Space n) :
    P201Specs.laplacian (fun y => a • ψ y) x = a • P201Specs.laplacian ψ x := by
  change P201Specs.laplacian (⇑(a • ψ)) x = _
  rw [← laplacianTest_apply, laplacianTest_real_smul]
  change a • laplacianTest ψ x = _
  rw [laplacianTest_apply]

theorem testWaveOperator_tensorTest {n : ℕ} {T : ℝ} {𝕜 : Type} [RCLike 𝕜]
    (η : TimeTest T) (ψ : Test 𝕜 (⊤ : Domain n)) (c t : ℝ) (x : Space n) :
    testWaveOperator c (tensorTest η ψ) t x =
      deriv (deriv η) t • ψ x - c^2 • (η t • P201Specs.laplacian ψ x) := by
  have hη : Differentiable ℝ η := η.contDiff.differentiable (by simp)
  have hη2 : ContDiff ℝ 2 η := η.contDiff.of_le (by simp)
  have hdη1 : ContDiff ℝ 1 (deriv η) := hη2.deriv'
  have hdη : Differentiable ℝ (deriv η) := hdη1.differentiable (by simp)
  simp only [testWaveOperator, tensorTest_apply]
  have he : (fun s => deriv (fun r => η r • ψ x) s) =
      (fun s => deriv η s • ψ x) := funext (fun s => deriv_smul_const (hη s) (ψ x))
  rw [he, deriv_smul_const (hdη t), laplacian_real_smul_test]

end P201.Wave.Cauchy.TestSlices
end

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform SchwartzMap
open P201 P201Specs.Wave
namespace P201.Wave.Cauchy

def testL2 {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (φ : P102.U4.WholeTests n 𝕜) :
    MeasureTheory.Lp (α := Space n) 𝕜 2 volume :=
  (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport).toLp φ

theorem testL2_ae {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (φ : P102.U4.WholeTests n 𝕜) :
    (testL2 φ : Space n → 𝕜) =ᵐ[volume] φ :=
  MemLp.coeFn_toLp _

theorem testL2_regular {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : P102.U4.WholeTests n 𝕜) :
    regularDistribution ⊤ (testL2 φ) = regularDistribution ⊤ φ := by
  apply (P102.U4.regular_injectivity n 𝕜 ⊤ _ _
    (((MeasureTheory.Lp.memLp (testL2 φ)).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
    (φ.continuous.locallyIntegrable.locallyIntegrableOn _)).mpr
  simpa only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using testL2_ae φ

theorem laplacian_regular_test {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : P102.U4.WholeTests n 𝕜) :
    distributionLaplacian (regularDistribution ⊤ φ) =
      regularDistribution ⊤ (laplacian φ) := by
  have hm (j : Fin n) : LocallyIntegrableOn (multiPartial φ ({j,j} : MultiIndex n))
      (⊤ : Domain n) volume := by
    change LocallyIntegrableOn (P102.U4.partialWord φ (({j,j} : MultiIndex n).sort (· ≤ ·))) _ _
    rw [← P102.U4.testPartialWord_coe ⊤ (({j,j} : MultiIndex n).sort (· ≤ ·)) φ]
    exact (P102.U4.testPartialWord ⊤ (({j,j} : MultiIndex n).sort (· ≤ ·)) φ).continuous.locallyIntegrable.locallyIntegrableOn _
  have he : ⇑(TestSlices.laplacianTest φ) = laplacian φ :=
    funext (TestSlices.laplacianTest_apply φ)
  have hLap : LocallyIntegrableOn (laplacian φ) (⊤ : Domain n) volume := by
    rw [← he]
    exact (TestSlices.laplacianTest φ).continuous.locallyIntegrable.locallyIntegrableOn _
  ext ψ
  simp only [distributionLaplacian, P201Specs.distributionLaplacian,
    P201Specs.distributionDerivative, _root_.sum_apply]
  have hd (j : Fin n) := P102.U4.derivative_classicalCompatibility n 𝕜 ⊤
    ({j,j} : MultiIndex n) φ (φ.contDiff.of_le (by simp)).contDiffOn
  simp_rw [hd]
  rw [P102.U4.regular_pairing n 𝕜 ⊤ (laplacian φ) hLap]
  simp_rw [P102.U4.regular_pairing n 𝕜 ⊤ _ (hm _)]
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
  have hi (j : Fin n) : Integrable (fun x => multiPartial φ ({j,j} : MultiIndex n) x * ψ x) := by
    have h := ψ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) (hm j)
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using h
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [laplacian, P201Specs.laplacian, Finset.sum_mul]

theorem testL2_laplacian_fourier {n : ℕ} (φ : P102.U4.WholeTests n ℂ) :
    (𝓕 (testL2 (TestSlices.laplacianTest φ)) : FrequencyL2 n) =ᵐ[volume]
      fun ξ => (-((2 * Real.pi) ^ 2 : ℝ) * (‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (𝓕 (testL2 φ) : FrequencyL2 n) ξ := by
  apply (laplacian_iff_radial_fourier (testL2 φ) (testL2 (TestSlices.laplacianTest φ))).mp
  rw [testL2_regular, testL2_regular, laplacian_regular_test]
  congr 1
  exact (funext (TestSlices.laplacianTest_apply φ)).symm

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set
open P201Specs.Wave
namespace P201.Wave.Cauchy

/-- The cosine derivative is minus frequency squared times the sine kernel,
including its continuous zero-frequency value. -/
theorem cosineDerivativeSymbol_eq_neg_sq_sine (t w : ℝ) :
    cosineDerivativeSymbol t w = -(w ^ 2) * sineSymbol t w := by
  by_cases hw : w = 0
  · simp [P201.Wave.cosineDerivativeSymbol, P201.Wave.sineSymbol,
      P201Specs.Wave.cosineDerivativeSymbol, P201Specs.Wave.sineSymbol, hw]
  · simp only [P201.Wave.cosineDerivativeSymbol, P201.Wave.sineSymbol,
      P201Specs.Wave.cosineDerivativeSymbol, P201Specs.Wave.sineSymbol, ite_eq_right hw]
    field_simp

/-- A Banach-valued finite-interval Green identity for the retarded scalar
sine kernel. No regularity of a forcing term enters this identity. -/
theorem sineSymbol_green {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {ψ ψ' ψ'' : ℝ → E} (s T w : ℝ)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hψ' : ∀ t, HasDerivAt ψ' (ψ'' t) t)
    (hψ'' : Continuous ψ'') (hT : ψ T = 0) (hT' : ψ' T = 0) :
    (∫ t in s..T, sineSymbol (t - s) w •
      (ψ'' t + (w ^ 2) • ψ t)) = ψ s := by
  let A : ℝ → ℝ := fun t => sineSymbol (t-s) w
  let B : ℝ → ℝ := fun t => cosineSymbol (t-s) w
  have hA (t : ℝ) : HasDerivAt A (B t) t := by
    simpa only [A, B, Function.comp_apply, id_eq, mul_one] using!
      ((P201.Wave.scalarDerivatives (t-s) w).1.comp t ((hasDerivAt_id t).sub_const s))
  have hB (t : ℝ) : HasDerivAt B (-(w^2) * A t) t := by
    simpa only [A, B, Function.comp_apply, id_eq, mul_one,
      cosineDerivativeSymbol_eq_neg_sq_sine] using!
      ((P201.Wave.scalarDerivatives (t-s) w).2.comp t ((hasDerivAt_id t).sub_const s))
  have hW (t : ℝ) : HasDerivAt (fun t => A t • ψ' t - B t • ψ t)
      (A t • (ψ'' t + (w ^ 2) • ψ t)) t := by
    convert ((hA t).smul (hψ' t)).sub ((hB t).smul (hψ t)) using 1 <;> module
  have hcψ : Continuous ψ := continuous_iff_continuousAt.mpr fun t => (hψ t).continuousAt
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun t => (hA t).continuousAt
  have hi : IntervalIntegrable (fun t => A t • (ψ'' t + (w ^ 2) • ψ t)) volume s T :=
    (hcA.smul (hψ''.add (continuous_const.smul hcψ))).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hW t) hi
  simpa only [A, B, sub_self, hT, hT', smul_zero, sub_zero, zero_sub,
    P201.Wave.sineSymbol, P201.Wave.cosineSymbol,
    P201Specs.Wave.sineSymbol, P201Specs.Wave.cosineSymbol, zero_mul, Real.sin_zero,
    Real.cos_zero, zero_div, ite_self, zero_smul, one_smul, neg_neg] using he


/-- The corresponding cosine Green identity; both endpoint data are displayed.
In the Cauchy problem the lower test value and derivative vanish. -/
theorem cosineSymbol_green {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {ψ ψ' ψ'' : ℝ → E} (s T w : ℝ)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hψ' : ∀ t, HasDerivAt ψ' (ψ'' t) t)
    (hψ'' : Continuous ψ'') (hT : ψ T = 0) (hT' : ψ' T = 0) :
    (∫ t in s..T, cosineSymbol (t - s) w •
      (ψ'' t + (w ^ 2) • ψ t)) = -ψ' s := by
  let A : ℝ → ℝ := fun t => sineSymbol (t-s) w
  let B : ℝ → ℝ := fun t => cosineSymbol (t-s) w
  have hA (t : ℝ) : HasDerivAt A (B t) t := by
    simpa only [A, B, Function.comp_apply, id_eq, mul_one] using!
      ((P201.Wave.scalarDerivatives (t-s) w).1.comp t ((hasDerivAt_id t).sub_const s))
  have hB (t : ℝ) : HasDerivAt B (-(w^2) * A t) t := by
    simpa only [A, B, Function.comp_apply, id_eq, mul_one,
      cosineDerivativeSymbol_eq_neg_sq_sine] using!
      ((P201.Wave.scalarDerivatives (t-s) w).2.comp t ((hasDerivAt_id t).sub_const s))
  have hW (t : ℝ) : HasDerivAt (fun t => B t • ψ' t + (w^2 * A t) • ψ t)
      (B t • (ψ'' t + (w ^ 2) • ψ t)) t := by
    convert ((hB t).smul (hψ' t)).add (((hA t).const_mul (w^2)).smul (hψ t)) using 1 <;> module
  have hcψ : Continuous ψ := continuous_iff_continuousAt.mpr fun t => (hψ t).continuousAt
  have hcB : Continuous B := continuous_iff_continuousAt.mpr fun t => (hB t).continuousAt
  have hi : IntervalIntegrable (fun t => B t • (ψ'' t + (w ^ 2) • ψ t)) volume s T :=
    (hcB.smul (hψ''.add (continuous_const.smul hcψ))).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hW t) hi
  simpa only [A, B, sub_self, hT, hT', smul_zero, zero_add, sub_zero, zero_sub,
    P201.Wave.sineSymbol, P201.Wave.cosineSymbol,
    P201Specs.Wave.sineSymbol, P201Specs.Wave.cosineSymbol, zero_mul, Real.sin_zero,
    Real.cos_zero, zero_div, ite_self, mul_zero, zero_smul, one_smul, add_zero] using he

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set
open P201Specs.Wave
namespace P201.Wave.Cauchy

/-- Transpose a causal scalar sine convolution against an integrable family
of bounded linear tests. Both time integrals are on a fixed finite interval. -/
theorem causalSine_integral_transpose {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T w : ℝ) (hT : 0 ≤ T) (f : ℝ → E) (R : ℝ → E →L[ℝ] F)
    (hf : IntegrableOn f (Icc 0 T)) (hR : IntegrableOn R (Icc 0 T)) :
    (∫ t in Icc 0 T, R t (∫ s in Icc 0 T, sineSymbol (max (t-s) 0) w • f s)) =
    ∫ s in Icc 0 T, (∫ t in Icc 0 T, sineSymbol (max (t-s) 0) w • R t) (f s) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let q : ℝ × ℝ → ℝ := fun p => sineSymbol (max (p.1-p.2) 0) w
  have hq : Continuous q :=
    P201.Wave.scalarContinuity.1.comp
      ((((continuous_fst.sub continuous_snd).max continuous_const)).prodMk continuous_const)
  have hqb (t s : ℝ) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) : ‖q (t,s)‖ ≤ T := by
    have hm : 0 ≤ max (t-s) 0 := le_max_right _ _
    have hMT : max (t-s) 0 ≤ T := max_le (by linarith [ht.2, hs.1]) hT
    exact (P201.Wave.scalarBounds _ _).1.trans (by simpa [q, Real.norm_eq_abs, abs_of_nonneg hm] using hMT)
  have hiF (t : ℝ) (ht : t ∈ Icc 0 T) :
      Integrable (fun s => q (t,s) • f s) μ := by
    apply hf.bdd_smul T ((hq.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hqb t s ht hs
  have hiR (s : ℝ) (hs : s ∈ Icc 0 T) :
      Integrable (fun t => q (t,s) • R t) μ := by
    apply hR.bdd_smul T ((hq.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hqb t s ht hs
  have hi : Integrable (fun p : ℝ × ℝ => q p • R p.1 (f p.2)) (μ.prod μ) := by
    have hEval : Continuous (fun p : (E →L[ℝ] F) × E => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    have heval := hR.op_fst_snd hEval ⟨1, fun A v => by simpa using A.le_opNorm v⟩ hf
    apply heval.bdd_smul T hq.aestronglyMeasurable
    have hm : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, p.1 ∈ Icc 0 T ∧ p.2 ∈ Icc 0 T := by
      change ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, p ∈ ((Icc 0 T) ×ˢ (Icc 0 T))
      rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Icc.prod measurableSet_Icc)]
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact ⟨ht,hs⟩
    filter_upwards [hm] with p hp
    exact hqb p.1 p.2 hp.1 hp.2
  calc
    (∫ t in Icc 0 T, R t (∫ s in Icc 0 T, sineSymbol (max (t-s) 0) w • f s)) =
        ∫ t, ∫ s, q (t,s) • R t (f s) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [← (R t).integral_comp_comm (hiF t ht)]
      simp only [q, map_smul]
    _ = ∫ s, ∫ t, q (t,s) • R t (f s) ∂μ ∂μ := integral_integral_swap hi
    _ = ∫ s in Icc 0 T, (∫ t in Icc 0 T, sineSymbol (max (t-s) 0) w • R t) (f s) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [ContinuousLinearMap.integral_apply (hiR s hs)]
      simp only [q, ContinuousLinearMap.smul_apply]

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform ComplexConjugate
open P201Specs.Wave
namespace P201.Wave.Cauchy

/-- A real frequency symbol gives a symmetric L² Fourier multiplier. -/
theorem fourierMultiplier_inner {n : ℕ} (m : Space n → ℂ)
    (hm : MemLp m ∞ volume) (hreal : ∀ x, star (m x) = m x)
    (f g : FrequencyL2 n) :
    inner ℂ (P201.Wave.fourierMultiplier m hm f) g =
      inner ℂ f (P201.Wave.fourierMultiplier m hm g) := by
  calc
    inner ℂ (P201.Wave.fourierMultiplier m hm f) g =
        inner ℂ (𝓕 (P201.Wave.fourierMultiplier m hm f)) (𝓕 g) :=
      (MeasureTheory.Lp.inner_fourier_eq _ _).symm
    _ = inner ℂ (𝓕 f) (𝓕 (P201.Wave.fourierMultiplier m hm g)) := by
      rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [P201.Wave.fourierMultiplier_ae m hm f,
        P201.Wave.fourierMultiplier_ae m hm g] with x hfx hgx
      rw [hfx,hgx]
      simp only [RCLike.inner_apply, map_mul, starRingEnd_apply, hreal]
      ring
    _ = inner ℂ f (P201.Wave.fourierMultiplier m hm g) :=
      MeasureTheory.Lp.inner_fourier_eq _ _


/-- The ordinary scalar-linear pairing is the Hermitian inner product with
conjugation applied to its first input. -/
theorem l2_bilinear_eq_inner {n : ℕ} (f g : FrequencyL2 n) :
    (∫ x, f x * g x) = inner ℂ (P201.Wave.RealBridge.conjL2 f) g := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [P201.Wave.RealBridge.conjL2_ae f] with x hx
  simp only [RCLike.inner_apply, hx, map_mul, starRingEnd_apply, star_star]
  exact mul_comm _ _

/-- A real even Fourier symbol is symmetric for the scalar-linear
L² distribution pairing, without a conjugate in the test. -/
theorem fourierMultiplier_bilinear {n : ℕ} (m : Space n → ℝ)
    (hm : MemLp (fun x => (m x : ℂ)) ∞ volume) (heven : ∀ x, m (-x) = m x)
    (f g : FrequencyL2 n) :
    (∫ x, (P201.Wave.fourierMultiplier (fun x => (m x : ℂ)) hm f) x * g x) =
      ∫ x, f x * (P201.Wave.fourierMultiplier (fun x => (m x : ℂ)) hm g) x := by
  rw [l2_bilinear_eq_inner, l2_bilinear_eq_inner]
  rw [P201.Wave.RealBridge.commutes_conj_of_real_even_symbol
    (P201.Wave.fourierMultiplier (fun x => (m x : ℂ)) hm) m heven
    (fun f => P201.Wave.fourierMultiplier_ae _ hm f) f]
  exact fourierMultiplier_inner _ hm (fun x => by simp) _ _

/-- Scalar-linear transposition for the actual cosine propagator on ordinary L². -/
theorem cosineL2_bilinear {n : ℕ} (c t : ℝ) (f g : FrequencyL2 n) :
    (∫ x, (P201.Wave.cosineL2 n c t f) x * g x) =
      ∫ x, f x * (P201.Wave.cosineL2 n c t g) x := by
  apply fourierMultiplier_bilinear
    (fun x => cosineSymbol t (frequency n c x)) (P201.Wave.cosineSymbol_memLp n c t)
  intro x
  rw [P201.Wave.RealBridge.frequency_neg]

/-- Scalar-linear transposition for the actual sine propagator on ordinary L². -/
theorem sineL2_bilinear {n : ℕ} (c t : ℝ) (f g : FrequencyL2 n) :
    (∫ x, (P201.Wave.sineL2 n c t f) x * g x) =
      ∫ x, f x * (P201.Wave.sineL2 n c t g) x := by
  apply fourierMultiplier_bilinear
    (fun x => sineSymbol t (frequency n c x)) (P201.Wave.sineSymbol_memLp n c t)
  intro x
  rw [P201.Wave.RealBridge.frequency_neg]


/-- Removing the whole-space restriction preserves the scalar-linear pairing. -/
theorem wholeL2Standard_bilinear {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f g : WholeL2 n 𝕜) :
    (∫ x, (wholeL2Standard n 𝕜 f) x * (wholeL2Standard n 𝕜 g) x) =
      ∫ x, f x * g x := by
  apply integral_congr_ae
  filter_upwards [P201.Wave.wholeL2Standard_ae f,
    P201.Wave.wholeL2Standard_ae g] with x hfx hgx
  rw [hfx, hgx]

/-- A real even frequency symbol is symmetric for the shared whole-space
scalar-linear L² pairing. -/
theorem wholeFourierMultiplier_bilinear {n : ℕ} (m : Space n → ℝ)
    (hm : MemLp (fun x => (m x : ℂ)) ∞ volume) (heven : ∀ x, m (-x) = m x)
    (f g : WholeL2 n ℂ) :
    (∫ x, (P201.Wave.wholeFourierMultiplier (fun x => (m x : ℂ)) hm f) x * g x) =
      ∫ x, f x * (P201.Wave.wholeFourierMultiplier (fun x => (m x : ℂ)) hm g) x := by
  rw [← wholeL2Standard_bilinear, P201.Wave.wholeFourierMultiplier_standard,
    fourierMultiplier_bilinear m hm heven]
  rw [← P201.Wave.wholeFourierMultiplier_standard, wholeL2Standard_bilinear]

/-- Transposition for the actual complex cosine operator in the accepted family. -/
theorem complexC0_bilinear {n : ℕ} (c : ℝ) (hc : 0 < c) (t : ℝ)
    (f g : WholeL2 n ℂ) :
    (∫ x, ((P201.Wave.complexWaveOperators n c hc).C0 t f) x * g x) =
      ∫ x, f x * ((P201.Wave.complexWaveOperators n c hc).C0 t g) x := by
  apply wholeFourierMultiplier_bilinear
    (fun x => cosineSymbol t (frequency n c x)) (P201.Wave.cosineSymbol_memLp n c t)
  intro x
  rw [P201.Wave.RealBridge.frequency_neg]

/-- Transposition for the underlying L² value of the actual sine operator. -/
theorem complexS_bilinear {n : ℕ} (c : ℝ) (hc : 0 < c) (t : ℝ)
    (f g : WholeL2 n ℂ) :
    (∫ x, (hUnderlying ⊤ 1 ((P201.Wave.complexWaveOperators n c hc).S t f)) x * g x) =
      ∫ x, f x * (hUnderlying ⊤ 1 ((P201.Wave.complexWaveOperators n c hc).S t g)) x := by
  have hs (f : WholeL2 n ℂ) :
      wholeL2Standard n ℂ (hUnderlying ⊤ 1 ((P201.Wave.complexWaveOperators n c hc).S t f)) =
        P201.Wave.sineL2 n c t (wholeL2Standard n ℂ f) := by
    change wholeL2Standard n ℂ (hUnderlying ⊤ 1 (P201.Wave.sineH1 n c hc t f)) = _
    rw [P201.Wave.sineH1_underlying]
    exact (wholeL2Standard n ℂ).apply_symm_apply _
  rw [← wholeL2Standard_bilinear, hs, sineL2_bilinear, ← hs, wholeL2Standard_bilinear]

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform
open P201 P201Specs.Wave
namespace P201.Wave.Cauchy

/-- The scalar derivative multiplier agrees with the sine multiplier times
the exact wave Laplacian symbol. -/
theorem cosineDerivativeSymbol_laplacian (n : ℕ) (c t : ℝ) (ξ : Space n) :
    (cosineDerivativeSymbol t (frequency n c ξ) : ℂ) =
      (c ^ 2 : ℂ) * (sineSymbol t (frequency n c ξ) : ℂ) *
        (-((2 * Real.pi) ^ 2 : ℝ) * (‖ξ‖ ^ 2 : ℝ) : ℂ) := by
  by_cases hw : frequency n c ξ = 0
  · have hz : c = 0 ∨ ‖ξ‖ = 0 := by
      simpa only [frequency, P201Specs.Wave.frequency, mul_eq_zero,
        OfNat.ofNat_ne_zero, Real.pi_ne_zero, false_or] using hw
    rcases hz with hc | hξ
    · simp [P201.Wave.cosineDerivativeSymbol, P201Specs.Wave.cosineDerivativeSymbol, hw, hc, frequency, P201Specs.Wave.frequency]
    · simp [P201.Wave.cosineDerivativeSymbol, P201Specs.Wave.cosineDerivativeSymbol, hw, hξ]
  · simp only [P201.Wave.cosineDerivativeSymbol, P201Specs.Wave.cosineDerivativeSymbol,
      P201.Wave.sineSymbol, P201Specs.Wave.sineSymbol, ite_eq_right hw]
    have hwc : (frequency n c ξ : ℂ) ≠ 0 := by exact_mod_cast hw
    push_cast
    field_simp
    simp only [frequency, P201Specs.Wave.frequency]
    push_cast
    ring

/-- Whenever the spatial Laplacian of g is the L² field q, the first cosine
time derivative is c² times the sine propagator applied to q. The hypothesis
is stated as the exact radial Fourier equality and does not assume a solution. -/
theorem waveD_eq_sine_laplacian {n : ℕ} (c : ℝ)
    (W : WaveOperators n ℂ) (hW : WaveFamilyLaws c (ContinuousLinearMap.id ℝ ℂ) W)
    (g : WholeH1 n ℂ) (q : WholeL2 n ℂ)
    (hq : (𝓕 (wholeL2Standard n ℂ q) : FrequencyL2 n) =ᵐ[volume]
      fun ξ => (-((2 * Real.pi) ^ 2 : ℝ) * (‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g)) : FrequencyL2 n) ξ)
    (t : ℝ) :
    W.D t g = (c ^ 2 : ℂ) • hUnderlying ⊤ 1 (W.S t q) := by
  rcases hW with ⟨_, _, hS, hD, _⟩
  apply (wholeL2Standard n ℂ).injective
  apply (MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).injective
  rw [map_smul, map_smul]
  change (𝓕 (wholeL2Standard n ℂ (W.D t g)) : FrequencyL2 n) =
    (c ^ 2 : ℂ) • (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 (W.S t q))) : FrequencyL2 n)
  apply MeasureTheory.Lp.ext
  have hS' := hS t q
  have hD' := hD t g
  simp only [P201.Wave.embeddedFourier_complex] at hS' hD'
  filter_upwards [hS', hD', hq,
    MeasureTheory.Lp.coeFn_smul (c ^ 2 : ℂ)
      (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 (W.S t q))) : FrequencyL2 n)]
    with ξ hSξ hDξ hqξ hsmul
  rw [hDξ, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hSξ, hqξ, cosineDerivativeSymbol_laplacian]
  ring

end P201.Wave.Cauchy
end

noncomputable section
open Filter Set Topology
namespace P201.Wave.Cauchy

/-- Product rule for a strongly continuous operator family. The operator need
only have a strong derivative at the one fixed input v(t); no operator-norm
derivative and no derivative uniform in the input is assumed. -/
theorem hasDerivAt_strong_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ → E →L[ℝ] F)
    (hAcont : Continuous (fun p : ℝ × E => A p.1 p.2))
    {v : ℝ → E} {v' : E} {d : F} {t : ℝ}
    (hv : HasDerivAt v v' t)
    (hA : HasDerivAt (fun r => A r (v t)) d t) :
    HasDerivAt (fun r => A r (v r)) (A t v' + d) t := by
  have h1 : Tendsto (fun r => A r (slope v t r)) (𝓝[≠] t) (𝓝 (A t v')) := by
    exact hAcont.continuousAt.tendsto.comp
      ((tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hv.tendsto_slope)
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply (h1.add hA.tendsto_slope).congr'
  filter_upwards [] with r
  simp only [slope_def_module, map_smul, map_sub]
  module

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace P201.Wave.Cauchy.Uniqueness
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open HyperbolicWeakEnergyExistence HyperbolicWeakEnergyUniqueness

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Distributional identities on compact smooth spatial tests determine the
full H¹-dual-valued time derivative. The bounds are Bochner integrability,
not an assumed solution or a second strong derivative. -/
theorem derivativeValue_of_dense_evaluations {ι : Type*} (D : ι → V)
    (hD : DenseRange D) (T : ℝ)
    (b g : ℝ → StrongDual ℝ V)
    (hb : Integrable b (timeMeasureValue T))
    (hg : Integrable g (timeMeasureValue T))
    (heval : ∀ ψ : ι,
      derivativeValue T (fun t => b t (D ψ)) (fun t => g t (D ψ))) :
    derivativeValue T b g := by
  refine ⟨(show IntegrableOn b (Ioo 0 T) volume from hb).locallyIntegrableOn,
    (show IntegrableOn g (Ioo 0 T) volume from hg).locallyIntegrableOn, ?_⟩
  intro φ hφ
  have hi₁ : Integrable (fun t => deriv φ t • b t) (timeMeasureValue T) :=
    hb.smul_of_top_right ((hφ.1.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport
      hφ.2.1.deriv (timeMeasureValue T))
  have hi₂ : Integrable (fun t => φ t • g t) (timeMeasureValue T) :=
    hg.smul_of_top_right (hφ.1.continuous.memLp_top_of_hasCompactSupport
      hφ.2.1 (timeMeasureValue T))
  let A : StrongDual ℝ V := ∫ t, deriv φ t • b t ∂timeMeasureValue T
  let B : StrongDual ℝ V := -(∫ t, φ t • g t ∂timeMeasureValue T)
  have he : (A : V → ℝ) = B := by
    apply hD.equalizer A.continuous B.continuous
    funext ψ
    dsimp only [Function.comp_def, A, B]
    rw [ContinuousLinearMap.integral_apply hi₁, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.integral_apply hi₂]
    exact (heval ψ).2.2 φ hφ
  exact DFunLike.coe_injective he

/-- The original strong derivative supplies the vector-valued distributional graph. -/
theorem derivativeValue_of_continuous_derivative
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (u : ℝ → V) (v : ℝ → H)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun s => j.embedding (u s)) (v t) (Ici 0) t) :
    derivativeValue T (fun s => j.embedding (u s)) v := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have hJu : ContinuousOn (fun s => j.embedding (u s)) (Icc 0 T) :=
    j.embedding.continuous.comp_continuousOn hu
  have huI : Integrable (fun s => j.embedding (u s)) (timeMeasureValue T) :=
    (continuousOn_time_memLp (p := 1) hJu).integrable (by simp)
  have hvI : Integrable v (timeMeasureValue T) :=
    (continuousOn_time_memLp (p := 1) hv).integrable (by simp)
  apply GalerkinNet.derivativeValue_of_integral_increments T hT _ _ huI hvI
  intro s t
  have hsub : uIcc (s : ℝ) (t : ℝ) ⊆ Icc 0 T :=
    ordConnected_Icc.uIcc_subset s.property t.property
  apply Eq.symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right
    (hJu.mono hsub) _ (hv.mono hsub).intervalIntegrable
  intro x hx
  have hx0 : 0 ≤ x := by
    have hs := s.property.1
    have ht := t.property.1
    have hmin : 0 ≤ min (s : ℝ) (t : ℝ) := le_min hs ht
    exact hmin.trans hx.1.le
  exact (hd x hx0).mono (fun y hy => hx0.trans hy.le)

/-- Every strongly continuous curve satisfying the scalar weak wave equation
is a genuine weak-energy solution; no energy identity is assumed. -/
def continuousWeakEnergySolution
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (ha : ScalarC1 T a)
    (g : V) (h : H) (f : timeLpValue H 2 T)
    (u : ℝ → V) (v : ℝ → H)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun s => j.embedding (u s)) (v t) (Ici 0) t)
    (hu0 : u 0 = g) (hv0 : v 0 = h)
    (heq : WaveTestEquation j T a u v f) :
    WeakEnergySolution j T a g h f where
  displacement := u
  velocity := v
  acceleration := fun t => pivotValue j (f t) - a t (u t)
  displacement_mem := continuousOn_time_memLp hu
  pivot_displacement_mem := continuousOn_time_memLp
    (j.embedding.continuous.comp_continuousOn hu)
  velocity_mem := continuousOn_time_memLp hv
  dual_velocity_mem := continuousOn_time_memLp
    ((pivotValue j).continuous.comp_continuousOn hv)
  acceleration_mem := acceleration_memLp j T a ha u f (continuousOn_time_memLp hu)
  displacement_derivative := derivativeValue_of_continuous_derivative j T hT u v hu hv hd
  velocity_derivative := velocity_derivative_of_wave_tests j T a ha u v f
    (continuousOn_time_memLp hu) (continuousOn_time_memLp hv) heq
  equation := Filter.Eventually.of_forall (fun t => sub_add_cancel _ _)
  displacement_weak := fun L => L.continuous.comp_continuousOn hu
  velocity_weak := fun L => L.continuous.comp_continuousOn hv
  initial_displacement := hu0
  initial_velocity := hv0

/-- Zero-forcing continuous curves fit the library graph once the wave
identity is proved on a dense family of spatial tests. -/
def homogeneousWeakEnergySolutionOfDenseTests {ι : Type*}
    (D : ι → V) (hD : DenseRange D)
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (ha : ScalarC1 T a)
    (u : ℝ → V) (v : ℝ → H)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun s => j.embedding (u s)) (v t) (Ici 0) t)
    (hu0 : u 0 = 0) (hv0 : v 0 = 0)
    (hscalar : ∀ ψ : ι, derivativeValue T
      (fun t => inner ℝ (v t) (j.embedding (D ψ)))
      (fun t => -(a t (u t) (D ψ)))) :
    WeakEnergySolution j T a 0 0 (0 : timeLpValue H 2 T) := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioo 0 T)))
  have hum : MemLp u 2 (timeMeasureValue T) := continuousOn_time_memLp hu
  have hvm : MemLp v 2 (timeMeasureValue T) := continuousOn_time_memLp hv
  have hb : Integrable (fun t => pivotValue j (v t)) (timeMeasureValue T) :=
    (((pivotValue j).comp_memLp' hvm).integrable (by norm_num))
  have hg : Integrable (fun t => -(a t (u t))) (timeMeasureValue T) :=
    ((form_apply_memLp T a ha u hum).neg.integrable (by norm_num))
  refine {
    displacement := u
    velocity := v
    acceleration := fun t => -(a t (u t))
    displacement_mem := continuousOn_time_memLp hu
    pivot_displacement_mem := continuousOn_time_memLp
      (j.embedding.continuous.comp_continuousOn hu)
    velocity_mem := continuousOn_time_memLp hv
    dual_velocity_mem := (pivotValue j).comp_memLp' hvm
    acceleration_mem := (form_apply_memLp T a ha u hum).neg
    displacement_derivative := derivativeValue_of_continuous_derivative j T hT u v hu hv hd
    velocity_derivative := ?_
    equation := ?_
    displacement_weak := fun L => L.continuous.comp_continuousOn hu
    velocity_weak := fun L => L.continuous.comp_continuousOn hv
    initial_displacement := hu0
    initial_velocity := hv0 }
  · apply derivativeValue_of_dense_evaluations D hD T _ _ hb hg
    intro ψ
    simpa only [← pivotInjection_apply, neg_apply] using! hscalar ψ
  · filter_upwards [Lp.coeFn_zero (E := H) (p := 2) (μ := timeMeasureValue T)] with t ht
    simp only [ht, Pi.zero_apply, map_zero, neg_add_cancel]

/-- Uniqueness requires the dense test equation only for the homogeneous
zero-data difference. Thus no L²-time assumption on a common forcing enters. -/
theorem homogeneous_unique_of_dense_tests {ι : Type*}
    (D : ι → V) (hD : DenseRange D)
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (u : ℝ → V) (v : ℝ → H)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun s => j.embedding (u s)) (v t) (Ici 0) t)
    (hu0 : u 0 = 0) (hv0 : v 0 = 0)
    (hscalar : ∀ ψ : ι, derivativeValue T
      (fun t => inner ℝ (v t) (j.embedding (D ψ)))
      (fun t => -(a t (u t) (D ψ)))) :
    ∀ t ∈ Icc 0 T, u t = 0 ∧ v t = 0 := by
  let z := homogeneousWeakEnergySolutionOfDenseTests D hD j T hT a ha.scalarC1
    u v hu hv hd hu0 hv0 hscalar
  let w := homogeneousWeakEnergySolutionOfDenseTests D hD j T hT a ha.scalarC1
    (fun _ => 0) (fun _ => 0) continuousOn_const continuousOn_const
    (fun t ht => by simpa only [map_zero] using
      hasDerivWithinAt_const t (Ici (0 : ℝ)) (0 : H)) rfl rfl
    (fun ψ => by simpa only [inner_zero_left, map_zero, zero_apply, neg_zero]
      using! (derivativeValue_zero (E := ℝ) T))
  exact (weak_uniqueness j T hT a α C ha 0 0 0 z w).1

/-- Comparison after the PDE has been extended from smooth spatial tests
into the full H¹ scalar weak equation. Applies to the zero-forcing difference
regardless of the time-integrability of the common original forcing. -/
theorem continuous_weak_wave_unique
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (g : V) (h : H) (f : timeLpValue H 2 T)
    (u₁ u₂ : ℝ → V) (v₁ v₂ : ℝ → H)
    (hu₁ : ContinuousOn u₁ (Icc 0 T)) (hv₁ : ContinuousOn v₁ (Icc 0 T))
    (hu₂ : ContinuousOn u₂ (Icc 0 T)) (hv₂ : ContinuousOn v₂ (Icc 0 T))
    (hd₁ : ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun s => j.embedding (u₁ s)) (v₁ t) (Ici 0) t)
    (hd₂ : ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun s => j.embedding (u₂ s)) (v₂ t) (Ici 0) t)
    (hu₁0 : u₁ 0 = g) (hv₁0 : v₁ 0 = h)
    (hu₂0 : u₂ 0 = g) (hv₂0 : v₂ 0 = h)
    (heq₁ : WaveTestEquation j T a u₁ v₁ f)
    (heq₂ : WaveTestEquation j T a u₂ v₂ f) :
    ∀ t ∈ Icc 0 T, u₁ t = u₂ t ∧ v₁ t = v₂ t := by
  let z := continuousWeakEnergySolution j T hT a ha.scalarC1 g h f
    u₁ v₁ hu₁ hv₁ hd₁ hu₁0 hv₁0 heq₁
  let w := continuousWeakEnergySolution j T hT a ha.scalarC1 g h f
    u₂ v₂ hu₂ hv₂ hd₂ hu₂0 hv₂0 heq₂
  exact (weak_uniqueness j T hT a α C ha g h f z w).1

end P201.Wave.Cauchy.Uniqueness
end

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace P201.Wave.Cauchy.Uniqueness
open P201Specs.Wave
open P201.Wave.RealBridge
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec

variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- Actual shared H¹ first coordinate derivative as a bounded linear map. -/
def firstDerivativeCLM (j : Fin n) : WholeH1 n 𝕜 →L[𝕜] WholeL2 n 𝕜 :=
  (PiLp.proj (𝕜 := 𝕜) 2 (fun _ : P102.U4.SobolevIndex n 1 => WholeL2 n 𝕜)
    (⟨{j}, by simp⟩ : P102.U4.SobolevIndex n 1)).comp
      (P201Specs.hilbertSubmodule 𝕜 ⊤ 1).subtypeL

@[simp] theorem firstDerivativeCLM_apply (j : Fin n) (u : WholeH1 n 𝕜) :
    firstDerivativeCLM j u = hFirstDerivative u j := rfl

/-- A compact smooth spatial test as the full H¹ graph. -/
def testH1 (φ : P102.U4.WholeTests n 𝕜) : WholeH1 n 𝕜 :=
  (P201Specs.hToW 𝕜 ⊤ 1).symm
    (P102.U4.smoothTest_hasSobolevRepresentative 1 2 φ).choose

lemma testH1_underlying_ae (φ : P102.U4.WholeTests n 𝕜) :
    (hUnderlying ⊤ 1 (testH1 φ) : Space n → 𝕜) =ᵐ[volume] φ := by
  have hr := (P102.U4.smoothTest_hasSobolevRepresentative 1 2 φ).choose_spec
    (P102.U4.zeroSobolevIndex n 1)
  change (P102.U4.sobolevUnderlying
    (P201Specs.hToW 𝕜 ⊤ 1 (testH1 φ)) : Space n → 𝕜) =ᵐ[volume] φ
  simp only [testH1, ContinuousLinearEquiv.apply_symm_apply]
  simpa [P102.U4.sobolevUnderlying, P102.U4.zeroSobolevIndex,
    P102.U4.multiPartial, P102.U4.partialWord] using hr

/-- Full H¹ is dense in the actual whole-space L² pivot. -/
theorem h1Underlying_denseRange :
    DenseRange (hUnderlying (𝕜 := 𝕜) (⊤ : Domain n) 1) := by
  let A := SchwartzMap.toLpCLM ℝ 𝕜 2 (volume : Measure (Space n))
  have hd : DenseRange (A ∘ P102.U4.testToSchwartz n 𝕜) :=
    (SchwartzMap.denseRange_toLpCLM (by simp : (2 : ℝ≥0∞) ≠ ⊤)).comp
      (P102.U4.testToSchwartz_denseRange n 𝕜) A.continuous
  have hd' : DenseRange (fun φ : P102.U4.WholeTests n 𝕜 =>
      (wholeL2Standard n 𝕜).symm (A (P102.U4.testToSchwartz n 𝕜 φ))) :=
    (wholeL2Standard n 𝕜).symm.surjective.denseRange.comp hd
      (wholeL2Standard n 𝕜).symm.continuous
  intro f
  apply closure_mono (s := Set.range (fun φ : P102.U4.WholeTests n 𝕜 =>
      (wholeL2Standard n 𝕜).symm (A (P102.U4.testToSchwartz n 𝕜 φ)))) _ (hd' f)
  rintro z ⟨φ, rfl⟩
  refine ⟨testH1 φ, ?_⟩
  apply (wholeL2Standard n 𝕜).injective
  dsimp only
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply MeasureTheory.Lp.ext
  filter_upwards [wholeL2Standard_ae (hUnderlying ⊤ 1 (testH1 φ)),
    testH1_underlying_ae φ, (P102.U4.testToSchwartz n 𝕜 φ).coeFn_toLp 2 volume] with x h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

lemma testH1_of_represents (φ : P102.U4.WholeTests n 𝕜)
    (v : P102.U4.Sobolev 𝕜 ⊤ 1 2) (hv : P102.U4.RepresentsSobolev φ v) :
    testH1 φ = (P201Specs.hToW 𝕜 ⊤ 1).symm v := by
  apply (P201Specs.hToW 𝕜 ⊤ 1).injective
  simp only [testH1, ContinuousLinearEquiv.apply_symm_apply]
  apply P102.U4.sobolevUnderlying_injective ⊤ 1 2
  apply MeasureTheory.Lp.ext
  have he := ((P102.U4.smoothTest_hasSobolevRepresentative 1 2 φ).choose_spec
    (P102.U4.zeroSobolevIndex n 1)).trans (hv (P102.U4.zeroSobolevIndex n 1)).symm
  simpa [P102.U4.sobolevUnderlying, domainMeasure] using he

/-- Compact smooth tests are dense in the full shared H¹ norm. -/
theorem testH1_denseRange : DenseRange (testH1 (n := n) (𝕜 := 𝕜)) := by
  intro u
  obtain ⟨φ, v, hv, hlim, herr⟩ := P102.U4.wholeSpace_density 1 2 (by simp)
    (P201Specs.hToW 𝕜 ⊤ 1 u)
  have he (k : ℕ) := testH1_of_represents (φ k) (v k) (hv k)
  have hlim' : Tendsto (fun k => testH1 (φ k)) atTop (𝓝 u) := by
    simp_rw [he]
    simpa only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_def] using!
      ((P201Specs.hToW 𝕜 ⊤ 1).symm.continuous.tendsto _).comp hlim
  exact mem_closure_of_tendsto hlim' (Filter.Eventually.of_forall (fun k => ⟨φ k, rfl⟩))

lemma testH1_derivative_ae (φ : P102.U4.WholeTests n 𝕜) (j : Fin n) :
    (hFirstDerivative (testH1 φ) j : Space n → 𝕜) =ᵐ[volume]
      P102.U4.multiPartial φ ({j} : MultiIndex n) := by
  change (P102.U4.sobolevDerivative
    (P201Specs.hToW 𝕜 ⊤ 1 (testH1 φ)) ⟨{j}, by simp⟩ : Space n → 𝕜) =ᵐ[volume] _
  simp only [testH1, ContinuousLinearEquiv.apply_symm_apply]
  exact (P102.U4.smoothTest_hasSobolevRepresentative 1 2 φ).choose_spec ⟨{j}, by simp⟩

/-- A single weak derivative transposes onto the derivative of a compact test. -/
lemma weak_firstDerivative_pairing (u : WholeH1 n 𝕜) (j : Fin n)
    (φ : P102.U4.WholeTests n 𝕜) :
    (∫ x : Space n, hUnderlying ⊤ 1 u x *
      P102.U4.testPartialWord ⊤ [j,j] φ x) =
      -(∫ x : Space n, hFirstDerivative u j x *
        P102.U4.testPartialWord ⊤ [j] φ x) := by
  have h := (P102.U4.distributionPartial_eq_regularLp_iff ⊤ 2
    ({j} : MultiIndex n) (hUnderlying ⊤ 1 u) (hFirstDerivative u j)).mp
      (hilbertDerivativeDistribution ⊤ 1 u ⟨{j}, by simp⟩)
  have he := h (P102.U4.testPartialWord ⊤ [j] φ)
  simp only [Multiset.card_singleton, Multiset.sort_singleton, pow_one,
    neg_one_mul, P102.U4.lpTestPairing_eq_integral] at he
  have hd : P102.U4.testPartialWord ⊤ [j] (P102.U4.testPartialWord ⊤ [j] φ) =
      P102.U4.testPartialWord ⊤ [j,j] φ := rfl
  rw [hd] at he
  simpa [domainMeasure] using congrArg Neg.neg he.symm

lemma testPartialWord_twice (φ : P102.U4.WholeTests n 𝕜) (j : Fin n) :
    (P102.U4.testPartialWord ⊤ [j,j] φ : Space n → 𝕜) =
      P102.U4.multiPartial φ ({j,j} : MultiIndex n) := by
  rw [P102.U4.testPartialWord_coe]
  simp [P102.U4.multiPartial, Multiset.sort_cons]

/-- Whole-space weak spatial integration by parts at exactly H¹ regularity. -/
lemma weak_laplacian_pairing (u : WholeH1 n 𝕜)
    (φ : P102.U4.WholeTests n 𝕜) :
    (∫ x : Space n, hUnderlying ⊤ 1 u x * laplacian φ x) =
      -∑ j : Fin n, ∫ x : Space n, hFirstDerivative u j x *
        P102.U4.testPartialWord ⊤ [j] φ x := by
  have hI (j : Fin n) : Integrable (fun x : Space n =>
      hUnderlying ⊤ 1 u x * P102.U4.testPartialWord ⊤ [j,j] φ x) := by
    simpa [domainMeasure, P201Specs.domainMeasure] using integrable_lp_test ⊤ (hUnderlying ⊤ 1 u)
      (P102.U4.testPartialWord ⊤ [j,j] φ)
  have hlap (x : Space n) : laplacian φ x =
      ∑ j : Fin n, P102.U4.testPartialWord ⊤ [j,j] φ x := by
    simp only [laplacian, P201Specs.laplacian, testPartialWord_twice]
  simp_rw [hlap, Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => hI j)]
  simp_rw [weak_firstDerivative_pairing]
  simp only [Finset.sum_neg_distrib]

/-- Conjugation preserves the actual compact smooth test space. -/
def conjugateTest (φ : P102.U4.WholeTests n 𝕜) : P102.U4.WholeTests n 𝕜 :=
  TestFunction.postcompCLM RCLike.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap φ

@[simp] lemma conjugateTest_apply (φ : P102.U4.WholeTests n 𝕜) (x : Space n) :
    conjugateTest φ x = star (φ x) := rfl

lemma testPartialWord_conjugate (φ : P102.U4.WholeTests n 𝕜) (j : Fin n) :
    P102.U4.testPartialWord ⊤ [j] (conjugateTest φ) =
      conjugateTest (P102.U4.testPartialWord ⊤ [j] φ) :=
  testPartial_postcomp ⊤ _ j φ

lemma lp_inner_eq_real_pairing_of_ae (f g : WholeL2 n 𝕜)
    (φ : P102.U4.WholeTests n 𝕜)
    (hg : (g : Space n → 𝕜) =ᵐ[volume] φ) :
    inner ℝ f g = RCLike.re (∫ x : Space n, f x * conjugateTest φ x) := by
  have hI : Integrable (fun x : Space n => f x * conjugateTest φ x) := by
    simpa [domainMeasure, P201Specs.domainMeasure] using integrable_lp_test ⊤ f (conjugateTest φ)
  rw [← integral_re hI, real_inner_comm, L2.inner_def]
  simp only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  change RCLike.re (f x * star (g x)) = RCLike.re (f x * conjugateTest φ x)
  simp only [hx, conjugateTest_apply]

lemma testH1_inner_pairing (f : WholeL2 n 𝕜) (φ : P102.U4.WholeTests n 𝕜) :
    inner ℝ f (hUnderlying ⊤ 1 (testH1 φ)) =
      RCLike.re (∫ x : Space n, f x * conjugateTest φ x) :=
  lp_inner_eq_real_pairing_of_ae f _ φ (testH1_underlying_ae φ)

lemma testH1_derivative_inner_pairing (u : WholeH1 n 𝕜)
    (φ : P102.U4.WholeTests n 𝕜) (j : Fin n) :
    inner ℝ (hFirstDerivative u j) (hFirstDerivative (testH1 φ) j) =
      RCLike.re (∫ x : Space n, hFirstDerivative u j x *
        P102.U4.testPartialWord ⊤ [j] (conjugateTest φ) x) := by
  rw [testPartialWord_conjugate]
  apply lp_inner_eq_real_pairing_of_ae
  simpa only [P102.U4.testPartialWord_coe, P102.U4.multiPartial,
    Multiset.sort_singleton] using testH1_derivative_ae φ j

local instance realInnerProductH1 : InnerProductSpace ℝ (WholeH1 n 𝕜) :=
  inferInstanceAs (InnerProductSpace ℝ
    ((P201Specs.hilbertSubmodule 𝕜 ⊤ 1).restrictScalars ℝ))

/-- The real Hilbert triple also covers complex fields by scalar restriction. -/
def wholeSpaceHilbertTriple (n : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    HilbertTriple (WholeH1 n 𝕜) (WholeL2 n 𝕜) where
  embedding := (hUnderlying ⊤ 1).restrictScalars ℝ
  injective := hilbertUnderlyingInjective ⊤ 1
  denseRange := h1Underlying_denseRange

/-- The symmetric bounded wave form uses exactly the shared weak derivatives. -/
def waveForm (n : ℕ) (𝕜 : Type) [RCLike 𝕜] (c : ℝ) : Form (WholeH1 n 𝕜) :=
  c ^ 2 • ∑ j : Fin n,
    (innerSL ℝ (E := WholeL2 n 𝕜)).bilinearComp
      ((firstDerivativeCLM j).restrictScalars ℝ)
      ((firstDerivativeCLM j).restrictScalars ℝ)

@[simp] theorem waveForm_apply (c : ℝ) (u v : WholeH1 n 𝕜) :
    waveForm n 𝕜 c u v = c ^ 2 * ∑ j : Fin n,
      inner ℝ (hFirstDerivative u j) (hFirstDerivative v j) := by
  simp [waveForm, ContinuousLinearMap.bilinearComp_apply]

lemma waveForm_test_pairing (c : ℝ) (u : WholeH1 n 𝕜)
    (φ : P102.U4.WholeTests n 𝕜) :
    c ^ 2 * RCLike.re (∫ x : Space n,
      hUnderlying ⊤ 1 u x * laplacian (conjugateTest φ) x) =
      -waveForm n 𝕜 c u (testH1 φ) := by
  have he := congrArg RCLike.re (weak_laplacian_pairing u (conjugateTest φ))
  simp only [map_neg, map_sum] at he
  simp_rw [← testH1_derivative_inner_pairing] at he
  rw [he, waveForm_apply]
  ring

lemma waveForm_hypotheses (c : ℝ) (hc : 0 < c) (T : ℝ) :
    FormHypotheses (wholeSpaceHilbertTriple n 𝕜) T
      (fun _ => waveForm n 𝕜 c) (c ^ 2) (c ^ 2) where
  scalarC1 := fun _ _ => contDiffOn_const
  symmetric := by
    intro t ht u v
    simp only [waveForm_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact real_inner_comm _ _
  alpha_pos := sq_pos_of_pos hc
  shift_nonneg := sq_nonneg c
  garding := by
    intro t ht u
    simp only [waveForm_apply, real_inner_self_eq_norm_sq]
    change c ^ 2 * ‖u‖ ^ 2 - c ^ 2 * ‖hUnderlying ⊤ 1 u‖ ^ 2 ≤ _
    rw [h1_norm_sq]
    ring_nf
    exact le_rfl

end P201.Wave.Cauchy.Uniqueness
end

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set TopologicalSpace Topology Filter
open scoped ENNReal ContDiff
open P201Specs P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201.Wave.Cauchy.TestSlices

def conjugateL2Map {n : ℕ} {𝕜 : Type} [RCLike 𝕜] : WholeL2 n 𝕜 →L[ℝ] WholeL2 n 𝕜 :=
  RCLike.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 (P201Specs.domainMeasure ⊤)

def scalarPair {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (f g : WholeL2 n 𝕜) : 𝕜 :=
  inner 𝕜 (conjugateL2Map f) g

theorem scalarPair_eq_integral {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (f g : WholeL2 n 𝕜) :
    scalarPair f g = ∫ x : Space n, f x * g x := by
  unfold scalarPair
  rw [L2.inner_def]
  change (∫ x : Space n, inner 𝕜 (conjugateL2Map f x) (g x) ∂P201Specs.domainMeasure ⊤) = _
  simp only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ]
  apply integral_congr_ae
  have he : (conjugateL2Map f : Space n → 𝕜) =ᵐ[volume] (fun x => star (f x)) := by
    let L : 𝕜 →L[ℝ] 𝕜 := (RCLike.conjLIE : 𝕜 ≃ₗᵢ[ℝ] 𝕜).toContinuousLinearEquiv.toContinuousLinearMap
    have h := L.coeFn_compLpL (p := 2) (μ := P201Specs.domainMeasure (⊤ : Domain n)) f
    change (conjugateL2Map f : Space n → 𝕜) =ᵐ[P201Specs.domainMeasure (⊤ : Domain n)] (fun x => L (f x)) at h
    simpa only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ, L,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
      RCLike.conjLIE_apply, starRingEnd_apply] using h
  filter_upwards [he] with x hx
  rw [hx, RCLike.inner_apply]
  simp only [starRingEnd_apply, star_star]
  exact mul_comm _ _

def scalarPairCLM {n : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    WholeL2 n 𝕜 →L[𝕜] WholeL2 n 𝕜 →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing (P201Specs.domainMeasure ⊤) 2 2

theorem scalarPairCLM_apply {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (f g : WholeL2 n 𝕜) :
    scalarPairCLM f g = scalarPair f g := by
  rw [scalarPair_eq_integral]
  unfold scalarPairCLM
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  simp only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ,
    ContinuousLinearMap.mul_apply']

theorem continuous_scalarPair {n : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    Continuous (fun p : WholeL2 n 𝕜 × WholeL2 n 𝕜 => scalarPair p.1 p.2) :=
  continuous_inner.comp ((conjugateL2Map.continuous.comp continuous_fst).prodMk continuous_snd)

theorem scalarPair_norm_le {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (f g : WholeL2 n 𝕜) :
    ‖scalarPair f g‖ ≤ ‖(conjugateL2Map : WholeL2 n 𝕜 →L[ℝ] WholeL2 n 𝕜)‖ * ‖f‖ * ‖g‖ :=
  (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (conjugateL2Map.le_opNorm f) (norm_nonneg _))

 theorem integrableOn_scalarPair {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : ℝ → WholeL2 n 𝕜) (hf : LocallyIntegrableForcing f)
    (v : ℝ → WholeL2 n 𝕜) (hv : Continuous v) (hvc : HasCompactSupport v) :
    IntegrableOn (fun t => scalarPair (f t) (v t)) (Ioi (0 : ℝ)) := by
  obtain ⟨R,hR⟩ := hvc.bddAbove
  let T := max R 0
  have hT : 0 ≤ T := le_max_right _ _
  have hv0 (t : ℝ) (ht : T < t) : v t = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hts
    have hr := hR hts
    have hRT : R ≤ T := le_max_left _ _
    linarith
  obtain ⟨B,hB⟩ := hv.bounded_above_of_compact_support hvc
  let C := ‖(conjugateL2Map : WholeL2 n 𝕜 →L[ℝ] WholeL2 n 𝕜)‖
  let f₀ := (Icc 0 T).indicator f
  have hf₀ : Integrable f₀ := (integrable_indicator_iff measurableSet_Icc).mpr (hf T hT)
  have hC : 0 ≤ C := norm_nonneg (conjugateL2Map : WholeL2 n 𝕜 →L[ℝ] WholeL2 n 𝕜)
  have hpair : Integrable (fun t => scalarPair (f₀ t) (v t)) := by
    apply ((hf₀.norm.const_mul C).mul_const B).mono'
      (continuous_scalarPair.comp_aestronglyMeasurable (hf₀.aestronglyMeasurable.prodMk hv.aestronglyMeasurable))
    exact Eventually.of_forall fun t => (scalarPair_norm_le (f₀ t) (v t)).trans
      (mul_le_mul_of_nonneg_left (hB t) (mul_nonneg hC (norm_nonneg _)))
  apply hpair.integrableOn.congr_fun _ measurableSet_Ioi
  intro t ht
  change scalarPair (f₀ t) (v t) = scalarPair (f t) (v t)
  by_cases htT : t ≤ T
  · simp only [f₀, indicator_of_mem (show t ∈ Icc 0 T from ⟨ht.le,htT⟩)]
  · rw [hv0 t (lt_of_not_ge htT)]
    simp only [scalarPair, inner_zero_right]

 theorem integrableOn_forcing_test_pairing {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : ℝ → WholeL2 n 𝕜) (hf : LocallyIntegrableForcing f) (φ : SpacetimeTest n 𝕜) :
    IntegrableOn (fun t => ∫ x : Space n, f t x * φ (t,x)) (Ioi (0 : ℝ)) := by
  have hp := integrableOn_scalarPair f hf (wholeSliceL2 φ) (wholeSliceL2_continuous φ)
    (wholeSliceL2_hasCompactSupport φ)
  apply hp.congr_fun _ measurableSet_Ioi
  intro t _
  change scalarPair (f t) (wholeSliceL2 φ t) = _
  rw [scalarPair_eq_integral]
  apply integral_congr_ae
  filter_upwards [wholeSliceL2_ae φ t] with x hx
  rw [hx]

def spaceDerivTest {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (j : Fin n) : SpacetimeTest n 𝕜 :=
  TestFunction.lineDerivCLM ℝ (0, coordinate n j) φ

theorem spatialSlice_spaceDerivTest {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (j : Fin n) (t : ℝ) :
    spatialSlice (spaceDerivTest φ j) t =
      TestFunction.lineDerivCLM 𝕜 (coordinate n j) (spatialSlice φ t) := by
  ext x
  change TestFunction.lineDerivCLM ℝ (0,coordinate n j) φ (t,x) = _
  rw [TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ (by simp),
    TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ (by simp)]
  have hd := ((φ.contDiff.differentiable (by simp)).differentiableAt
    (x := (t,x))).hasFDerivAt
  have he := (hd.comp x (hasFDerivAt_prodMk_right t x)).fderiv
  have he' := congrArg (fun L : Space n →L[ℝ] 𝕜 => L (coordinate n j)) he
  exact he'.symm

def spaceWordTest {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) : List (Fin n) → SpacetimeTest n 𝕜
  | [] => φ
  | i :: l => spaceDerivTest (spaceWordTest φ l) i

theorem spatialSlice_spaceWordTest {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (l : List (Fin n)) (t : ℝ) :
    spatialSlice (spaceWordTest φ l) t = P102.U4.testPartialWord ⊤ l (spatialSlice φ t) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [spaceWordTest, spatialSlice_spaceDerivTest, ih, P102.U4.testPartialWord,
      ContinuousLinearMap.comp_apply]

def spaceLaplacianTest {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) : SpacetimeTest n 𝕜 :=
  ∑ i : Fin n, spaceWordTest φ (({i,i} : MultiIndex n).sort (· ≤ ·))

theorem spaceLaplacianTest_apply {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) (x : Space n) :
    spaceLaplacianTest φ (t,x) = P201Specs.laplacian (fun y => φ (t,y)) x := by
  change ((FunLike.coeAddMonoidHom (SpacetimeTest n 𝕜) (ℝ × Space n) 𝕜)
    (∑ i : Fin n, spaceWordTest φ (({i,i} : MultiIndex n).sort (· ≤ ·)))) (t,x) = _
  rw [map_sum, Finset.sum_apply]
  change (∑ i : Fin n, spaceWordTest φ (({i,i} : MultiIndex n).sort (· ≤ ·)) (t,x)) = _
  change (∑ i : Fin n, spatialSlice (spaceWordTest φ (({i,i} : MultiIndex n).sort (· ≤ ·))) t x) = _
  simp only [spatialSlice_spaceWordTest, P102.U4.testPartialWord_coe]
  rfl

def spacetimeWaveTest {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (φ : SpacetimeTest n 𝕜) : SpacetimeTest n 𝕜 :=
  timeDerivTest (timeDerivTest φ) - c^2 • spaceLaplacianTest φ

theorem spacetimeWaveTest_apply {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (φ : SpacetimeTest n 𝕜) (t : ℝ) (x : Space n) :
    spacetimeWaveTest c φ (t,x) = testWaveOperator c φ t x := by
  simp only [spacetimeWaveTest, sub_apply, smul_apply, timeDerivTest_apply,
    spaceLaplacianTest_apply, testWaveOperator]

 theorem integrableOn_solution_test_pairing {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : ℝ → WholeH1 n 𝕜) (hu : ContinuousOn u (Ici (0 : ℝ)))
    (c : ℝ) (φ : SpacetimeTest n 𝕜) :
    IntegrableOn (fun t => ∫ x : Space n, hUnderlying ⊤ 1 (u t) x *
      testWaveOperator c φ t x) (Ioi (0 : ℝ)) := by
  have hf : LocallyIntegrableForcing (fun t => hUnderlying ⊤ 1 (u t)) := by
    intro T hT
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (hUnderlying (𝕜 := 𝕜) (⊤ : Domain n) 1).continuous.comp_continuousOn
      (hu.mono (fun _ ht => ht.1))
  simpa only [spacetimeWaveTest_apply] using
    integrableOn_forcing_test_pairing (fun t => hUnderlying ⊤ 1 (u t)) hf (spacetimeWaveTest c φ)

end P201.Wave.Cauchy.TestSlices
end

noncomputable section
open MeasureTheory Set TopologicalSpace Topology Filter
open scoped ENNReal ContDiff
open P201Specs P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201.Wave.Cauchy.TestSlices

theorem wholeSliceL2_deriv {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) : deriv (wholeSliceL2 φ) = wholeSliceL2 (timeDerivTest φ) :=
  funext fun t => (wholeSliceL2_hasDerivAt φ t).deriv

theorem wholeSliceL2_contDiff_nat {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (k : ℕ) (φ : SpacetimeTest n 𝕜) : ContDiff ℝ k (wholeSliceL2 φ) := by
  induction k generalizing φ with
  | zero => exact contDiff_zero.mpr (wholeSliceL2_continuous φ)
  | succ k ih =>
    rw [show (↑(k + 1) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp, contDiff_succ_iff_deriv]
    refine ⟨fun t => (wholeSliceL2_hasDerivAt φ t).differentiableAt, ?_, ?_⟩
    · simp
    · rw [wholeSliceL2_deriv]
      exact ih _

theorem wholeSliceL2_contDiff {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) : ContDiff ℝ ∞ (wholeSliceL2 φ) :=
  contDiff_infty.mpr (fun k => wholeSliceL2_contDiff_nat k φ)

 theorem wholeSliceL2_tsupport_subset_timeSupport {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) : tsupport (wholeSliceL2 φ) ⊆ Prod.fst '' tsupport φ := by
  apply closure_minimal _ (φ.hasCompactSupport.image continuous_fst).isClosed
  intro t ht
  by_contra hn
  apply ht
  apply (wholeL2Standard n 𝕜).injective
  rw [map_zero]
  apply MeasureTheory.Lp.ext
  have he : wholeL2Standard n 𝕜 (wholeSliceL2 φ t) = standardSliceL2 φ t :=
    (wholeL2Standard n 𝕜).apply_symm_apply _
  rw [he]
  filter_upwards [standardSliceL2_ae φ t,
    MeasureTheory.Lp.coeFn_zero 𝕜 2 (volume : Measure (Space n))] with x hx hz
  rw [hx,hz]
  apply image_eq_zero_of_notMem_tsupport
  exact fun hp => hn ⟨(t,x),hp,rfl⟩

theorem wholeSliceL2_tsupport_pos {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) : tsupport (wholeSliceL2 φ) ⊆ Ioi (0 : ℝ) := by
  intro t ht
  obtain ⟨⟨s,x⟩,hs,hst⟩ := wholeSliceL2_tsupport_subset_timeSupport φ ht
  exact hst ▸ (φ.tsupport_subset hs).1

def l2TimeTest {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) :
    TestFunction (⟨Ioi (0 : ℝ),isOpen_Ioi⟩ : Opens ℝ) (WholeL2 n 𝕜) ⊤ where
  toFun := wholeSliceL2 φ
  contDiff' := wholeSliceL2_contDiff φ
  hasCompactSupport' := wholeSliceL2_hasCompactSupport φ
  tsupport_subset' := wholeSliceL2_tsupport_pos φ

end P201.Wave.Cauchy.TestSlices
end

noncomputable section
open MeasureTheory Set
open scoped FourierTransform
open P201 P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201.Wave.Cauchy

/-- A smooth spacetime test slice, represented in the actual full H¹ space. -/
def spacetimeH1Slice {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) : WholeH1 n 𝕜 :=
  Uniqueness.testH1 (TestSlices.spatialSlice φ t)

theorem spacetimeH1Slice_underlying {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    hUnderlying ⊤ 1 (spacetimeH1Slice φ t) = TestSlices.wholeSliceL2 φ t := by
  apply MeasureTheory.Lp.ext
  have he : (hUnderlying ⊤ 1 (spacetimeH1Slice φ t) : Space n → 𝕜) =ᵐ[volume]
      (TestSlices.wholeSliceL2 φ t : Space n → 𝕜) := by
    filter_upwards [Uniqueness.testH1_underlying_ae (TestSlices.spatialSlice φ t),
      TestSlices.wholeSliceL2_ae φ t] with x h₁ h₂
    exact h₁.trans h₂.symm
  simpa only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using he

theorem testL2_spatialSlice {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    testL2 (TestSlices.spatialSlice φ t) = TestSlices.standardSliceL2 φ t := rfl

/-- The spatial Laplacian of a smooth compact spacetime test as an L² slice. -/
def spatialLaplacianSliceL2 {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) : WholeL2 n 𝕜 :=
  (wholeL2Standard n 𝕜).symm
    (testL2 (TestSlices.laplacianTest (TestSlices.spatialSlice φ t)))

theorem spatialLaplacianSliceL2_fourier {n : ℕ}
    (φ : SpacetimeTest n ℂ) (t : ℝ) :
    (𝓕 (wholeL2Standard n ℂ (spatialLaplacianSliceL2 φ t)) : FrequencyL2 n) =ᵐ[volume]
      fun ξ => (-((2 * Real.pi) ^ 2 : ℝ) * (‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 (spacetimeH1Slice φ t))) : FrequencyL2 n) ξ := by
  rw [spacetimeH1Slice_underlying]
  simpa only [spatialLaplacianSliceL2, TestSlices.wholeSliceL2,
    LinearIsometryEquiv.apply_symm_apply, ← testL2_spatialSlice] using
    testL2_laplacian_fourier (TestSlices.spatialSlice φ t)

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set TopologicalSpace Topology Filter
open scoped ENNReal ContDiff
open P201Specs P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201.Wave.Cauchy.TestSlices

theorem wholeSliceL2_add {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ ψ : SpacetimeTest n 𝕜) (t : ℝ) :
    wholeSliceL2 (φ+ψ) t = wholeSliceL2 φ t + wholeSliceL2 ψ t := by
  apply MeasureTheory.Lp.ext
  change _ =ᵐ[volume.restrict (univ : Set (Space n))] _
  rw [Measure.restrict_univ]
  have hs : ((wholeSliceL2 φ t + wholeSliceL2 ψ t : WholeL2 n 𝕜) : Space n → 𝕜) =ᵐ[volume]
      (fun x => wholeSliceL2 φ t x + wholeSliceL2 ψ t x) := by
    have h := MeasureTheory.Lp.coeFn_add (wholeSliceL2 φ t) (wholeSliceL2 ψ t)
    simp only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] at h
    filter_upwards [h] with x hx
    exact hx
  filter_upwards [wholeSliceL2_ae (φ+ψ) t, wholeSliceL2_ae φ t,
    wholeSliceL2_ae ψ t,hs] with x hsum hφ hψ hLp
  simp only [hsum, hLp, hφ, hψ, add_apply]

theorem wholeSliceL2_sub {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ ψ : SpacetimeTest n 𝕜) (t : ℝ) :
    wholeSliceL2 (φ-ψ) t = wholeSliceL2 φ t - wholeSliceL2 ψ t := by
  apply MeasureTheory.Lp.ext
  change _ =ᵐ[volume.restrict (univ : Set (Space n))] _
  rw [Measure.restrict_univ]
  have hs : ((wholeSliceL2 φ t - wholeSliceL2 ψ t : WholeL2 n 𝕜) : Space n → 𝕜) =ᵐ[volume]
      (fun x => wholeSliceL2 φ t x - wholeSliceL2 ψ t x) := by
    have h := MeasureTheory.Lp.coeFn_sub (wholeSliceL2 φ t) (wholeSliceL2 ψ t)
    simp only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] at h
    filter_upwards [h] with x hx
    exact hx
  filter_upwards [wholeSliceL2_ae (φ-ψ) t, wholeSliceL2_ae φ t,
    wholeSliceL2_ae ψ t,hs] with x hsum hφ hψ hLp
  simp only [hsum, hLp, hφ, hψ, sub_apply]

theorem wholeSliceL2_real_smul {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : ℝ) (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    wholeSliceL2 (a • φ) t = a • wholeSliceL2 φ t := by
  apply MeasureTheory.Lp.ext
  change _ =ᵐ[volume.restrict (univ : Set (Space n))] _
  rw [Measure.restrict_univ]
  have hs : ((a • wholeSliceL2 φ t : WholeL2 n 𝕜) : Space n → 𝕜) =ᵐ[volume]
      (fun x => a • wholeSliceL2 φ t x) := by
    have h := MeasureTheory.Lp.coeFn_smul a (wholeSliceL2 φ t)
    simp only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] at h
    filter_upwards [h] with x hx
    exact hx
  filter_upwards [wholeSliceL2_ae (a • φ) t, wholeSliceL2_ae φ t, hs] with x ha hφ hLp
  simp only [ha, hLp, hφ, smul_apply]

theorem wholeSliceL2_smul {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : 𝕜) (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    wholeSliceL2 (a • φ) t = a • wholeSliceL2 φ t := by
  apply MeasureTheory.Lp.ext
  change _ =ᵐ[volume.restrict (univ : Set (Space n))] _
  rw [Measure.restrict_univ]
  have hs : ((a • wholeSliceL2 φ t : WholeL2 n 𝕜) : Space n → 𝕜) =ᵐ[volume]
      (fun x => a • wholeSliceL2 φ t x) := by
    have h := MeasureTheory.Lp.coeFn_smul a (wholeSliceL2 φ t)
    simp only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] at h
    filter_upwards [h] with x hx
    exact hx
  filter_upwards [wholeSliceL2_ae (a • φ) t, wholeSliceL2_ae φ t, hs] with x ha hφ hLp
  simp only [ha, hLp, hφ, smul_apply]

theorem wholeSliceL2_waveTest {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    wholeSliceL2 (spacetimeWaveTest c φ) t =
      deriv (deriv (wholeSliceL2 φ)) t - c^2 • wholeSliceL2 (spaceLaplacianTest φ) t := by
  rw [spacetimeWaveTest, wholeSliceL2_sub, wholeSliceL2_real_smul,
    wholeSliceL2_deriv, wholeSliceL2_deriv]

theorem wholeSliceL2_waveTest_eq {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    wholeSliceL2 (spacetimeWaveTest c φ) t =
      wholeSliceL2 (timeDerivTest (timeDerivTest φ)) t -
        c^2 • wholeSliceL2 (spaceLaplacianTest φ) t := by
  rw [spacetimeWaveTest, wholeSliceL2_sub, wholeSliceL2_real_smul]

theorem spatialSlice_spaceLaplacianTest {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    spatialSlice (spaceLaplacianTest φ) t = laplacianTest (spatialSlice φ t) := by
  ext x
  rw [spatialSlice_apply, spaceLaplacianTest_apply, laplacianTest_apply]
  rfl

end P201.Wave.Cauchy.TestSlices
end

set_option maxHeartbeats 200000

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform
open P201 P201Specs.Wave
namespace P201.Wave.Cauchy

/-- A vector-valued retarded Green identity for arbitrary moving L² tests.
The lifts and Laplacians are genuine spatial data, with the latter characterized
by the exact Fourier symbol. No second derivative of a solution is assumed. -/
theorem waveSine_green {n : ℕ} (c : ℝ)
    (W : WaveOperators n ℂ) (hW : WaveFamilyLaws c (ContinuousLinearMap.id ℝ ℂ) W)
    (Ψ Ψ' Ψ'' q : ℝ → WholeL2 n ℂ) (G : ℝ → WholeH1 n ℂ)
    (hG : ∀ t, hUnderlying ⊤ 1 (G t) = Ψ t)
    (hq : ∀ t, (𝓕 (wholeL2Standard n ℂ (q t)) : FrequencyL2 n) =ᵐ[volume]
      fun ξ => (-((2 * Real.pi) ^ 2 : ℝ) * (‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 (G t))) : FrequencyL2 n) ξ)
    (hΨ : ∀ t, HasDerivAt Ψ (Ψ' t) t)
    (hΨ' : ∀ t, HasDerivAt Ψ' (Ψ'' t) t)
    (hΨ'' : Continuous Ψ'') (hqc : Continuous q)
    (s T : ℝ) (hT : Ψ T = 0) (hT' : Ψ' T = 0) :
    (∫ t in s..T, hUnderlying ⊤ 1
      (W.S (t-s) (Ψ'' t - (c ^ 2 : ℂ) • q t))) = Ψ s := by
  have hWcopy := hW
  rcases hW with ⟨_, hCompat, _, _, hBound, hCcont, _, hScont, _, hCD, hSD,
    hC0, _, hS0, _⟩
  let U := hUnderlying (𝕜 := ℂ) (⊤ : Domain n) 1
  let A : ℝ → WholeL2 n ℂ →L[ℝ] WholeL2 n ℂ :=
    fun t => (U.comp (W.S (t-s))).restrictScalars ℝ
  let B : ℝ → WholeL2 n ℂ →L[ℝ] WholeL2 n ℂ :=
    fun t => (W.C0 (t-s)).restrictScalars ℝ
  have hSjoint := continuous_family_apply W.S
    (fun r => Real.sqrt (r ^ 2 + c⁻¹ ^ 2)) (by fun_prop)
    (fun r => (hBound r).2.2.1) hScont
  have hCjoint := continuous_family_apply W.C0 (fun _ => 1) continuous_const
    (fun r => (hBound r).1) hCcont
  have hAjoint : Continuous (fun p : ℝ × WholeL2 n ℂ => A p.1 p.2) :=
    U.continuous.comp (hSjoint.comp
      ((continuous_fst.sub continuous_const).prodMk continuous_snd))
  have hBjoint : Continuous (fun p : ℝ × WholeL2 n ℂ => B p.1 p.2) :=
    hCjoint.comp ((continuous_fst.sub continuous_const).prodMk continuous_snd)
  have hSD' (r : ℝ) (v : WholeL2 n ℂ) :
      HasDerivAt (fun a => U (W.S a v)) (W.C0 r v) r := by
    simpa only [U] using! hSD r v
  have hCD' (r : ℝ) (g : WholeH1 n ℂ) :
      HasDerivAt (fun a => U (W.C1 a g)) (W.D r g) r := by
    simpa only [U] using! hCD r g
  have hAD (t : ℝ) (v : WholeL2 n ℂ) :
      HasDerivAt (fun r => A r v) (B t v) t := by
    simpa only [A, B, U, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.comp_apply, Function.comp_apply, id_eq, mul_one] using!
      ((hSD' (t-s) v).comp_sub_const t s)
  have hBD (t : ℝ) :
      HasDerivAt (fun r => B r (Ψ t)) ((c ^ 2 : ℂ) • A t (q t)) t := by
    have hd := (hCD' (t-s) (G t)).comp_sub_const t s
    have he := waveD_eq_sine_laplacian c W hWcopy (G t) (q t) (hq t) (t-s)
    simpa only [A, B, U, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.comp_apply, Function.comp_apply, id_eq, mul_one,
      hCompat, hG, he] using! hd
  have hWD (t : ℝ) :
      HasDerivAt (fun r => A r (Ψ' r) - B r (Ψ r))
        (A t (Ψ'' t - (c ^ 2 : ℂ) • q t)) t := by
    have h1 := hasDerivAt_strong_apply A hAjoint (hΨ' t) (hAD t (Ψ' t))
    have h2 := hasDerivAt_strong_apply B hBjoint (hΨ t) (hBD t)
    convert h1.sub h2 using 1
    simp only [A, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.comp_apply, map_sub, map_smul]
    abel
  have hcR : Continuous (fun t => Ψ'' t - (c ^ 2 : ℂ) • q t) :=
    hΨ''.sub (hqc.const_smul (c ^ 2 : ℂ))
  have hPair : Continuous (fun t : ℝ => (t, Ψ'' t - (c ^ 2 : ℂ) • q t)) :=
    continuous_id.prodMk hcR
  have hcK := hAjoint.comp hPair
  have hInt : IntervalIntegrable
      (fun t => A t (Ψ'' t - (c ^ 2 : ℂ) • q t)) volume s T := by
    exact hcK.intervalIntegrable s T
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hWD t) hInt
  simpa only [A, B, U, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.comp_apply, sub_self, hT, hT', hS0, hC0,
    zero_apply, map_zero, ContinuousLinearMap.id_apply, sub_zero, zero_sub, neg_neg] using he

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set Filter Topology
open P201 P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201.Wave.Cauchy

theorem intervalIntegral_reverse_convolution {E F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ → E → F) (f : ℝ → E) (s T : ℝ) :
    (∫ t in s..T, A (t-s) (f t)) =
      ∫ r in 0..T-s, A (T-s-r) (f (T-r)) := by
  have he := intervalIntegral.integral_comp_sub_left
    (f := fun t => A (t-s) (f t)) (a := 0) (b := T-s) T
  calc
    _ = ∫ r in 0..T-s, A (T-r-s) (f (T-r)) := by
      simpa only [sub_sub_cancel, sub_zero] using he.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r _
      dsimp only
      rw [show T-r-s = T-s-r by ring]

/-- Differentiation of the retarded test integral in its lower time endpoint.
This uses the already proved Duhamel derivative after reversing time. -/
theorem reverseSineConvolution_hasDerivAt {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W) (R : ℝ → WholeL2 n 𝕜) (hR : Continuous R)
    (s T : ℝ) (hs : s < T) :
    HasDerivAt (fun r => ∫ t in r..T, hUnderlying ⊤ 1 (W.S (t-r) (R t)))
      (-(∫ t in s..T, W.C0 (t-s) (R t))) s := by
  let f : ℝ → WholeL2 n 𝕜 := fun r => R (T-r)
  have hf : LocallyIntegrableForcing f := fun t ht =>
    (hR.comp (continuous_const.sub continuous_id)).continuousOn.integrableOn_Icc
  have hd := sineConvolution_hasDerivWithinAt c κ W hW f hf (T-s) (sub_nonneg.mpr hs.le)
  have hd' := (hd.hasDerivAt (Ici_mem_nhds (sub_pos.mpr hs))).comp_const_sub T s
  have he (r : ℝ) (hr : r ≤ T) :
      (∫ t in r..T, hUnderlying ⊤ 1 (W.S (t-r) (R t))) =
        hUnderlying ⊤ 1 (∫ a in Icc 0 (T-r), W.S (T-r-a) (f a)) := by
    rw [intervalIntegral_reverse_convolution
      (fun a v => hUnderlying ⊤ 1 (W.S a v)) R r T]
    rw [intervalIntegral.integral_of_le (sub_nonneg.mpr hr), ← integral_Icc_eq_integral_Ioc]
    exact (hUnderlying ⊤ 1).integral_comp_comm
      ((duhamelIntegrable c κ W hW f hf (T-r) (sub_nonneg.mpr hr)).1)
  have hv : (∫ a in Icc 0 (T-s), W.C0 (T-s-a) (f a)) =
      ∫ t in s..T, W.C0 (t-s) (R t) := by
    rw [intervalIntegral_reverse_convolution (fun a v => W.C0 a v) R s T]
    rw [intervalIntegral.integral_of_le (sub_nonneg.mpr hs.le), integral_Icc_eq_integral_Ioc]
  rw [hv] at hd'
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hs] with r hr
  exact he r hr.le

/-- The cosine test identity follows by differentiating the sine identity in
the initial time. No temporal derivative of a spatial Laplacian is needed. -/
theorem waveCosine_green_initial {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W) (R Ψ : ℝ → WholeL2 n 𝕜)
    (hR : Continuous R) (T : ℝ) (hT : 0 < T)
    (hGreen : ∀ s : ℝ,
      (∫ t in s..T, hUnderlying ⊤ 1 (W.S (t-s) (R t))) = Ψ s)
    (hΨ : HasDerivAt Ψ 0 0) :
    (∫ t in 0..T, W.C0 t (R t)) = 0 := by
  have hd := reverseSineConvolution_hasDerivAt c κ W hW R hR 0 T hT
  have hd' : HasDerivAt Ψ (-(∫ t in 0..T, W.C0 t (R t))) 0 := by
    simpa only [sub_zero] using hd.congr_of_eventuallyEq
      (Eventually.of_forall fun s => (hGreen s).symm)
  exact neg_eq_zero.mp (hd'.unique hΨ)

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set TopologicalSpace Topology Filter
open scoped ENNReal ContDiff FourierTransform
open P201 P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201.Wave.Cauchy
open TestSlices

theorem spatialLaplacianSliceL2_eq {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    spatialLaplacianSliceL2 φ t = wholeSliceL2 (spaceLaplacianTest φ) t := by
  unfold spatialLaplacianSliceL2 wholeSliceL2
  congr 1
  rw [← testL2_spatialSlice, spatialSlice_spaceLaplacianTest]

/-- A single upper time beyond the supports of a spacetime test, its first
slice derivative, and its transposed wave residual. -/
theorem spacetimeTest_terminal_time {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (φ : SpacetimeTest n 𝕜) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t →
      wholeSliceL2 φ t = 0 ∧ wholeSliceL2 (timeDerivTest φ) t = 0 ∧
        wholeSliceL2 (spacetimeWaveTest c φ) t = 0 := by
  have hK := ((wholeSliceL2_hasCompactSupport φ).union
    (wholeSliceL2_hasCompactSupport (timeDerivTest φ))).union
      (wholeSliceL2_hasCompactSupport (spacetimeWaveTest c φ))
  obtain ⟨R,hR⟩ := hK.bddAbove
  let T := max R 0 + 1
  have hRT : R < T := by dsimp only [T]; linarith [le_max_left R 0]
  have hT : 0 < T := by dsimp only [T]; linarith [le_max_right R 0]
  refine ⟨T,hT,fun t ht => ⟨?_,?_,?_⟩⟩
  · apply image_eq_zero_of_notMem_tsupport
    intro hts
    have hr := hR (Or.inl (Or.inl hts))
    linarith
  · apply image_eq_zero_of_notMem_tsupport
    intro hts
    have hr := hR (Or.inl (Or.inr hts))
    linarith
  · apply image_eq_zero_of_notMem_tsupport
    intro hts
    have hr := hR (Or.inr hts)
    linarith

/-- The operator Green identity applies to every original spacetime test,
with the actual compact L²-valued transposed wave residual. -/
theorem spacetimeTest_sine_green {n : ℕ} (c : ℝ)
    (W : WaveOperators n ℂ) (hW : WaveFamilyLaws c (ContinuousLinearMap.id ℝ ℂ) W)
    (φ : SpacetimeTest n ℂ) :
    ∃ T : ℝ, 0 < T ∧
      (∀ t : ℝ, T ≤ t →
        wholeSliceL2 φ t = 0 ∧ wholeSliceL2 (timeDerivTest φ) t = 0 ∧
          wholeSliceL2 (spacetimeWaveTest c φ) t = 0) ∧
      ∀ s : ℝ, (∫ t in s..T,
        hUnderlying ⊤ 1 (W.S (t-s) (wholeSliceL2 (spacetimeWaveTest c φ) t))) =
          wholeSliceL2 φ s := by
  obtain ⟨T,hT,ht⟩ := spacetimeTest_terminal_time c φ
  have hres (t : ℝ) : wholeSliceL2 (timeDerivTest (timeDerivTest φ)) t -
      (c^2 : ℂ) • wholeSliceL2 (spaceLaplacianTest φ) t =
        wholeSliceL2 (spacetimeWaveTest c φ) t := by
    rw [wholeSliceL2_waveTest_eq]
    congr 1
    rw [show (c^2 : ℂ) = algebraMap ℝ ℂ (c^2) by simp]
    exact algebraMap_smul ℂ (c^2) _
  have hq (t : ℝ) := spatialLaplacianSliceL2_fourier φ t
  simp_rw [spatialLaplacianSliceL2_eq] at hq
  refine ⟨T,hT,ht,fun s => ?_⟩
  have he := waveSine_green c W hW
    (wholeSliceL2 φ) (wholeSliceL2 (timeDerivTest φ))
    (wholeSliceL2 (timeDerivTest (timeDerivTest φ)))
    (wholeSliceL2 (spaceLaplacianTest φ)) (spacetimeH1Slice φ)
    (spacetimeH1Slice_underlying φ) hq (wholeSliceL2_hasDerivAt φ)
    (wholeSliceL2_hasDerivAt (timeDerivTest φ))
    (wholeSliceL2_continuous (timeDerivTest (timeDerivTest φ)))
    (wholeSliceL2_continuous (spaceLaplacianTest φ)) s T
    (ht T le_rfl).1 (ht T le_rfl).2.1
  simpa only [hres] using he

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace P201.Wave.Cauchy.Uniqueness
open ExpandedFA.Evolution
open HilbertTripleSpec

/-- The scalar distributional second derivative determines the weak derivative
of the already prescribed continuous first derivative. -/
theorem scalar_second_to_first (T : ℝ) (hT : 0 ≤ T) (p r q : ℝ → ℝ)
    (hp : ContinuousOn p (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (hq : ContinuousOn q (Icc 0 T))
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt p (r t) (Ici 0) t)
    (hsecond : ∀ φ : ℝ → ℝ, testValue T φ →
      (∫ t, deriv (deriv φ) t * p t ∂timeMeasureValue T) =
        ∫ t, φ t * q t ∂timeMeasureValue T) :
    derivativeValue T r q := by
  let j : HilbertTriple ℝ ℝ :=
    ⟨ContinuousLinearMap.id ℝ ℝ, Function.injective_id, denseRange_id⟩
  have hd' := derivativeValue_of_continuous_derivative j T hT p r hp hr hd
  refine ⟨(hr.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo,
    (hq.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo, ?_⟩
  intro φ hφ
  have htest : testValue T (deriv φ) :=
    ⟨hφ.1.deriv', hφ.2.1.deriv, tsupport_deriv_subset.trans hφ.2.2⟩
  have h₁ := hd'.2.2 (deriv φ) htest
  have h₂ := hsecond φ hφ
  simp only [smul_eq_mul, j, ContinuousLinearMap.id_apply] at h₁ ⊢
  linarith

end P201.Wave.Cauchy.Uniqueness
end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace P201.Wave.Cauchy.Uniqueness
open P201Specs.Wave P201Specs.Wave.Cauchy
open ExpandedFA.Evolution HilbertTripleSpec
open P201.Wave.RealBridge

variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]

local instance realInnerProductH1' : InnerProductSpace ℝ (WholeH1 n 𝕜) :=
  inferInstanceAs (InnerProductSpace ℝ
    ((P201Specs.hilbertSubmodule 𝕜 ⊤ 1).restrictScalars ℝ))

lemma tensor_residual_re {T : ℝ} (c : ℝ) (η : TestSlices.TimeTest T)
    (ψ : P102.U4.WholeTests n 𝕜) (t : ℝ) (u : WholeH1 n 𝕜) :
    RCLike.re (∫ x : Space n, hUnderlying ⊤ 1 u x *
      testWaveOperator c (TestSlices.tensorTest η (conjugateTest ψ)) t x) =
      deriv (deriv η) t * inner ℝ (hUnderlying ⊤ 1 u) (hUnderlying ⊤ 1 (testH1 ψ)) +
        η t * waveForm n 𝕜 c u (testH1 ψ) := by
  have hI₁ : Integrable (fun x : Space n => hUnderlying ⊤ 1 u x * conjugateTest ψ x) := by
    simpa [domainMeasure, P201Specs.domainMeasure] using
      integrable_lp_test ⊤ (hUnderlying ⊤ 1 u) (conjugateTest ψ)
  have hI₂ : Integrable (fun x : Space n => hUnderlying ⊤ 1 u x *
      laplacian (conjugateTest ψ) x) := by
    simpa [domainMeasure, P201Specs.domainMeasure, TestSlices.laplacianTest_apply] using
      integrable_lp_test ⊤ (hUnderlying ⊤ 1 u) (TestSlices.laplacianTest (conjugateTest ψ))
  simp_rw [TestSlices.testWaveOperator_tensorTest, mul_sub, mul_smul_comm]
  have h₁ : Integrable (fun x : Space n => deriv (deriv η) t •
      (hUnderlying ⊤ 1 u x * conjugateTest ψ x)) := by
    simpa only [Pi.smul_apply] using! hI₁.smul (deriv (deriv η) t)
  have h₂ : Integrable (fun x : Space n => c ^ 2 • η t •
      (hUnderlying ⊤ 1 u x * P201Specs.laplacian (conjugateTest ψ) x)) :=
    (hI₂.smul (η t)).smul (c ^ 2)
  rw [integral_sub h₁ h₂, integral_smul,
    integral_smul, integral_smul]
  simp only [map_sub, RCLike.smul_re]
  rw [← testH1_inner_pairing]
  have he := waveForm_test_pairing c u ψ
  linear_combination -η t * he

/-- Arbitrary spacetime testing contains the scalar second-order time equation
on each compact smooth spatial test. -/
lemma homogeneous_test_second_identity (c : ℝ) (T : ℝ)
    (u : ℝ → WholeH1 n 𝕜) (hu : ContinuousOn u (Ici 0))
    (hres : ∀ φ : SpacetimeTest n 𝕜,
      (∫ t in Ioi (0 : ℝ), ∫ x : Space n,
        hUnderlying ⊤ 1 (u t) x * testWaveOperator c φ t x) = 0)
    (ψ : P102.U4.WholeTests n 𝕜) :
    ∀ η : ℝ → ℝ, testValue T η →
      (∫ t, deriv (deriv η) t *
        inner ℝ (hUnderlying ⊤ 1 (u t)) (hUnderlying ⊤ 1 (testH1 ψ))
          ∂timeMeasureValue T) =
      ∫ t, η t * -(waveForm n 𝕜 c (u t) (testH1 ψ)) ∂timeMeasureValue T := by
  intro η hη
  let ηtest : TestSlices.TimeTest T := ⟨η, hη.1, hη.2.1, hη.2.2⟩
  let φ := TestSlices.tensorTest ηtest (conjugateTest ψ)
  have hI := TestSlices.integrableOn_solution_test_pairing u hu c φ
  have hr := congrArg RCLike.re (hres φ)
  rw [← integral_re hI] at hr
  simp only [map_zero] at hr
  change (∫ t in Ioi (0 : ℝ), RCLike.re (∫ x : Space n,
      hUnderlying ⊤ 1 (u t) x * testWaveOperator c φ t x)) = 0 at hr
  simp_rw [φ, tensor_residual_re] at hr
  have hηzero (t : ℝ) (ht : t ∉ Ioo 0 T) : η t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => ht (hη.2.2 h))
  have hη2zero (t : ℝ) (ht : t ∉ Ioo 0 T) : deriv (deriv η) t = 0 :=
    deriv_of_notMem_tsupport (fun h => ht (hη.2.2 (tsupport_deriv_subset h)))
  have hrestrict : (∫ t in Ioi (0 : ℝ), deriv (deriv η) t *
      inner ℝ (hUnderlying ⊤ 1 (u t)) (hUnderlying ⊤ 1 (testH1 ψ)) +
      η t * waveForm n 𝕜 c (u t) (testH1 ψ)) =
      ∫ t in Ioo (0 : ℝ) T, deriv (deriv η) t *
      inner ℝ (hUnderlying ⊤ 1 (u t)) (hUnderlying ⊤ 1 (testH1 ψ)) +
      η t * waveForm n 𝕜 c (u t) (testH1 ψ) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun t ht => ht.1)
    intro t ht
    rw [hηzero t ht.2, hη2zero t ht.2]
    simp only [zero_mul, add_zero]
  change (∫ t in Ioi (0 : ℝ), deriv (deriv η) t *
      inner ℝ (hUnderlying ⊤ 1 (u t)) (hUnderlying ⊤ 1 (testH1 ψ)) +
      η t * waveForm n 𝕜 c (u t) (testH1 ψ)) = 0 at hr
  rw [hrestrict] at hr
  have huT := hu.mono (show Icc (0 : ℝ) T ⊆ Ici 0 from fun t ht => ht.1)
  have hp : ContinuousOn (fun t => inner ℝ (hUnderlying ⊤ 1 (u t))
      (hUnderlying ⊤ 1 (testH1 ψ))) (Icc 0 T) :=
    ((hUnderlying ⊤ 1).continuous.comp_continuousOn huT).inner continuousOn_const
  have hq : ContinuousOn (fun t => waveForm n 𝕜 c (u t) (testH1 ψ)) (Icc 0 T) :=
    ((waveForm n 𝕜 c).flip (testH1 ψ)).continuous.comp_continuousOn huT
  have hη2 : ContDiff ℝ 2 η := hη.1.of_le (by simp)
  have hdη : ContDiff ℝ 1 (deriv η) := hη2.deriv'
  have hddη : Continuous (deriv (deriv η)) := hdη.continuous_deriv (by norm_num)
  have hA : IntegrableOn (fun t => deriv (deriv η) t *
      inner ℝ (hUnderlying ⊤ 1 (u t)) (hUnderlying ⊤ 1 (testH1 ψ))) (Ioo 0 T) :=
    ((hddη.continuousOn.mul hp).integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  have hB : IntegrableOn (fun t => η t * waveForm n 𝕜 c (u t) (testH1 ψ)) (Ioo 0 T) :=
    ((hη.1.continuous.continuousOn.mul hq).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [integral_add hA hB] at hr
  simp_rw [mul_neg]
  rw [integral_neg]
  change (∫ t in Ioo 0 T, deriv (deriv η) t *
    inner ℝ (hUnderlying ⊤ 1 (u t)) (hUnderlying ⊤ 1 (testH1 ψ))) = _
  dsimp only [timeMeasureValue]
  linarith

lemma homogeneous_test_first_identity (c : ℝ) (T : ℝ) (hT : 0 ≤ T)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜)
    (hu : ContinuousOn u (Ici 0)) (hv : ContinuousOn v (Ici 0))
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt
      (fun s => hUnderlying ⊤ 1 (u s)) (v t) (Ici 0) t)
    (hres : ∀ φ : SpacetimeTest n 𝕜,
      (∫ t in Ioi (0 : ℝ), ∫ x : Space n,
        hUnderlying ⊤ 1 (u t) x * testWaveOperator c φ t x) = 0)
    (ψ : P102.U4.WholeTests n 𝕜) :
    derivativeValue T
      (fun t => inner ℝ (v t) (hUnderlying ⊤ 1 (testH1 ψ)))
      (fun t => -(waveForm n 𝕜 c (u t) (testH1 ψ))) := by
  have huT := hu.mono (show Icc (0 : ℝ) T ⊆ Ici 0 from fun t ht => ht.1)
  have hvT := hv.mono (show Icc (0 : ℝ) T ⊆ Ici 0 from fun t ht => ht.1)
  apply scalar_second_to_first T hT
    (fun t => inner ℝ (hUnderlying ⊤ 1 (u t)) (hUnderlying ⊤ 1 (testH1 ψ)))
    _ _
  · exact ((hUnderlying ⊤ 1).continuous.comp_continuousOn huT).inner continuousOn_const
  · exact hvT.inner continuousOn_const
  · exact (((waveForm n 𝕜 c).flip (testH1 ψ)).continuous.comp_continuousOn huT).neg
  · intro t ht
    simpa only [inner_zero_right, zero_add] using!
      (hd t ht).inner ℝ (hasDerivWithinAt_const t (Ici (0 : ℝ))
        (hUnderlying ⊤ 1 (testH1 ψ)))
  · exact homogeneous_test_second_identity c T u hu hres ψ

/-- Homogeneous distributional comparison uniqueness in the exact H¹/L²
class, deduced from arbitrary spacetime tests without a spectral certificate. -/
theorem homogeneous_spacetime_unique (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 ≤ T)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜)
    (hu : ContinuousOn u (Ici 0)) (hv : ContinuousOn v (Ici 0))
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt
      (fun s => hUnderlying ⊤ 1 (u s)) (v t) (Ici 0) t)
    (hu0 : u 0 = 0) (hv0 : v 0 = 0)
    (hres : ∀ φ : SpacetimeTest n 𝕜,
      (∫ t in Ioi (0 : ℝ), ∫ x : Space n,
        hUnderlying ⊤ 1 (u t) x * testWaveOperator c φ t x) = 0) :
    ∀ t ∈ Icc 0 T, u t = 0 ∧ v t = 0 := by
  exact homogeneous_unique_of_dense_tests testH1 testH1_denseRange
    (wholeSpaceHilbertTriple n 𝕜) T hT (fun _ => waveForm n 𝕜 c) (c ^ 2) (c ^ 2)
    (waveForm_hypotheses c hc T) u v (hu.mono (fun _ ht => ht.1))
    (hv.mono (fun _ ht => ht.1)) hd hu0 hv0
    (homogeneous_test_first_identity c T hT u v hu hv hd hres)

lemma wave_residual_sub_zero (c : ℝ) (u₁ u₂ : ℝ → WholeH1 n 𝕜)
    (hu₁ : ContinuousOn u₁ (Ici 0)) (hu₂ : ContinuousOn u₂ (Ici 0))
    (heq : ∀ φ : SpacetimeTest n 𝕜,
      (∫ t in Ioi (0 : ℝ), ∫ x : Space n,
        hUnderlying ⊤ 1 (u₁ t) x * testWaveOperator c φ t x) =
      ∫ t in Ioi (0 : ℝ), ∫ x : Space n,
        hUnderlying ⊤ 1 (u₂ t) x * testWaveOperator c φ t x) :
    ∀ φ : SpacetimeTest n 𝕜,
      (∫ t in Ioi (0 : ℝ), ∫ x : Space n,
        hUnderlying ⊤ 1 (u₁ t - u₂ t) x * testWaveOperator c φ t x) = 0 := by
  intro φ
  have hi (w : WholeH1 n 𝕜) (t : ℝ) : Integrable (fun x : Space n =>
      hUnderlying ⊤ 1 w x * testWaveOperator c φ t x) := by
    simpa [domainMeasure, P201Specs.domainMeasure, TestSlices.waveOperatorSlice_apply] using
      integrable_lp_test ⊤ (hUnderlying ⊤ 1 w) (TestSlices.waveOperatorSlice c φ t)
  have hpoint (t : ℝ) : (∫ x : Space n,
      hUnderlying ⊤ 1 (u₁ t - u₂ t) x * testWaveOperator c φ t x) =
      (∫ x : Space n, hUnderlying ⊤ 1 (u₁ t) x * testWaveOperator c φ t x) -
      ∫ x : Space n, hUnderlying ⊤ 1 (u₂ t) x * testWaveOperator c φ t x := by
    rw [map_sub]
    calc
      (∫ x : Space n, (hUnderlying ⊤ 1 (u₁ t) - hUnderlying ⊤ 1 (u₂ t)) x *
          testWaveOperator c φ t x) =
          ∫ x : Space n, (hUnderlying ⊤ 1 (u₁ t) x - hUnderlying ⊤ 1 (u₂ t) x) *
            testWaveOperator c φ t x := by
        apply integral_congr_ae
        have hs := MeasureTheory.Lp.coeFn_sub (hUnderlying ⊤ 1 (u₁ t))
          (hUnderlying ⊤ 1 (u₂ t))
        simp only [domainMeasure, P201Specs.domainMeasure,
          TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at hs
        exact hs.mono (fun x hx => by
          dsimp only
          rw [hx]
          rfl)
      _ = _ := by
        simp_rw [sub_mul]
        exact integral_sub (hi (u₁ t) t) (hi (u₂ t) t)
  simp_rw [hpoint]
  rw [integral_sub (TestSlices.integrableOn_solution_test_pairing u₁ hu₁ c φ)
    (TestSlices.integrableOn_solution_test_pairing u₂ hu₂ c φ), heq φ, sub_self]

/-- Comparison uniqueness for all distributional solutions in the original
continuous H¹ and continuously differentiable L² class. -/
theorem comparison_spacetime_unique (c : ℝ) (hc : 0 < c)
    (u₁ u₂ : ℝ → WholeH1 n 𝕜) (v₁ v₂ : ℝ → WholeL2 n 𝕜)
    (hu₁ : ContinuousOn u₁ (Ici 0)) (hv₁ : ContinuousOn v₁ (Ici 0))
    (hu₂ : ContinuousOn u₂ (Ici 0)) (hv₂ : ContinuousOn v₂ (Ici 0))
    (hd₁ : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt
      (fun s => hUnderlying ⊤ 1 (u₁ s)) (v₁ t) (Ici 0) t)
    (hd₂ : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt
      (fun s => hUnderlying ⊤ 1 (u₂ s)) (v₂ t) (Ici 0) t)
    (hu0 : u₁ 0 = u₂ 0) (hv0 : v₁ 0 = v₂ 0)
    (heq : ∀ φ : SpacetimeTest n 𝕜,
      (∫ t in Ioi (0 : ℝ), ∫ x : Space n,
        hUnderlying ⊤ 1 (u₁ t) x * testWaveOperator c φ t x) =
      ∫ t in Ioi (0 : ℝ), ∫ x : Space n,
        hUnderlying ⊤ 1 (u₂ t) x * testWaveOperator c φ t x) :
    ∀ t ∈ Ici (0 : ℝ), u₁ t = u₂ t ∧ v₁ t = v₂ t := by
  intro t ht
  have hdz : ∀ r ∈ Ici (0 : ℝ), HasDerivWithinAt
      (fun s => hUnderlying ⊤ 1 (u₁ s - u₂ s)) (v₁ r - v₂ r) (Ici 0) r := by
    intro r hr
    simpa only [map_sub] using! (hd₁ r hr).sub (hd₂ r hr)
  have hz := homogeneous_spacetime_unique c hc t ht
    (fun s => u₁ s - u₂ s) (fun s => v₁ s - v₂ s) (hu₁.sub hu₂) (hv₁.sub hv₂)
    hdz (sub_eq_zero.mpr hu0) (sub_eq_zero.mpr hv0)
    (wave_residual_sub_zero c u₁ u₂ hu₁ hu₂ heq) t ⟨ht, le_rfl⟩
  exact ⟨sub_eq_zero.mp hz.1, sub_eq_zero.mp hz.2⟩

theorem energy_solution_unique (c : ℝ) (hc : 0 < c)
    (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜)
    (u₁ u₂ : ℝ → WholeH1 n 𝕜) (v₁ v₂ : ℝ → WholeL2 n 𝕜)
    (h₁ : IsEnergySolution c g h f u₁ v₁)
    (h₂ : IsEnergySolution c g h f u₂ v₂) :
    ∀ t ∈ Ici (0 : ℝ), u₁ t = u₂ t ∧ v₁ t = v₂ t := by
  rcases h₁ with ⟨hu₁, hv₁, hd₁, hu₁0, hv₁0, hpde₁⟩
  rcases h₂ with ⟨hu₂, hv₂, hd₂, hu₂0, hv₂0, hpde₂⟩
  exact comparison_spacetime_unique c hc u₁ u₂ v₁ v₂ hu₁ hv₁ hu₂ hv₂ hd₁ hd₂
    (hu₁0.trans hu₂0.symm) (hv₁0.trans hv₂0.symm)
    (fun φ => (hpde₁ φ).trans (hpde₂ φ).symm)

end P201.Wave.Cauchy.Uniqueness
end

noncomputable section
open MeasureTheory Set
open P201 P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201.Wave.Cauchy
open TestSlices

theorem integral_Ioi_eq_Icc_of_zero_after {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (T : ℝ) (hF : ∀ t, T ≤ t → F t = 0) :
    (∫ t in Ioi (0 : ℝ), F t) = ∫ t in Icc 0 T, F t := by
  rw [integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun t ht => ht.1)
  intro t ht
  exact hF t (le_of_lt (lt_of_not_ge (fun htT => ht.2 ⟨ht.1,htT⟩)))

theorem scalarPair_spacetimeSlice {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : WholeL2 n 𝕜) (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    scalarPair f (wholeSliceL2 φ t) = ∫ x : Space n, f x * φ (t,x) := by
  rw [scalarPair_eq_integral]
  apply integral_congr_ae
  filter_upwards [wholeSliceL2_ae φ t] with x hx
  rw [hx]

theorem scalarPair_waveSlice {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (f : WholeL2 n 𝕜) (φ : SpacetimeTest n 𝕜) (t : ℝ) :
    scalarPair f (wholeSliceL2 (spacetimeWaveTest c φ) t) =
      ∫ x : Space n, f x * testWaveOperator c φ t x := by
  simpa only [spacetimeWaveTest_apply] using
    scalarPair_spacetimeSlice f (spacetimeWaveTest c φ) t

/-- Finite-interval scalar-linear pairing identities imply the exact original
spacetime distributional PDE. The terminal time is chosen separately per test. -/
theorem distributionalWave_of_finite_pairings {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (f : ℝ → WholeL2 n 𝕜) (u : ℝ → WholeH1 n 𝕜)
    (hfinite : ∀ φ : SpacetimeTest n 𝕜, ∃ T : ℝ,
      (∀ t, T ≤ t → wholeSliceL2 φ t = 0 ∧
        wholeSliceL2 (spacetimeWaveTest c φ) t = 0) ∧
      (∫ t in Icc 0 T, scalarPair (hUnderlying ⊤ 1 (u t))
        (wholeSliceL2 (spacetimeWaveTest c φ) t)) =
        ∫ t in Icc 0 T, scalarPair (f t) (wholeSliceL2 φ t)) :
    IsDistributionalWave c f u := by
  intro φ
  obtain ⟨T,ht,hpair⟩ := hfinite φ
  simp_rw [← scalarPair_waveSlice, ← scalarPair_spacetimeSlice]
  rw [integral_Ioi_eq_Icc_of_zero_after
    (fun t => scalarPair (hUnderlying ⊤ 1 (u t)) (wholeSliceL2 (spacetimeWaveTest c φ) t)) T
    (fun t htT => by rw [(ht t htT).2]; simp [scalarPair]),
    integral_Ioi_eq_Icc_of_zero_after
      (fun t => scalarPair (f t) (wholeSliceL2 φ t)) T
      (fun t htT => by rw [(ht t htT).1]; simp [scalarPair])]
  exact hpair

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set TopologicalSpace Topology Filter
open scoped ENNReal ContDiff
open P201 P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201.Wave.Cauchy
open RealBridge TestSlices

theorem locallyIntegrableForcing_ofReal {n : ℕ}
    (f : ℝ → WholeL2 n ℝ) (hf : LocallyIntegrableForcing f) :
    LocallyIntegrableForcing (fun t => ofRealLp ⊤ (f t)) := by
  intro T hT
  exact (ofRealLp ⊤).integrable_comp (hf T hT)

theorem displacement_real_projection {n : ℕ} (c : ℝ)
    (W : WaveOperators n ℂ) (hW : WaveFamilyLaws c (ContinuousLinearMap.id ℝ ℂ) W)
    (g : WholeH1 n ℝ) (h : WholeL2 n ℝ) (f : ℝ → WholeL2 n ℝ)
    (hf : LocallyIntegrableForcing f) (t : ℝ) (ht : 0 ≤ t) :
    reH1 ⊤ (displacement W (ofRealH1 ⊤ g) (ofRealLp ⊤ h)
      (fun s => ofRealLp ⊤ (f s)) t) = displacement (realWaveOperators W) g h f t := by
  have hi := (duhamelIntegrable c (ContinuousLinearMap.id ℝ ℂ) W hW
    (fun s => ofRealLp ⊤ (f s)) (locallyIntegrableForcing_ofReal f hf) t ht).1
  unfold displacement
  rw [map_add, map_add, ← (reH1 ⊤).integral_comp_comm hi]
  rfl

theorem spacetime_lineDeriv_postcomp {n : ℕ} {𝕜 𝕜' : Type} [RCLike 𝕜] [RCLike 𝕜']
    (L : 𝕜 →L[ℝ] 𝕜') (φ : SpacetimeTest n 𝕜) (v : ℝ × Space n) :
    (TestFunction.lineDerivCLM ℝ v (TestFunction.postcompCLM L φ) : SpacetimeTest n 𝕜') =
      TestFunction.postcompCLM L (TestFunction.lineDerivCLM ℝ v φ : SpacetimeTest n 𝕜) := by
  ext p
  rw [TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ (by simp)]
  change fderiv ℝ (L ∘ φ) p v = L ((TestFunction.lineDerivCLM ℝ v φ : SpacetimeTest n 𝕜) p)
  rw [TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ (by simp),
    (L.hasFDerivAt.comp p (φ.contDiff.differentiable (by simp) p).hasFDerivAt).fderiv]
  rfl

theorem timeDerivTest_postcomp {n : ℕ} {𝕜 𝕜' : Type} [RCLike 𝕜] [RCLike 𝕜']
    (L : 𝕜 →L[ℝ] 𝕜') (φ : SpacetimeTest n 𝕜) :
    timeDerivTest (TestFunction.postcompCLM L φ) = TestFunction.postcompCLM L (timeDerivTest φ) :=
  spacetime_lineDeriv_postcomp L φ (1,0)

theorem spaceWordTest_postcomp {n : ℕ} {𝕜 𝕜' : Type} [RCLike 𝕜] [RCLike 𝕜']
    (L : 𝕜 →L[ℝ] 𝕜') (φ : SpacetimeTest n 𝕜) (l : List (Fin n)) :
    spaceWordTest (TestFunction.postcompCLM L φ) l = TestFunction.postcompCLM L (spaceWordTest φ l) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [spaceWordTest, ih, spaceDerivTest, spacetime_lineDeriv_postcomp]

theorem spaceLaplacianTest_postcomp {n : ℕ} {𝕜 𝕜' : Type} [RCLike 𝕜] [RCLike 𝕜']
    (L : 𝕜 →L[ℝ] 𝕜') (φ : SpacetimeTest n 𝕜) :
    spaceLaplacianTest (TestFunction.postcompCLM L φ) =
      TestFunction.postcompCLM L (spaceLaplacianTest φ) := by
  unfold spaceLaplacianTest
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact spaceWordTest_postcomp L φ _

theorem spacetimeWaveTest_postcomp {n : ℕ} {𝕜 𝕜' : Type} [RCLike 𝕜] [RCLike 𝕜']
    (L : 𝕜 →L[ℝ] 𝕜') (c : ℝ) (φ : SpacetimeTest n 𝕜) :
    spacetimeWaveTest c (TestFunction.postcompCLM L φ) =
      TestFunction.postcompCLM L (spacetimeWaveTest c φ) := by
  simp only [spacetimeWaveTest, timeDerivTest_postcomp, spaceLaplacianTest_postcomp,
    map_sub, map_smul]

theorem testWaveOperator_ofReal {n : ℕ} (c : ℝ) (φ : SpacetimeTest n ℝ) (t : ℝ) (x : Space n) :
    testWaveOperator c (TestFunction.postcompCLM Complex.ofRealCLM φ) t x =
      ((testWaveOperator (𝕜 := ℝ) c φ t x : ℝ) : ℂ) := by
  rw [← spacetimeWaveTest_apply, spacetimeWaveTest_postcomp]
  change ((spacetimeWaveTest (𝕜 := ℝ) c φ (t,x) : ℝ) : ℂ) = _
  rw [spacetimeWaveTest_apply]

theorem reLp_integral_real_test {n : ℕ} (f : WholeL2 n ℂ)
    (ψ : P102.U4.TestSpace ℝ (⊤ : Domain n)) :
    (∫ x : Space n, reLp ⊤ f x * ψ x) =
      (∫ x : Space n, f x * (ψ x : ℂ)).re := by
  have h := reLp_pairing (⊤ : Domain n) f ψ
  rw [P102.U4.lpTestPairing_eq_integral, P102.U4.lpTestPairing_eq_integral] at h
  change (∫ x : Space n, reLp ⊤ f x * ψ x ∂domainMeasure ⊤) =
    (∫ x : Space n, f x * P102.U4.complexifyTest ⊤ ψ x ∂domainMeasure ⊤).re at h
  simpa only [domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
    Measure.restrict_univ, P102.U4.complexifyTest_apply] using h

/-- Taking the real part preserves the original arbitrary-spacetime weak
wave equation; the local integrability and time continuity justify all integrals. -/
theorem isDistributionalWave_real_projection {n : ℕ} (c : ℝ)
    (f : ℝ → WholeL2 n ℂ) (hf : LocallyIntegrableForcing f)
    (u : ℝ → WholeH1 n ℂ) (hu : ContinuousOn u (Ici (0 : ℝ)))
    (hPDE : IsDistributionalWave c f u) :
    IsDistributionalWave c (fun t => reLp ⊤ (f t)) (fun t => reH1 ⊤ (u t)) := by
  intro φ
  let φC : SpacetimeTest n ℂ := TestFunction.postcompCLM Complex.ofRealCLM φ
  have hL (t : ℝ) :
      (∫ x : Space n, hUnderlying ⊤ 1 (u t) x * testWaveOperator c φC t x).re =
        ∫ x : Space n, hUnderlying ⊤ 1 (reH1 ⊤ (u t)) x * testWaveOperator c φ t x := by
    rw [reH1_underlying]
    have h := reLp_integral_real_test (hUnderlying ⊤ 1 (u t)) (waveOperatorSlice c φ t)
    simpa only [waveOperatorSlice_apply, φC, testWaveOperator_ofReal] using h.symm
  have hR (t : ℝ) : (∫ x : Space n, f t x * φC (t,x)).re =
      ∫ x : Space n, reLp ⊤ (f t) x * φ (t,x) := by
    have h := reLp_integral_real_test (f t) (spatialSlice φ t)
    exact h.symm
  have hiL := integrableOn_solution_test_pairing u hu c φC
  have hiR := integrableOn_forcing_test_pairing f hf φC
  have h := congrArg Complex.re (hPDE φC)
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        (∫ x : Space n, hUnderlying ⊤ 1 (u t) x * testWaveOperator c φC t x).re := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => (hL t).symm)
    _ = (∫ t in Ioi (0 : ℝ),
        ∫ x : Space n, hUnderlying ⊤ 1 (u t) x * testWaveOperator c φC t x).re :=
      integral_re hiL
    _ = (∫ t in Ioi (0 : ℝ), ∫ x : Space n, f t x * φC (t,x)).re := h
    _ = ∫ t in Ioi (0 : ℝ), (∫ x : Space n, f t x * φC (t,x)).re :=
      (integral_re hiR).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall hR

theorem isDistributionalWave_real_data_projection {n : ℕ} (c : ℝ)
    (f : ℝ → WholeL2 n ℝ) (hf : LocallyIntegrableForcing f)
    (u : ℝ → WholeH1 n ℂ) (hu : ContinuousOn u (Ici (0 : ℝ)))
    (hPDE : IsDistributionalWave c (fun t => ofRealLp ⊤ (f t)) u) :
    IsDistributionalWave c f (fun t => reH1 ⊤ (u t)) := by
  simpa only [reLp_ofRealLp] using
    isDistributionalWave_real_projection c (fun t => ofRealLp ⊤ (f t))
      (locallyIntegrableForcing_ofReal f hf) u hu hPDE

theorem isDistributionalWave_congrOn_positive {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} {f : ℝ → WholeL2 n 𝕜} {u v : ℝ → WholeH1 n 𝕜}
    (hPDE : IsDistributionalWave c f u) (hEq : ∀ t : ℝ, 0 < t → u t = v t) :
    IsDistributionalWave c f v := by
  intro φ
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∫ x : Space n,
        hUnderlying ⊤ 1 (u t) x * testWaveOperator c φ t x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [hEq t ht]
    _ = _ := hPDE φ

theorem isDistributionalWave_real_displacement {n : ℕ} (c : ℝ)
    (W : WaveOperators n ℂ) (hW : WaveFamilyLaws c (ContinuousLinearMap.id ℝ ℂ) W)
    (g : WholeH1 n ℝ) (h : WholeL2 n ℝ) (f : ℝ → WholeL2 n ℝ)
    (hf : LocallyIntegrableForcing f)
    (hPDE : IsDistributionalWave c (fun t => ofRealLp ⊤ (f t))
      (displacement W (ofRealH1 ⊤ g) (ofRealLp ⊤ h) (fun t => ofRealLp ⊤ (f t)))) :
    IsDistributionalWave c f (displacement (realWaveOperators W) g h f) := by
  have hu := (duhamelRegularity c (ContinuousLinearMap.id ℝ ℂ) W hW
    (ofRealH1 ⊤ g) (ofRealLp ⊤ h) (fun t => ofRealLp ⊤ (f t))
    (locallyIntegrableForcing_ofReal f hf)).1
  apply isDistributionalWave_congrOn_positive
    (isDistributionalWave_real_data_projection c f hf _ hu hPDE)
  intro t ht
  exact displacement_real_projection c W hW g h f hf t ht.le

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set
open P201 P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201.Wave.Cauchy

/-- Assemble the original solution class after verifying the distributional
equation of the explicit Bochner formula. Comparison uses the proved theorem
for all distributional energy solutions. -/
theorem cauchyForField_of_distributional {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (hc : 0 < c) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W)
    (hPDE : ∀ (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜),
      LocallyIntegrableForcing f → IsDistributionalWave c f (displacement W g h f)) :
    cauchyForField n 𝕜 c κ := by
  refine ⟨W, hW, ?_⟩
  intro g h f hf
  rcases duhamelRegularity c κ W hW g h f hf with ⟨hu,hv,hd,hu0,hv0⟩
  have hSol : IsEnergySolution c g h f (displacement W g h f) (velocity W g h f) :=
    ⟨hu,hv,hd,hu0,hv0,hPDE g h f hf⟩
  refine ⟨fun t ht => duhamelIntegrable c κ W hW f hf t ht, hSol, ?_⟩
  intro u v huv
  exact Uniqueness.energy_solution_unique c hc g h f u (displacement W g h f)
    v (velocity W g h f) huv hSol

/-- The exact real restriction of the canonical complex Fourier family obeys
the accepted multiplier laws, without choosing any new solution certificate. -/
theorem canonicalRealWaveFamilyLaws (n : ℕ) (c : ℝ) (hc : 0 < c) :
    WaveFamilyLaws c Complex.ofRealCLM
      (P201.Wave.realWaveOperators (P201.Wave.complexWaveOperators n c hc)) := by
  apply P201.Wave.realWaveFamilyLaws c _ (P201.Wave.complexWaveFamilyLaws n c hc)
  · exact P201.Wave.RealBridge.embeddedFourier_real
  · exact fun t f => P201.Wave.RealBridge.wholeCosine_reality c t f
  · exact fun t f => P201.Wave.RealBridge.sineH1_underlying_reality c hc t f
  · exact fun t g => P201.Wave.RealBridge.cosineH1Derivative_reality c hc.le t g

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set
namespace P201.Wave.Cauchy

/-- A causal kernel on the fixed rectangle reduces to the backward triangle.
Only its value at zero is used; all integrals are actual set integrals. -/
theorem backward_causal_integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → ℝ → E) (hF0 : ∀ t, F 0 t = 0)
    (s T : ℝ) (hs : 0 ≤ s) :
    (∫ t in Icc 0 T, F (max (t-s) 0) t) = ∫ t in Icc s T, F (t-s) t := by
  calc
    (∫ t in Icc 0 T, F (max (t-s) 0) t) =
        ∫ t in Icc 0 T, (Icc s T).indicator (fun t => F (t-s) t) t := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only
      by_cases hst : s ≤ t
      · rw [max_eq_left (sub_nonneg.mpr hst), indicator_of_mem (show t ∈ Icc s T from ⟨hst,ht.2⟩)]
      · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hst)), hF0,
          indicator_of_notMem (by simp [hst])]
    _ = ∫ t in Icc s T, F (t-s) t := by
      rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
      rw [inter_eq_left.mpr (Icc_subset_Icc_left hs)]

end P201.Wave.Cauchy
end

set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
open P201 P201Specs.Wave
open P201.Wave.Cauchy.TestSlices
namespace P201.Wave.Cauchy

/-- Transpose the genuine causal sine propagator against an L¹ family of L²
tests. The forcing needs exactly Bochner L¹, and the two-variable integrand is
proved integrable before invoking Fubini. -/
theorem waveS_causal_integral_transpose {n : ℕ} (c : ℝ)
    (W : WaveOperators n ℂ) (hW : WaveFamilyLaws c (ContinuousLinearMap.id ℝ ℂ) W)
    (hTranspose : ∀ r (v z : WholeL2 n ℂ),
      scalarPair (hUnderlying ⊤ 1 (W.S r v)) z =
        scalarPair v (hUnderlying ⊤ 1 (W.S r z)))
    (T : ℝ) (hT : 0 ≤ T) (f R : ℝ → WholeL2 n ℂ)
    (hf : IntegrableOn f (Icc 0 T)) (hR : IntegrableOn R (Icc 0 T)) :
    (∫ t in Icc 0 T, scalarPair
      (hUnderlying ⊤ 1 (∫ s in Icc 0 T,
        W.S (max (t-s) 0) (f s))) (R t)) =
    ∫ s in Icc 0 T, scalarPair (f s)
      (∫ t in Icc 0 T, hUnderlying ⊤ 1
        (W.S (max (t-s) 0) (R t))) := by
  let U := hUnderlying (𝕜 := ℂ) (⊤ : Domain n) 1
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let a : ℝ × ℝ → ℝ := fun p => max (p.1-p.2) 0
  let M := Real.sqrt (T ^ 2 + c⁻¹ ^ 2)
  rcases hW with ⟨_, _, _, _, hBound, _, _, hScont, _⟩
  have hSjoint := continuous_family_apply W.S
    (fun r => Real.sqrt (r ^ 2 + c⁻¹ ^ 2)) (by fun_prop)
    (fun r => (hBound r).2.2.1) hScont
  have ha : Continuous a := (continuous_fst.sub continuous_snd).max continuous_const
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hAbound (t s : ℝ) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
      ‖W.S (a (t,s))‖ ≤ M := by
    apply (hBound _).2.2.1.trans
    apply Real.sqrt_le_sqrt
    have hm0 : 0 ≤ a (t,s) := le_max_right _ _
    have hmT : a (t,s) ≤ T := max_le (by linarith [ht.2,hs.1]) hT
    nlinarith
  have hAf (t : ℝ) (ht : t ∈ Icc 0 T) :
      Integrable (fun s => W.S (a (t,s)) (f s)) μ := by
    apply (hf.norm.const_mul M).mono'
      (hSjoint.comp_aestronglyMeasurable
        (((ha.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).prodMk hf.aestronglyMeasurable))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact ((W.S _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hAbound t s ht hs) (norm_nonneg _))
  have hAR (s : ℝ) (hs : s ∈ Icc 0 T) :
      Integrable (fun t => U (W.S (a (t,s)) (R t))) μ := by
    apply U.integrable_comp
    apply (hR.norm.const_mul M).mono'
      (hSjoint.comp_aestronglyMeasurable
        (((ha.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable).prodMk hR.aestronglyMeasurable))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ((W.S _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hAbound t s ht hs) (norm_nonneg _))
  have hMeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => scalarPair (U (W.S (a p) (f p.2))) (R p.1)) (μ.prod μ) := by
    have hmInput : AEStronglyMeasurable (fun p : ℝ × ℝ => (a p, f p.2)) (μ.prod μ) :=
      ha.aestronglyMeasurable.prodMk hf.aestronglyMeasurable.comp_snd
    have hmS := hSjoint.comp_aestronglyMeasurable hmInput
    have hmU := U.continuous.comp_aestronglyMeasurable hmS
    have hmPair := hmU.prodMk hR.aestronglyMeasurable.comp_fst
    exact continuous_scalarPair.comp_aestronglyMeasurable hmPair
  let K : ℝ := ‖(conjugateL2Map : WholeL2 n ℂ →L[ℝ] WholeL2 n ℂ)‖
  have hInt : Integrable
      (fun p : ℝ × ℝ => scalarPair (U (W.S (a p) (f p.2))) (R p.1)) (μ.prod μ) := by
    apply ((hR.norm.mul_prod hf.norm).const_mul (K * ‖U‖ * M)).mono' hMeas
    have hm : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, p.1 ∈ Icc 0 T ∧ p.2 ∈ Icc 0 T := by
      change ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, p ∈ ((Icc 0 T) ×ˢ (Icc 0 T))
      rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Icc.prod measurableSet_Icc)]
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact ⟨ht,hs⟩
    filter_upwards [hm] with p hp
    have hSBound : ‖W.S (a p) (f p.2)‖ ≤ M * ‖f p.2‖ :=
      ((W.S (a p)).le_opNorm (f p.2)).trans
        (mul_le_mul_of_nonneg_right (hAbound p.1 p.2 hp.1 hp.2) (norm_nonneg (f p.2)))
    have hUBound : ‖U (W.S (a p) (f p.2))‖ ≤ ‖U‖ * (M * ‖f p.2‖) :=
      (U.le_opNorm (W.S (a p) (f p.2))).trans
        (mul_le_mul_of_nonneg_left hSBound (ContinuousLinearMap.opNorm_nonneg U))
    have hK : 0 ≤ K := ContinuousLinearMap.opNorm_nonneg (conjugateL2Map : WholeL2 n ℂ →L[ℝ] WholeL2 n ℂ)
    calc
      ‖scalarPair (U (W.S (a p) (f p.2))) (R p.1)‖ ≤
          K * ‖U (W.S (a p) (f p.2))‖ * ‖R p.1‖ := scalarPair_norm_le _ _
      _ ≤ K * (‖U‖ * (M * ‖f p.2‖)) * ‖R p.1‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUBound hK) (norm_nonneg _)
      _ = (K * ‖U‖ * M) * (‖R p.1‖ * ‖f p.2‖) := by ring
  have hTranspose' (r : ℝ) (v z : WholeL2 n ℂ) :
      scalarPair (U (W.S r v)) z = scalarPair v (U (W.S r z)) := hTranspose r v z
  calc
    _ = ∫ t, ∫ s, scalarPair (U (W.S (a (t,s)) (f s))) (R t) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [← U.integral_comp_comm (hAf t ht)]
      have hiU := U.integrable_comp (hAf t ht)
      have he := ((scalarPairCLM (𝕜 := ℂ)).flip (R t)).integral_comp_comm hiU
      simpa only [ContinuousLinearMap.flip_apply, scalarPairCLM_apply] using he.symm
    _ = ∫ s, ∫ t, scalarPair (U (W.S (a (t,s)) (f s))) (R t) ∂μ ∂μ :=
      integral_integral_swap hInt
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      simp_rw [hTranspose']
      have he := (scalarPairCLM (f s)).integral_comp_comm (hAR s hs)
      simpa only [scalarPairCLM_apply] using he


/-- Specialization of the genuine operator transpose to the constructed
complex Fourier family; the pairing symmetry is proved by Plancherel. -/
theorem complexS_causal_integral_transpose {n : ℕ} (c : ℝ) (hc : 0 < c)
    (T : ℝ) (hT : 0 ≤ T) (f R : ℝ → WholeL2 n ℂ)
    (hf : IntegrableOn f (Icc 0 T)) (hR : IntegrableOn R (Icc 0 T)) :
    (∫ t in Icc 0 T, scalarPair
      (hUnderlying ⊤ 1 (∫ s in Icc 0 T,
        (P201.Wave.complexWaveOperators n c hc).S (max (t-s) 0) (f s))) (R t)) =
    ∫ s in Icc 0 T, scalarPair (f s)
      (∫ t in Icc 0 T, hUnderlying ⊤ 1
        ((P201.Wave.complexWaveOperators n c hc).S (max (t-s) 0) (R t))) := by
  apply waveS_causal_integral_transpose c (P201.Wave.complexWaveOperators n c hc)
    (P201.Wave.complexWaveFamilyLaws n c hc) ?_ T hT f R hf hR
  intro r v z
  simpa only [scalarPair_eq_integral] using complexS_bilinear c hc r v z

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
open P201 P201Specs.Wave P201Specs.Wave.Cauchy
open P201.Wave.Cauchy.TestSlices
namespace P201.Wave.Cauchy

/-- Finite-interval distributional identity for the actual H¹-valued Duhamel
source, against the full residual of an arbitrary spacetime test. -/
theorem complexDuhamel_finite_pairing {n : ℕ} (c : ℝ) (hc : 0 < c)
    (φ : SpacetimeTest n ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hGreen : ∀ s : ℝ, (∫ t in s..T, hUnderlying ⊤ 1
      ((P201.Wave.complexWaveOperators n c hc).S (t-s)
        (wholeSliceL2 (spacetimeWaveTest c φ) t))) = wholeSliceL2 φ s)
    (f : ℝ → WholeL2 n ℂ) (hf : IntegrableOn f (Icc 0 T)) :
    (∫ t in Icc 0 T, scalarPair
      (hUnderlying ⊤ 1 (∫ s in Icc 0 t,
        (P201.Wave.complexWaveOperators n c hc).S (t-s) (f s)))
      (wholeSliceL2 (spacetimeWaveTest c φ) t)) =
      ∫ t in Icc 0 T, scalarPair (f t) (wholeSliceL2 φ t) := by
  let W := P201.Wave.complexWaveOperators n c hc
  let U := hUnderlying (𝕜 := ℂ) (⊤ : Domain n) 1
  let R := wholeSliceL2 (spacetimeWaveTest c φ)
  have hS0 : W.S 0 = 0 := P201.Wave.sineH1_zero n c hc
  have hR : IntegrableOn R (Icc 0 T) :=
    (wholeSliceL2_continuous (spacetimeWaveTest c φ)).continuousOn.integrableOn_Icc
  have hBack (s : ℝ) (hs : s ∈ Icc 0 T) :
      (∫ t in Icc 0 T, U (W.S (max (t-s) 0) (R t))) = wholeSliceL2 φ s := by
    rw [backward_causal_integral_eq (fun r t => U (W.S r (R t)))
      (fun t => by rw [hS0]; simp) s T hs.1]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.2]
    exact hGreen s
  calc
    _ = ∫ t in Icc 0 T, scalarPair
        (U (∫ s in Icc 0 T, W.S (max (t-s) 0) (f s))) (R t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have he := sineConvolutionOn_eq W hS0 T f t ht
      change (∫ s in Icc 0 T, W.S (max (t-s) 0) (f s)) =
        ∫ s in Icc 0 t, W.S (t-s) (f s) at he
      rw [he]
    _ = ∫ s in Icc 0 T, scalarPair (f s)
        (∫ t in Icc 0 T, U (W.S (max (t-s) 0) (R t))) :=
      complexS_causal_integral_transpose c hc T hT f R hf hR
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [hBack s hs]

end P201.Wave.Cauchy
end

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Topology
open P201 P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201.Wave.Cauchy

/-- Transpose the genuine homogeneous propagator against an L²-valued test
curve. Both transpose integrals are genuine Bochner integrals. -/
theorem homogeneous_pairing_zero_of_transpose {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W)
    (hCbil : ∀ t f q, TestSlices.scalarPair (W.C0 t f) q =
      TestSlices.scalarPair f (W.C0 t q))
    (hSbil : ∀ t f q, TestSlices.scalarPair (hUnderlying ⊤ 1 (W.S t f)) q =
      TestSlices.scalarPair f (hUnderlying ⊤ 1 (W.S t q)))
    (T : ℝ) (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
    (R : ℝ → WholeL2 n 𝕜) (hR : Continuous R)
    (hcos : (∫ t in Icc 0 T, W.C0 t (R t)) = 0)
    (hsine : (∫ t in Icc 0 T,
      hUnderlying ⊤ 1 (W.S t (R t))) = 0) :
    (∫ t in Icc 0 T, TestSlices.scalarPair
      (hUnderlying ⊤ 1 (W.C1 t g +
        W.S t h)) (R t)) = 0 := by
  rcases hW with
    ⟨_,hcompat,_,_,hbound,hC0,_,hS,_,_,_,_,_,_,_⟩
  have hRC : Continuous (fun t => W.C0 t (R t)) :=
    (continuous_family_apply W.C0 (fun _ => 1) continuous_const
      (fun t => (hbound t).1) hC0).comp (continuous_id.prodMk hR)
  have hRS : Continuous (fun t => hUnderlying ⊤ 1 (W.S t (R t))) :=
    (hUnderlying ⊤ 1).continuous.comp
      ((continuous_family_apply W.S (fun t => Real.sqrt (t ^ 2 + c⁻¹ ^ 2))
        (by fun_prop) (fun t => (hbound t).2.2.1) hS).comp (continuous_id.prodMk hR))
  have hiRC : IntegrableOn (fun t => W.C0 t (R t)) (Icc 0 T) :=
    hRC.continuousOn.integrableOn_Icc
  have hiRS : IntegrableOn (fun t => hUnderlying ⊤ 1 (W.S t (R t))) (Icc 0 T) :=
    hRS.continuousOn.integrableOn_Icc
  have hpC : IntegrableOn (fun t => TestSlices.scalarPairCLM (hUnderlying ⊤ 1 g)
      (W.C0 t (R t))) (Icc 0 T) :=
    (TestSlices.scalarPairCLM (hUnderlying ⊤ 1 g)).integrable_comp hiRC
  have hpS : IntegrableOn (fun t => TestSlices.scalarPairCLM h
      (hUnderlying ⊤ 1 (W.S t (R t)))) (Icc 0 T) :=
    (TestSlices.scalarPairCLM h).integrable_comp hiRS
  have he (t : ℝ) : TestSlices.scalarPair
      (hUnderlying ⊤ 1 (W.C1 t g + W.S t h)) (R t) =
      TestSlices.scalarPairCLM (hUnderlying ⊤ 1 g) (W.C0 t (R t)) +
      TestSlices.scalarPairCLM h (hUnderlying ⊤ 1 (W.S t (R t))) := by
    rw [← TestSlices.scalarPairCLM_apply]
    simp only [map_add, ContinuousLinearMap.add_apply]
    rw [TestSlices.scalarPairCLM_apply, TestSlices.scalarPairCLM_apply,
      TestSlices.scalarPairCLM_apply, TestSlices.scalarPairCLM_apply]
    rw [hcompat t g, hCbil, hSbil]
  change (∫ t in Icc 0 T, TestSlices.scalarPair
    (hUnderlying ⊤ 1 (W.C1 t g + W.S t h)) (R t)) = 0
  simp_rw [he]
  rw [integral_add hpC hpS,
    (TestSlices.scalarPairCLM (hUnderlying ⊤ 1 g)).integral_comp_comm hiRC,
    (TestSlices.scalarPairCLM h).integral_comp_comm hiRS,
    hcos, hsine, map_zero, map_zero, add_zero]

theorem complex_homogeneous_pairing_zero {n : ℕ} (c : ℝ) (hc : 0 < c)
    (T : ℝ) (g : WholeH1 n ℂ) (h : WholeL2 n ℂ)
    (R : ℝ → WholeL2 n ℂ) (hR : Continuous R)
    (hcos : (∫ t in Icc 0 T, (complexWaveOperators n c hc).C0 t (R t)) = 0)
    (hsine : (∫ t in Icc 0 T,
      hUnderlying ⊤ 1 ((complexWaveOperators n c hc).S t (R t))) = 0) :
    (∫ t in Icc 0 T, TestSlices.scalarPair
      (hUnderlying ⊤ 1 ((complexWaveOperators n c hc).C1 t g +
        (complexWaveOperators n c hc).S t h)) (R t)) = 0 := by
  apply homogeneous_pairing_zero_of_transpose c (ContinuousLinearMap.id ℝ ℂ)
    (complexWaveOperators n c hc) (complexWaveFamilyLaws n c hc) ?_ ?_
    T g h R hR hcos hsine
  · intro t f q
    simp only [TestSlices.scalarPair_eq_integral]
    exact complexC0_bilinear c hc t f q
  · intro t f q
    simp only [TestSlices.scalarPair_eq_integral]
    exact complexS_bilinear c hc t f q

/-- The initial cosine and sine Green integrals annihilate every homogeneous
solution against an arbitrary original spacetime test. -/
theorem complex_homogeneous_test_pairing_zero {n : ℕ} (c : ℝ) (hc : 0 < c)
    (g : WholeH1 n ℂ) (h : WholeL2 n ℂ) (φ : SpacetimeTest n ℂ)
    (T : ℝ) (hT : 0 < T)
    (hGreen : ∀ s : ℝ, (∫ t in s..T,
      hUnderlying ⊤ 1 ((complexWaveOperators n c hc).S (t-s)
        (TestSlices.wholeSliceL2 (TestSlices.spacetimeWaveTest c φ) t))) =
          TestSlices.wholeSliceL2 φ s) :
    (∫ t in Icc 0 T, TestSlices.scalarPair
      (hUnderlying ⊤ 1 ((complexWaveOperators n c hc).C1 t g +
        (complexWaveOperators n c hc).S t h))
      (TestSlices.wholeSliceL2 (TestSlices.spacetimeWaveTest c φ) t)) = 0 := by
  let W := complexWaveOperators n c hc
  let R := TestSlices.wholeSliceL2 (TestSlices.spacetimeWaveTest c φ)
  have hR : Continuous R := TestSlices.wholeSliceL2_continuous _
  have hΨ : HasDerivAt (TestSlices.wholeSliceL2 φ) 0 0 := by
    simpa only [TestSlices.wholeSliceL2_zero_nonpos (TestSlices.timeDerivTest φ) 0 le_rfl] using
      TestSlices.wholeSliceL2_hasDerivAt φ 0
  have hcos := waveCosine_green_initial c (ContinuousLinearMap.id ℝ ℂ) W
    (complexWaveFamilyLaws n c hc) R (TestSlices.wholeSliceL2 φ) hR T hT hGreen hΨ
  have hsine : (∫ t in 0..T, hUnderlying ⊤ 1 (W.S t (R t))) = 0 := by
    simpa only [sub_zero, TestSlices.wholeSliceL2_zero_nonpos φ 0 le_rfl] using hGreen 0
  rw [intervalIntegral.integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc] at hcos hsine
  exact complex_homogeneous_pairing_zero c hc T g h R hR hcos hsine

end P201.Wave.Cauchy
end

noncomputable section
open MeasureTheory Set
open P201 P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201.Wave.Cauchy
open TestSlices

/-- The original Fourier/Bochner formula solves the equation against every
smooth compact spacetime test for exactly local L¹-in-time L² forcing. -/
theorem complex_displacement_distributional {n : ℕ} (c : ℝ) (hc : 0 < c)
    (g : WholeH1 n ℂ) (h : WholeL2 n ℂ) (f : ℝ → WholeL2 n ℂ)
    (hf : LocallyIntegrableForcing f) :
    IsDistributionalWave c f (displacement (complexWaveOperators n c hc) g h f) := by
  let W := complexWaveOperators n c hc
  have hW := complexWaveFamilyLaws n c hc
  apply distributionalWave_of_finite_pairings
  intro φ
  obtain ⟨T,hT,hterminal,hGreen⟩ := spacetimeTest_sine_green c W hW φ
  refine ⟨T,fun t ht => ⟨(hterminal t ht).1, (hterminal t ht).2.2⟩,?_⟩
  let R := wholeSliceL2 (spacetimeWaveTest c φ)
  let U := hUnderlying (𝕜 := ℂ) (⊤ : Domain n) 1
  have hR : Continuous R := wholeSliceL2_continuous _
  have hhom : Continuous (fun t => W.C1 t g + W.S t h) := by
    have hh := (homogeneousRegularity c (ContinuousLinearMap.id ℝ ℂ) W hW g h).1
    change Continuous (fun t => displacement W g h 0 t) at hh
    simpa [displacement] using hh
  have hhPair : IntegrableOn (fun t => scalarPair
      (U (W.C1 t g + W.S t h)) (R t)) (Icc 0 T) :=
    (continuous_scalarPair.comp
      ((U.continuous.comp hhom).prodMk hR)).continuousOn.integrableOn_Icc
  have hsrc := (sineConvolution_continuousOn c (ContinuousLinearMap.id ℝ ℂ) W hW f hf).mono
    (show Icc (0 : ℝ) T ⊆ Ici 0 from fun _ ht => ht.1)
  have hsPair : IntegrableOn (fun t => scalarPair
      (U (∫ s in Icc 0 t, W.S (t-s) (f s))) (R t)) (Icc 0 T) :=
    (continuous_scalarPair.comp_continuousOn
      ((U.continuous.comp_continuousOn hsrc).prodMk hR.continuousOn)).integrableOn_Icc
  have hpoint (t : ℝ) : scalarPair (U (displacement W g h f t)) (R t) =
      scalarPair (U (W.C1 t g + W.S t h)) (R t) +
        scalarPair (U (∫ s in Icc 0 t, W.S (t-s) (f s))) (R t) := by
    simp only [displacement, map_add, ← scalarPairCLM_apply, _root_.add_apply]
  have hhomZero := complex_homogeneous_test_pairing_zero c hc g h φ T hT hGreen
  have hsrcEq := complexDuhamel_finite_pairing c hc φ T hT.le hGreen f (hf T hT.le)
  change (∫ t in Icc 0 T, scalarPair (U (displacement W g h f t)) (R t)) = _
  simp_rw [hpoint]
  rw [integral_add hhPair hsPair, hhomZero, zero_add]
  exact hsrcEq

/-- Full real and complex whole-space energy Cauchy theorem: Bochner formula,
one-sided initial derivative, distributional PDE and unrestricted comparison
within the original energy class. -/
theorem energyWaveCauchy : P201Specs.Wave.Cauchy.energyWaveCauchyStatement := by
  intro n hn c hc
  let W := complexWaveOperators n c hc
  have hW := complexWaveFamilyLaws n c hc
  constructor
  · apply cauchyForField_of_distributional c hc Complex.ofRealCLM (realWaveOperators W)
      (canonicalRealWaveFamilyLaws n c hc)
    intro g h f hf
    apply isDistributionalWave_real_displacement c W hW g h f hf
    exact complex_displacement_distributional c hc _ _ _ (locallyIntegrableForcing_ofReal f hf)
  · exact cauchyForField_of_distributional c hc (ContinuousLinearMap.id ℝ ℂ) W hW
      (complex_displacement_distributional c hc)

end P201.Wave.Cauchy
end
