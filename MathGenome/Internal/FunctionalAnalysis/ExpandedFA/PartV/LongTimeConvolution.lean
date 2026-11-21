import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.LongTimeConvolution
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ConvolutionEndpointBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace ExpandedFA.PartV.LongTimeConvolution

lemma causalConv_eq_integral {𝕜 : Type} [RCLike 𝕜] (r f : ℝ → 𝕜) (t : ℝ) :
    causalConv r f t = ∫ s, r s * (Ioi (0 : ℝ)).indicator f (t-s) ∂halfLineMeasure := by
  rw [causalConv, posConvolution_eq_convolution_indicator r f (ContinuousLinearMap.mul ℝ 𝕜) volume]
  change (∫ s, (Ioi (0 : ℝ)).indicator r s * (Ioi (0 : ℝ)).indicator f (t-s)) = _
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  ext s
  by_cases hs : s ∈ Ioi (0 : ℝ) <;> simp [hs]

/-- Bounded forcing need only be measurable and bounded on the positive half-line.
Dominated convergence gives the actual integral representative's pointwise limit. -/
theorem convolution_limit : Spec.ConvolutionLimit := by
  intro 𝕜 _ r f ℓ hr hf hM hlim
  obtain ⟨M, hM⟩ := hM
  have hM0 : 0 ≤ M := (norm_nonneg (f 1)).trans (hM 1 zero_lt_one)
  let F := (Ioi (0 : ℝ)).indicator f
  have hF : AEStronglyMeasurable F volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioi).mpr hf
  have hB (s : ℝ) : ‖F s‖ ≤ M := by
    by_cases hs : 0 < s
    · simpa [F, hs] using hM s hs
    · simp [F, hs, hM0]
  have hmeas (t : ℝ) : AEStronglyMeasurable (fun s => r s * F (t-s)) halfLineMeasure :=
    hr.aestronglyMeasurable.mul
      ((hF.comp_measurePreserving (volume.measurePreserving_sub_left t)).restrict)
  have hdom (t : ℝ) : ∀ᵐ s ∂halfLineMeasure,
      ‖r s * F (t-s)‖ ≤ ‖r s‖ * M :=
    Eventually.of_forall fun s => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  have hpt (s : ℝ) : Tendsto (fun t => r s * F (t-s)) atTop (𝓝 (r s * ℓ)) := by
    apply tendsto_const_nhds.mul
    have hshift : Tendsto (fun t : ℝ => f (t-s)) atTop (𝓝 ℓ) :=
      hlim.comp (by
        simpa only [sub_eq_add_neg, id_eq] using
          tendsto_atTop_add_const_right atTop (-s) tendsto_id)
    apply hshift.congr'
    filter_upwards [eventually_gt_atTop s] with t ht
    simp [F, sub_pos.mpr ht]
  have H := tendsto_integral_filter_of_dominated_convergence (μ := halfLineMeasure)
    (fun s => ‖r s‖ * M) (Eventually.of_forall hmeas)
    (Eventually.of_forall hdom) (hr.norm.mul_const M) (Eventually.of_forall hpt)
  simpa only [F, integral_mul_const, ← causalConv_eq_integral] using H

lemma integrable_causalConv {𝕜 : Type} [RCLike 𝕜] {k f : ℝ → 𝕜}
    (hk : Integrable k halfLineMeasure) (hf : Integrable f halfLineMeasure) :
    Integrable (causalConv k f) halfLineMeasure :=
  (integrable_posConvolution hk hf (ContinuousLinearMap.mul ℝ 𝕜)).restrict

lemma integral_causalConv {𝕜 : Type} [RCLike 𝕜] {k f : ℝ → 𝕜}
    (hk : Integrable k halfLineMeasure) (hf : Integrable f halfLineMeasure) :
    (∫ t, causalConv k f t ∂halfLineMeasure) =
      (∫ t, k t ∂halfLineMeasure) * ∫ t, f t ∂halfLineMeasure := by
  have he : causalConv k f =ᵐ[halfLineMeasure]
      (fun t => ∫ s in 0..t, k s * f (t-s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp [causalConv, posConvolution, ht]
  rw [integral_congr_ae he]
  exact integral_posConvolution hk hf (ContinuousLinearMap.mul ℝ 𝕜)

lemma norm_causalConv_le {𝕜 : Type} [RCLike 𝕜] (k f : ℝ → 𝕜) (t : ℝ) :
    ‖causalConv k f t‖ ≤ causalConv (fun s => ‖k s‖) (fun s => ‖f s‖) t := by
  simp only [causalConv_eq_integral]
  convert norm_integral_le_integral_norm
    (fun s => k s * (Ioi (0 : ℝ)).indicator f (t-s)) using 1
  congr 1
  ext s
  by_cases hs : t-s ∈ Ioi (0 : ℝ) <;> simp [hs, norm_mul]

lemma l1Norm_eq_integral_norm {𝕜 : Type} [RCLike 𝕜] {f : ℝ → 𝕜}
    (hf : Integrable f halfLineMeasure) :
    (eLpNorm f 1 halfLineMeasure).toReal = ∫ s, ‖f s‖ ∂halfLineMeasure := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]

lemma causalConv_l1_bound {𝕜 : Type} [RCLike 𝕜] {k f : ℝ → 𝕜}
    (hk : Integrable k halfLineMeasure) (hf : Integrable f halfLineMeasure) :
    (eLpNorm (causalConv k f) 1 halfLineMeasure).toReal ≤
      (eLpNorm k 1 halfLineMeasure).toReal * (eLpNorm f 1 halfLineMeasure).toReal := by
  rw [l1Norm_eq_integral_norm (integrable_causalConv hk hf),
    l1Norm_eq_integral_norm hk, l1Norm_eq_integral_norm hf]
  exact (integral_mono_ae (integrable_causalConv hk hf).norm
    (integrable_causalConv hk.norm hf.norm)
    (Eventually.of_forall (norm_causalConv_le k f))).trans_eq
      (integral_causalConv hk.norm hf.norm)

lemma integrable_kernelPower {𝕜 : Type} [RCLike 𝕜] {k : ℝ → 𝕜}
    (hk : Integrable k halfLineMeasure) (n : ℕ) :
    Integrable (kernelPower k n) halfLineMeasure := by
  induction n with
  | zero => exact hk
  | succ n ih => exact integrable_causalConv hk ih

lemma norm_powerClass {𝕜 : Type} [RCLike 𝕜] {k : ℝ → 𝕜}
    (hk : Integrable k halfLineMeasure) (n : ℕ) :
    ‖powerClass k n‖ = (eLpNorm (kernelPower k n) 1 halfLineMeasure).toReal := by
  have hm : MemLp (kernelPower k n) 1 halfLineMeasure :=
    (memLp_one_iff_integrable).mpr (integrable_kernelPower hk n)
  simp only [powerClass, dite_eq_left hm, Lp.norm_toLp]

lemma powerClass_coe {𝕜 : Type} [RCLike 𝕜] {k : ℝ → 𝕜}
    (hk : Integrable k halfLineMeasure) (n : ℕ) :
    (powerClass k n : ℝ → 𝕜) =ᵐ[halfLineMeasure] kernelPower k n := by
  have hm : MemLp (kernelPower k n) 1 halfLineMeasure :=
    (memLp_one_iff_integrable).mpr (integrable_kernelPower hk n)
  simp only [powerClass, dite_eq_left hm]
  exact hm.coeFn_toLp

lemma powerClass_bound {𝕜 : Type} [RCLike 𝕜] {k : ℝ → 𝕜}
    (hk : Integrable k halfLineMeasure) (n : ℕ) :
    ‖powerClass k n‖ ≤ (eLpNorm k 1 halfLineMeasure).toReal ^ (n+1) := by
  rw [norm_powerClass hk]
  induction n with
  | zero => simp [kernelPower]
  | succ n ih =>
    exact (causalConv_l1_bound hk (integrable_kernelPower hk n)).trans
      ((mul_le_mul_of_nonneg_left ih ENNReal.toReal_nonneg).trans_eq (pow_succ' _ _).symm)

/-- Convergence takes place in the genuine L¹ quotient with its norm topology. -/
theorem resolvent_series : Spec.Series := by
  intro 𝕜 _ k hk ha
  let a := (eLpNorm k 1 halfLineMeasure).toReal
  have hs : Summable (fun n : ℕ => a ^ (n+1)) :=
    (summable_geometric_of_lt_one ENNReal.toReal_nonneg ha).comp_injective
      (fun n m h => Nat.add_right_cancel h)
  have hn : Summable (fun n => ‖powerClass k n‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) (powerClass_bound hk)
  refine ⟨fun n => memLp_one_iff_integrable.mpr (integrable_kernelPower hk n),
    hn.of_norm.hasSum, ?_⟩
  apply (norm_tsum_le_tsum_norm hn).trans
  apply (Summable.tsum_le_tsum (powerClass_bound hk) hn hs).trans_eq
  have hgeom := hasSum_geometric_of_lt_one ENNReal.toReal_nonneg ha
  have hshift := (hasSum_nat_add_iff' 1).mpr hgeom
  have he : (∑' n : ℕ, a ^ (n+1)) = (1-a)⁻¹ - 1 := by
    simpa using hshift.tsum_eq
  rw [he]
  dsimp [a]
  field_simp
  ring

lemma integral_kernelPower {𝕜 : Type} [RCLike 𝕜] {k : ℝ → 𝕜}
    (hk : Integrable k halfLineMeasure) (n : ℕ) :
    (∫ t, kernelPower k n t ∂halfLineMeasure) =
      (∫ t, k t ∂halfLineMeasure) ^ (n+1) := by
  induction n with
  | zero => simp [kernelPower]
  | succ n ih =>
    rw [kernelPower, integral_causalConv hk (integrable_kernelPower hk n), ih]
    exact (pow_succ' _ (n+1)).symm

lemma kernel_integral_norm_lt_one {𝕜 : Type} [RCLike 𝕜] {k : ℝ → 𝕜}
    (hk : Integrable k halfLineMeasure)
    (ha : (eLpNorm k 1 halfLineMeasure).toReal < 1) :
    ‖∫ t, k t ∂halfLineMeasure‖ < 1 := by
  exact (norm_integral_le_integral_norm k).trans_lt ((l1Norm_eq_integral_norm hk).symm.trans_lt ha)

lemma integral_resolvent {𝕜 : Type} [RCLike 𝕜] {k : ℝ → 𝕜}
    (hk : Integrable k halfLineMeasure)
    (ha : (eLpNorm k 1 halfLineMeasure).toReal < 1) :
    (∫ t, resolvent k t ∂halfLineMeasure) =
      (∫ t, k t ∂halfLineMeasure) / (1 - ∫ t, k t ∂halfLineMeasure) := by
  have H := (resolvent_series k hk ha).2.1.mapL
    (L1.integralCLM : Lp 𝕜 1 halfLineMeasure →L[ℝ] 𝕜)
  have hI (f : Lp 𝕜 1 halfLineMeasure) :
      L1.integralCLM f = ∫ t, f t ∂halfLineMeasure :=
    (L1.integral_eq f).symm.trans (L1.integral_eq_integral f)
  have H' : HasSum (fun n => ∫ t, powerClass k n t ∂halfLineMeasure)
      (∫ t, resolvent k t ∂halfLineMeasure) := by
    rw [← hI (resolvent k)]
    exact H.congr_fun (fun n => (hI (powerClass k n)).symm)
  have ht (n : ℕ) : (∫ t, powerClass k n t ∂halfLineMeasure) =
      (∫ t, k t ∂halfLineMeasure) ^ (n+1) :=
    (integral_congr_ae (powerClass_coe hk n)).trans (integral_kernelPower hk n)
  have H'' := H'.congr_fun (fun n => (ht n).symm)
  have hn := kernel_integral_norm_lt_one hk ha
  have hg := (hasSum_nat_add_iff' (f := fun n : ℕ => (∫ t, k t ∂halfLineMeasure) ^ n)
    (g := (1 - ∫ t, k t ∂halfLineMeasure)⁻¹) 1).mpr (hasSum_geometric_of_norm_lt_one hn)
  have he := H''.unique hg
  simp only [Finset.sum_range_one, pow_zero] at he
  rw [he]
  have hc : (1 : 𝕜) - ∫ t, k t ∂halfLineMeasure ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    rw [← h, norm_one] at hn
    exact (lt_irrefl (1 : ℝ)) hn
  field_simp
  ring

/-- The bounded-forcing limit, including complex kernels and zero mass. -/
theorem long_time_limit : Spec.LongTimeLimit := by
  intro 𝕜 _ k hk ha f ℓ hf hb hl
  have H := hl.add (convolution_limit (resolvent k) f ℓ (L1.integrable_coeFn _) hf hb hl)
  rw [integral_resolvent hk ha] at H
  convert H using 1
  have hn := kernel_integral_norm_lt_one hk ha
  have hc : (1 : 𝕜) - ∫ t, k t ∂halfLineMeasure ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    rw [← h, norm_one] at hn
    exact (lt_irrefl (1 : ℝ)) hn
  congr 1
  field_simp
  ring

lemma laplace_weight_bound (z : ℂ) (hz : 0 ≤ z.re) (t : ℝ) (ht : 0 < t) :
    ‖Complex.exp (-z * (t : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simpa using neg_nonpos.mpr (mul_nonneg hz ht.le)

lemma integrable_laplace_integrand {k : ℝ → ℂ} (hk : Integrable k halfLineMeasure)
    {z : ℂ} (hz : 0 ≤ z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * k t) halfLineMeasure := by
  apply hk.bdd_mul
    ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z * (t : ℂ)))).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact laplace_weight_bound z hz t ht

lemma laplace_norm_le {k : ℝ → ℂ} (hk : Integrable k halfLineMeasure)
    {z : ℂ} (hz : 0 ≤ z.re) :
    ‖laplace k z‖ ≤ (eLpNorm k 1 halfLineMeasure).toReal := by
  rw [l1Norm_eq_integral_norm hk]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (integrable_laplace_integrand hk hz).norm hk.norm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (laplace_weight_bound z hz t ht)

lemma laplace_congr {f g : ℝ → ℂ} (h : f =ᵐ[halfLineMeasure] g) (z : ℂ) :
    laplace f z = laplace g z :=
  integral_congr_ae (h.mono fun t ht => congrArg (Complex.exp (-z * (t : ℂ)) * ·) ht)

lemma laplace_add {f g : ℝ → ℂ} (hf : Integrable f halfLineMeasure)
    (hg : Integrable g halfLineMeasure) {z : ℂ} (hz : 0 ≤ z.re) :
    laplace (f+g) z = laplace f z + laplace g z := by
  simp only [laplace, Pi.add_apply, mul_add]
  exact integral_add (integrable_laplace_integrand hf hz) (integrable_laplace_integrand hg hz)

lemma laplace_smul (c : ℂ) (f : ℝ → ℂ) (z : ℂ) :
    laplace (c • f) z = c * laplace f z := by
  simp only [laplace, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  ext t
  ring

/-- Laplace evaluation on the closed right half-plane is a bounded functional
on the genuine L¹ quotient. -/
def laplaceCLM (z : ℂ) (hz : 0 ≤ z.re) : Lp ℂ 1 halfLineMeasure →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => laplace f z
      map_add' := fun f g => (laplace_congr (Lp.coeFn_add f g) z).trans
        (laplace_add (L1.integrable_coeFn f) (L1.integrable_coeFn g) hz)
      map_smul' := fun c f => (laplace_congr (Lp.coeFn_smul c f) z).trans
        (laplace_smul c f z) }
    1 (fun f => by
      change ‖laplace f z‖ ≤ 1 * ‖f‖
      simpa only [one_mul, Lp.norm_def] using laplace_norm_le (L1.integrable_coeFn f) hz)

lemma laplace_weight_mul (z : ℂ) (s t : ℝ) :
    Complex.exp (-z * (t : ℂ)) =
      Complex.exp (-z * (s : ℂ)) * Complex.exp (-z * ((t-s : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma weighted_causalConv (k f : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    Complex.exp (-z * (t : ℂ)) * causalConv k f t =
      causalConv (fun s : ℝ => Complex.exp (-z * (s : ℂ)) * k s)
        (fun s : ℝ => Complex.exp (-z * (s : ℂ)) * f s) t := by
  rw [causalConv_eq_integral, causalConv_eq_integral, ← integral_const_mul]
  congr 1
  ext s
  by_cases hs : t-s ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem hs]
    rw [laplace_weight_mul z s t]
    ring
  · simp only [indicator_of_notMem hs, mul_zero]

lemma laplace_causalConv {k f : ℝ → ℂ} (hk : Integrable k halfLineMeasure)
    (hf : Integrable f halfLineMeasure) {z : ℂ} (hz : 0 ≤ z.re) :
    laplace (causalConv k f) z = laplace k z * laplace f z := by
  unfold laplace
  simp only [weighted_causalConv]
  exact integral_causalConv (integrable_laplace_integrand hk hz) (integrable_laplace_integrand hf hz)

lemma laplace_kernelPower {k : ℝ → ℂ} (hk : Integrable k halfLineMeasure)
    {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    laplace (kernelPower k n) z = laplace k z ^ (n+1) := by
  induction n with
  | zero => simp [kernelPower]
  | succ n ih =>
    rw [kernelPower, laplace_causalConv hk (integrable_kernelPower hk n) hz, ih]
    exact (pow_succ' _ (n+1)).symm

/-- Absolute Fubini and continuity of Laplace evaluation identify the series
on the boundary Re z = 0 as well as in the open right half-plane. -/
theorem laplace_identity : Spec.LaplaceIdentity := by
  intro k hk ha z hz
  have hn : ‖laplace k z‖ < 1 := (laplace_norm_le hk hz).trans_lt ha
  have hc : 1 - laplace k z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    rw [← h, norm_one] at hn
    exact (lt_irrefl (1 : ℝ)) hn
  refine ⟨integrable_laplace_integrand hk hz,
    integrable_laplace_integrand (L1.integrable_coeFn _) hz, hc, ?_⟩
  have H := (resolvent_series k hk ha).2.1.mapL (laplaceCLM z hz)
  change HasSum (fun n => laplace (powerClass k n) z) (laplace (resolvent k) z) at H
  have ht (n : ℕ) : laplace (powerClass k n) z = laplace k z ^ (n+1) :=
    (laplace_congr (powerClass_coe hk n) z).trans (laplace_kernelPower hk hz n)
  have H' := H.congr_fun (fun n => (ht n).symm)
  have hg := (hasSum_nat_add_iff' (f := fun n : ℕ => laplace k z ^ n)
    (g := (1 - laplace k z)⁻¹) 1).mpr (hasSum_geometric_of_norm_lt_one hn)
  have he := H'.unique hg
  simp only [Finset.sum_range_one, pow_zero] at he
  rw [he]
  field_simp
  ring

/-- The L¹–Lp endpoint on ℝ. This applies the accepted, measure-generic
Minkowski integral theorem; it includes p=∞ by Hölder. -/
lemma real_young {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) (hp : 1 ≤ p)
    (k f : ℝ → 𝕜) (hk : MemLp k 1 volume) (hf : MemLp f p volume) :
    (∀ᵐ t ∂volume, ConvolutionExistsAt k f t (ContinuousLinearMap.mul ℝ 𝕜) volume) ∧
    MemLp (convolution k f (ContinuousLinearMap.mul ℝ 𝕜) volume) p volume ∧
    eLpNorm (convolution k f (ContinuousLinearMap.mul ℝ 𝕜) volume) p volume ≤
      eLpNorm k 1 volume * eLpNorm f p volume := by
  let L := ContinuousLinearMap.mul ℝ 𝕜
  have hm := hk.aestronglyMeasurable.convolution L hf.aestronglyMeasurable
  by_cases hpt : p = ∞
  · subst p
    have hi := ConvolutionExists.of_memLp_memLp L hk hf
    have hb (t : ℝ) : ‖convolution k f L volume t‖ₑ ≤ eLpNorm k 1 volume * eLpNorm f ∞ volume := by
      simpa [L] using enorm_convolution_le L hk.aestronglyMeasurable hf.aestronglyMeasurable t
    have hn : eLpNorm (convolution k f L volume) ∞ volume ≤ eLpNorm k 1 volume * eLpNorm f ∞ volume := by
      rw [eLpNorm_exponent_top hm]
      exact eLpNormEssSup_le_of_ae_enorm_bound (Eventually.of_forall hb)
    exact ⟨Eventually.of_forall hi, hn.trans_lt (ENNReal.mul_lt_top hk hf), hn⟩
  let : MeasurableSpace 𝕜 := borel 𝕜
  let K := hk.aestronglyMeasurable.mk k
  let F := hf.aestronglyMeasurable.mk f
  have hK : Measurable K := hk.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hF : Measurable F := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have heK : k =ᵐ[volume] K := hk.aestronglyMeasurable.ae_eq_mk
  have heF : f =ᵐ[volume] F := hf.aestronglyMeasurable.ae_eq_mk
  let G : ℝ × ℝ → 𝕜 := fun z => K z.2 * F (z.1-z.2)
  have hG : Measurable G := (hK.comp measurable_snd).mul
    (hF.comp (measurable_fst.sub measurable_snd))
  have hs (s : ℝ) : eLpNorm (fun t => G (t,s)) p volume = ‖K s‖ₑ * eLpNorm F p volume := by
    change eLpNorm ((K s) • (fun t => F (t-s))) p volume = _
    rw [eLpNorm_const_smul]
    exact congrArg (‖K s‖ₑ * ·) (eLpNorm_comp_measurePreserving (hf.ae_eq heF).aestronglyMeasurable
      (measurePreserving_sub_right volume s))
  have hR : (∫⁻ s, eLpNorm (fun t => G (t,s)) p volume) = eLpNorm k 1 volume * eLpNorm f p volume := by
    simp_rw [hs]
    rw [lintegral_mul_const _ hK.enorm, ← eLpNorm_one_eq_lintegral_enorm hK.aestronglyMeasurable,
      eLpNorm_congr_ae heK.symm, eLpNorm_congr_ae heF.symm]
  obtain ⟨hi, hb⟩ := ExpandedFA.Distributions.minkowski_integral_eLpNorm
    volume volume p hp hpt G hG (by rw [hR]; exact ENNReal.mul_lt_top hk hf)
  have he := convolution_congr L heK heF
  have hi' : ∀ᵐ t ∂volume, ConvolutionExistsAt k f t L volume := by
    filter_upwards [hi] with t ht
    exact ht.congr ((heK.mul ((volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae heF)).symm)
  have hb' : eLpNorm (convolution k f L volume) p volume ≤ eLpNorm k 1 volume * eLpNorm f p volume := by
    rw [he]
    exact hb.trans_eq hR
  exact ⟨hi', hb'.trans_lt (ENNReal.mul_lt_top hk hf), hb'⟩

lemma causal_young {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) (hp : 1 ≤ p)
    (k f : ℝ → 𝕜) (hk : MemLp k 1 halfLineMeasure) (hf : MemLp f p halfLineMeasure) :
    MemLp (causalConv k f) p halfLineMeasure ∧
    eLpNorm (causalConv k f) p halfLineMeasure ≤
      eLpNorm k 1 halfLineMeasure * eLpNorm f p halfLineMeasure := by
  have hK := (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hk
  have hF := (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hf
  obtain ⟨_, hm, hb⟩ := real_young p hp _ _ hK hF
  have he := posConvolution_eq_convolution_indicator k f (ContinuousLinearMap.mul ℝ 𝕜) volume
  change MemLp (posConvolution k f (ContinuousLinearMap.mul ℝ 𝕜) volume) p halfLineMeasure ∧ _
  rw [he]
  refine ⟨hm.restrict _, ?_⟩
  apply (eLpNorm_restrict_le _ p volume (Ioi (0 : ℝ))).trans
  simpa only [causalConv, he, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi.nullMeasurableSet] using hb

private abbrev Z {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) := (Ioi (0 : ℝ)).indicator f

lemma zeroExtend_ae_eq {𝕜 : Type} [RCLike 𝕜] {f g : ℝ → 𝕜}
    (h : f =ᵐ[halfLineMeasure] g) : Z f =ᵐ[volume] Z g := by
  have hh := (ae_restrict_iff' measurableSet_Ioi).mp h
  filter_upwards [hh] with t ht
  by_cases hs : t ∈ Ioi (0 : ℝ)
  · simp [Z, hs, ht hs]
  · simp [Z, hs]

lemma causalConv_congr {𝕜 : Type} [RCLike 𝕜] {k k' f f' : ℝ → 𝕜}
    (hk : k =ᵐ[halfLineMeasure] k') (hf : f =ᵐ[halfLineMeasure] f') :
    causalConv k f = causalConv k' f' := by
  simp only [causalConv, posConvolution_eq_convolution_indicator _ _ _ volume]
  exact convolution_congr _ (zeroExtend_ae_eq hk) (zeroExtend_ae_eq hf)

lemma causalConv_full {𝕜 : Type} [RCLike 𝕜] (k f : ℝ → 𝕜) :
    causalConv k f = convolution (Z k) (Z f) (ContinuousLinearMap.mul ℝ 𝕜) volume :=
  posConvolution_eq_convolution_indicator k f (ContinuousLinearMap.mul ℝ 𝕜) volume

lemma zeroExtend_causalConv {𝕜 : Type} [RCLike 𝕜] (k f : ℝ → 𝕜) :
    Z (causalConv k f) = causalConv k f := by
  ext t
  by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [Z, causalConv, posConvolution, ht]

lemma causalConv_comm {𝕜 : Type} [RCLike 𝕜] (k f : ℝ → 𝕜) :
    causalConv k f = causalConv f k := by
  rw [causalConv_full, causalConv_full]
  exact convolution_symm (ContinuousLinearMap.mul ℝ 𝕜)
    (by ext a b; exact mul_comm b a)

lemma causalConv_add_right {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {k f g : ℝ → 𝕜} (hk : MemLp k 1 halfLineMeasure)
    (hf : MemLp f p halfLineMeasure) (hg : MemLp g p halfLineMeasure) :
    causalConv k (f+g) =ᵐ[halfLineMeasure] causalConv k f + causalConv k g := by
  have hK := (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hk
  have hF := (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hf
  have hG := (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hg
  have hiF := (real_young p hp _ _ hK hF).1
  have hiG := (real_young p hp _ _ hK hG).1
  apply ae_restrict_of_ae
  filter_upwards [hiF, hiG] with t ht ht'
  simp only [causalConv_full, Z, indicator_add', Pi.add_apply]
  exact ht.distrib_add ht'

lemma causalConv_add_left {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {k r f : ℝ → 𝕜} (hk : MemLp k 1 halfLineMeasure)
    (hr : MemLp r 1 halfLineMeasure) (hf : MemLp f p halfLineMeasure) :
    causalConv (k+r) f =ᵐ[halfLineMeasure] causalConv k f + causalConv r f := by
  have hK := (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hk
  have hR := (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hr
  have hF := (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hf
  have hiK := (real_young p hp _ _ hK hF).1
  have hiR := (real_young p hp _ _ hR hF).1
  apply ae_restrict_of_ae
  filter_upwards [hiK, hiR] with t ht ht'
  simp only [causalConv_full, Z, indicator_add', Pi.add_apply]
  exact ht.add_distrib ht'

lemma causalConv_smul_right {𝕜 : Type} [RCLike 𝕜] (k f : ℝ → 𝕜) (c : 𝕜) :
    causalConv k (c • f) = c • causalConv k f := by
  ext t
  simp only [Pi.smul_apply, causalConv_eq_integral]
  rw [← integral_smul]
  congr 1
  ext s
  by_cases hs : t-s ∈ Ioi (0 : ℝ) <;> simp [hs, mul_left_comm]

lemma causalConv_smul_left {𝕜 : Type} [RCLike 𝕜] (k f : ℝ → 𝕜) (c : 𝕜) :
    causalConv (c • k) f = c • causalConv k f := by
  rw [causalConv_comm, causalConv_smul_right, causalConv_comm f k]

lemma causalConv_assoc {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {k r f : ℝ → 𝕜} (hk : MemLp k 1 halfLineMeasure)
    (hr : MemLp r 1 halfLineMeasure) (hf : MemLp f p halfLineMeasure) :
    causalConv (causalConv k r) f =ᵐ[halfLineMeasure] causalConv k (causalConv r f) := by
  let L := ContinuousLinearMap.mul ℝ 𝕜
  have hK := (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hk
  have hR := (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hr
  have hF := (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hf
  have hkr := (real_young 1 le_rfl _ _ hK hR).1
  obtain ⟨hrf, hrfmem, _⟩ := real_young p hp _ _ hR.norm hF.norm
  have hkrf := (real_young p hp _ _ hK.norm hrfmem).1
  rw [causalConv_full (causalConv k r) f, causalConv_full k (causalConv r f),
    zeroExtend_causalConv, zeroExtend_causalConv, causalConv_full k r, causalConv_full r f]
  apply ae_restrict_of_ae
  filter_upwards [hkrf] with t ht
  exact convolution_assoc L L L L (fun a b c => mul_assoc a b c)
    hK.aestronglyMeasurable hR.aestronglyMeasurable hF.aestronglyMeasurable hkr hrf ht

section LpAction
variable {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The integral convolution as an ordinary Lp class. -/
def lpConv (k : Lp 𝕜 1 halfLineMeasure) (f : Lp 𝕜 p halfLineMeasure) : Lp 𝕜 p halfLineMeasure :=
  ((causal_young p Fact.out k f (Lp.memLp k) (Lp.memLp f)).1).toLp (causalConv k f)

lemma lpConv_coe (k : Lp 𝕜 1 halfLineMeasure) (f : Lp 𝕜 p halfLineMeasure) :
    (lpConv k f : ℝ → 𝕜) =ᵐ[halfLineMeasure] causalConv k f := MemLp.coeFn_toLp _

lemma lpConv_bound (k : Lp 𝕜 1 halfLineMeasure) (f : Lp 𝕜 p halfLineMeasure) :
    ‖lpConv k f‖ ≤ ‖k‖ * ‖f‖ := by
  rw [lpConv, Lp.norm_toLp, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.memLp k).ne (Lp.memLp f).ne)
    (causal_young p Fact.out k f (Lp.memLp k) (Lp.memLp f)).2

lemma lpConv_add_right (k : Lp 𝕜 1 halfLineMeasure) (f g : Lp 𝕜 p halfLineMeasure) :
    lpConv k (f+g) = lpConv k f + lpConv k g := by
  apply Lp.ext
  refine (lpConv_coe k (f+g)).trans ?_
  have he := causalConv_congr (k := (k : ℝ → 𝕜)) ae_eq_rfl (Lp.coeFn_add f g)
  refine (EventuallyEq.of_eq he).trans ?_
  refine (causalConv_add_right Fact.out (Lp.memLp k) (Lp.memLp f) (Lp.memLp g)).trans ?_
  exact ((lpConv_coe k f).add (lpConv_coe k g)).symm.trans (Lp.coeFn_add _ _).symm

lemma lpConv_add_left (k r : Lp 𝕜 1 halfLineMeasure) (f : Lp 𝕜 p halfLineMeasure) :
    lpConv (k+r) f = lpConv k f + lpConv r f := by
  apply Lp.ext
  refine (lpConv_coe (k+r) f).trans ?_
  have he := causalConv_congr (Lp.coeFn_add k r) (f := (f : ℝ → 𝕜)) ae_eq_rfl
  refine (EventuallyEq.of_eq he).trans ?_
  refine (causalConv_add_left Fact.out (Lp.memLp k) (Lp.memLp r) (Lp.memLp f)).trans ?_
  exact ((lpConv_coe k f).add (lpConv_coe r f)).symm.trans (Lp.coeFn_add _ _).symm

lemma lpConv_smul_right (k : Lp 𝕜 1 halfLineMeasure) (f : Lp 𝕜 p halfLineMeasure) (c : 𝕜) :
    lpConv k (c • f) = c • lpConv k f := by
  apply Lp.ext
  refine (lpConv_coe k (c • f)).trans ?_
  have he := causalConv_congr (k := (k : ℝ → 𝕜)) ae_eq_rfl (Lp.coeFn_smul c f)
  refine (EventuallyEq.of_eq (he.trans (causalConv_smul_right k f c))).trans ?_
  exact ((lpConv_coe k f).const_smul c).symm.trans (Lp.coeFn_smul c _).symm

lemma lpConv_smul_left (k : Lp 𝕜 1 halfLineMeasure) (f : Lp 𝕜 p halfLineMeasure) (c : 𝕜) :
    lpConv (c • k) f = c • lpConv k f := by
  apply Lp.ext
  refine (lpConv_coe (c • k) f).trans ?_
  have he := causalConv_congr (Lp.coeFn_smul c k) (f := (f : ℝ → 𝕜)) ae_eq_rfl
  refine (EventuallyEq.of_eq (he.trans (causalConv_smul_left k f c))).trans ?_
  exact ((lpConv_coe k f).const_smul c).symm.trans (Lp.coeFn_smul c _).symm

/-- The causal convolution action is bounded in both variables. -/
def convolutionAction : Lp 𝕜 1 halfLineMeasure →L[𝕜]
    Lp 𝕜 p halfLineMeasure →L[𝕜] Lp 𝕜 p halfLineMeasure :=
  LinearMap.mkContinuous₂
    { toFun := fun k =>
        { toFun := lpConv k
          map_add' := lpConv_add_right k
          map_smul' := fun c f => lpConv_smul_right k f c }
      map_add' := fun k r => by
        apply LinearMap.ext
        intro f
        exact lpConv_add_left k r f
      map_smul' := fun c k => by
        apply LinearMap.ext
        intro f
        exact lpConv_smul_left k f c }
    1 (fun k f => by
      change ‖lpConv k f‖ ≤ 1 * ‖k‖ * ‖f‖
      simpa only [one_mul] using lpConv_bound k f)

lemma convolutionAction_apply (k : Lp 𝕜 1 halfLineMeasure) (f : Lp 𝕜 p halfLineMeasure) :
    convolutionAction k f = lpConv k f := rfl

lemma convolutionAction_norm (k : Lp 𝕜 1 halfLineMeasure) :
    ‖convolutionAction (p := p) k‖ ≤ ‖k‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg k) (lpConv_bound k)

lemma lpConv_assoc (k r : Lp 𝕜 1 halfLineMeasure) (f : Lp 𝕜 p halfLineMeasure) :
    lpConv (lpConv k r) f = lpConv k (lpConv r f) := by
  apply Lp.ext
  refine (lpConv_coe _ f).trans ?_
  have hl := causalConv_congr (lpConv_coe k r) (f := (f : ℝ → 𝕜)) ae_eq_rfl
  have hr := causalConv_congr (k := (k : ℝ → 𝕜)) ae_eq_rfl (lpConv_coe r f)
  refine (EventuallyEq.of_eq hl).trans ?_
  refine (causalConv_assoc Fact.out (Lp.memLp k) (Lp.memLp r) (Lp.memLp f)).trans ?_
  exact (EventuallyEq.of_eq hr.symm).trans (lpConv_coe _ _).symm

end LpAction

lemma lpConv_powerClass {𝕜 : Type} [RCLike 𝕜] {k : ℝ → 𝕜}
    (hk : Integrable k halfLineMeasure) (n : ℕ) :
    lpConv (powerClass k 0) (powerClass k n) = powerClass k (n+1) := by
  apply Lp.ext
  refine (lpConv_coe _ _).trans ?_
  have he := causalConv_congr (powerClass_coe hk 0) (powerClass_coe hk n)
  exact (EventuallyEq.of_eq he).trans (powerClass_coe hk (n+1)).symm

lemma resolvent_equation {𝕜 : Type} [RCLike 𝕜] {k : ℝ → 𝕜}
    (hk : Integrable k halfLineMeasure) (ha : (eLpNorm k 1 halfLineMeasure).toReal < 1) :
    lpConv (powerClass k 0) (resolvent k) = resolvent k - powerClass k 0 := by
  have H := (resolvent_series k hk ha).2.1.mapL
    (convolutionAction (p := 1) (powerClass k 0))
  have H' := H.congr_fun (fun n => (lpConv_powerClass hk n).symm)
  have HS := (hasSum_nat_add_iff' (f := powerClass k) (g := resolvent k) 1).mpr
    (resolvent_series k hk ha).2.1
  simpa only [Finset.sum_range_one, convolutionAction_apply] using H'.unique HS

/-- The same L¹ resolvent gives the inverse on every Lp space, including L∞.
Uniqueness holds among all Lp solutions of the equation. -/
theorem lp_solution : Spec.LpSolution := by
  intro 𝕜 _ k hk ha p _ f
  let K := powerClass k 0
  let R := resolvent k
  have hK : (K : ℝ → 𝕜) =ᵐ[halfLineMeasure] k := by
    simpa only [K, kernelPower] using powerClass_coe hk 0
  have hnK : ‖K‖ < 1 := by
    simpa only [K, norm_powerClass hk, kernelPower] using ha
  have hKR : lpConv K R = R-K := resolvent_equation hk ha
  let u := f + lpConv R f
  have hsub : lpConv (R-K) f = lpConv R f - lpConv K f := by
    change convolutionAction (R-K) f = convolutionAction R f - convolutionAction K f
    rw [map_sub]
    rfl
  have hKu : lpConv K u = lpConv R f := by
    dsimp [u]
    rw [lpConv_add_right, ← lpConv_assoc, hKR, hsub]
    abel
  have hu : u = f + lpConv K u := by rw [hKu]
  have rep (v : Lp 𝕜 p halfLineMeasure) :
      ((f + lpConv K v : Lp 𝕜 p halfLineMeasure) : ℝ → 𝕜) =ᵐ[halfLineMeasure]
        (fun t => f t + causalConv k v t) := by
    refine (Lp.coeFn_add _ _).trans ?_
    have he := causalConv_congr hK (f := (v : ℝ → 𝕜)) ae_eq_rfl
    exact EventuallyEq.add ae_eq_rfl ((lpConv_coe K v).trans (EventuallyEq.of_eq he))
  refine ⟨u, ?_, ?_, ?_⟩
  · exact (EventuallyEq.of_eq (congrArg (fun w : Lp 𝕜 p halfLineMeasure => (w : ℝ → 𝕜)) hu)).trans (rep u)
  · exact (Lp.coeFn_add f (lpConv R f)).trans (EventuallyEq.add ae_eq_rfl (lpConv_coe R f))
  · intro v hv
    have hv' : v = f + lpConv K v := Lp.ext (hv.trans (rep v).symm)
    have hd : v-u = lpConv K (v-u) := by
      change v-u = convolutionAction K (v-u)
      rw [map_sub]
      change v-u = lpConv K v - lpConv K u
      conv_lhs => rw [hv', hu]
      abel
    have hb : ‖v-u‖ ≤ ‖K‖ * ‖v-u‖ :=
      (congrArg norm hd).le.trans (lpConv_bound K (v-u))
    have hz : ‖v-u‖ = 0 := by nlinarith [norm_nonneg (v-u)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma causalConv_ofReal (k f : ℝ → ℝ) :
    causalConv (fun t => (k t : ℂ)) (fun t => (f t : ℂ)) =
      fun t => ((causalConv k f t : ℝ) : ℂ) := by
  ext t
  simp only [causalConv_eq_integral]
  rw [← integral_complex_ofReal]
  congr 1
  ext s
  by_cases hs : t-s ∈ Ioi (0 : ℝ) <;> simp [hs]

lemma kernelPower_ofReal (k : ℝ → ℝ) (n : ℕ) :
    kernelPower (fun t => (k t : ℂ)) n = fun t => ((kernelPower k n t : ℝ) : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [kernelPower, ih, causalConv_ofReal]
    rfl

lemma complexify_eLpNorm {k : ℝ → ℝ} (hk : AEStronglyMeasurable k halfLineMeasure) :
    eLpNorm (fun t => (k t : ℂ)) 1 halfLineMeasure = eLpNorm k 1 halfLineMeasure := by
  apply eLpNorm_congr_norm_ae (Complex.continuous_ofReal.comp_aestronglyMeasurable hk) hk
  exact Eventually.of_forall fun _ => by simp

lemma resolvent_ofReal {k : ℝ → ℝ} (hk : Integrable k halfLineMeasure)
    (ha : (eLpNorm k 1 halfLineMeasure).toReal < 1) :
    (resolvent (fun t => (k t : ℂ)) : ℝ → ℂ) =ᵐ[halfLineMeasure]
      (fun t => (resolvent k t : ℂ)) := by
  let C := Complex.ofRealCLM.compLpL 1 halfLineMeasure
  have hC (f : Lp ℝ 1 halfLineMeasure) :
      (C f : ℝ → ℂ) =ᵐ[halfLineMeasure] (fun t => (f t : ℂ)) :=
    Complex.ofRealCLM.coeFn_compLpL f
  have hkc : Integrable (fun t => (k t : ℂ)) halfLineMeasure :=
    memLp_one_iff_integrable.mp (memLp_one_iff_integrable.mpr hk).ofReal
  have hac : (eLpNorm (fun t => (k t : ℂ)) 1 halfLineMeasure).toReal < 1 := by
    rwa [complexify_eLpNorm hk.aestronglyMeasurable]
  have ht (n : ℕ) : C (powerClass k n) = powerClass (fun t => (k t : ℂ)) n := by
    apply Lp.ext
    refine (hC _).trans ?_
    have hp : (fun t => ((powerClass k n t : ℝ) : ℂ)) =ᵐ[halfLineMeasure]
        (fun t => ((kernelPower k n t : ℝ) : ℂ)) := by
      filter_upwards [powerClass_coe hk n] with t ht
      exact congrArg Complex.ofReal ht
    refine hp.trans ?_
    have hpC := powerClass_coe hkc n
    rw [kernelPower_ofReal] at hpC
    exact hpC.symm
  have H := (resolvent_series k hk ha).2.1.mapL C
  have H' := H.congr_fun (fun n => (ht n).symm)
  have he := H'.unique (resolvent_series (fun t => (k t : ℂ)) hkc hac).2.1
  rw [← he]
  exact hC _

theorem real_laplace_identity : Spec.RealLaplaceIdentity := by
  intro k hk ha z hz
  have hkc : Integrable (fun t => (k t : ℂ)) halfLineMeasure :=
    memLp_one_iff_integrable.mp (memLp_one_iff_integrable.mpr hk).ofReal
  have hac : (eLpNorm (fun t => (k t : ℂ)) 1 halfLineMeasure).toReal < 1 := by
    rwa [complexify_eLpNorm hk.aestronglyMeasurable]
  obtain ⟨_, _, hn, he⟩ := laplace_identity _ hkc hac z hz
  exact ⟨hn, (laplace_congr (resolvent_ofReal hk ha).symm z).trans he⟩

lemma unstable_convolution (t : ℝ) (ht : 0 ≤ t) :
    causalConv (fun s : ℝ => 2 * Real.exp (-s))
      (fun s => 2 * Real.exp s - 1) t = 2 * Real.exp t - 2 := by
  by_cases ht' : 0 < t
  · unfold causalConv posConvolution
    rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht')]
    change (∫ s in 0..t, 2 * Real.exp (-s) * (2 * Real.exp (t-s) - 1)) = _
    have hd (s : ℝ) : HasDerivAt
        (fun s : ℝ => -2 * Real.exp (t-2*s) + 2 * Real.exp (-s))
        (2 * Real.exp (-s) * (2 * Real.exp (t-s) - 1)) s := by
      have H := ((((hasDerivAt_id s).const_mul 2).const_sub t).exp.const_mul (-2)).add
        ((hasDerivAt_id s).neg.exp.const_mul 2)
      convert H using 1
      · rfl
      · have he : Real.exp (t-2*s) = Real.exp (-s) * Real.exp (t-s) := by
          rw [← Real.exp_add]
          congr 1
          ring
        simp only [id_eq, Pi.neg_apply, he]
        ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      ((by fun_prop : Continuous (fun s : ℝ =>
        2 * Real.exp (-s) * (2 * Real.exp (t-s) - 1))).intervalIntegrable 0 t)]
    rw [show t - 2*t = -t by ring]
    simp
    ring
  · have ht0 : t = 0 := le_antisymm (le_of_not_gt ht') ht
    subst t
    simp [causalConv, posConvolution]

/-- An integrable causal kernel can produce an exponentially growing solution
of the equation with constant forcing, even on every finite time interval. -/
theorem unstable_example : Spec.UnstableExample := by
  change Integrable (fun t : ℝ => 2 * Real.exp (-t)) halfLineMeasure ∧ _
  refine ⟨(integrableOn_exp_neg_Ioi 0).const_mul 2, ?_, ?_, ?_⟩
  · rw [integral_const_mul]
    simp only [halfLineMeasure, integral_exp_neg_Ioi_zero, mul_one]
  · intro t ht
    rw [unstable_convolution t ht]
    ring
  · simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ)
      (Real.tendsto_exp_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))

end ExpandedFA.PartV.LongTimeConvolution
