import MathGenome.Internal.FourierSobolev.Specs.P102.U2.PrincipalValues
import MathGenome.Internal.FourierSobolev.P102.U2.MaximalTruncation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace P102.U2.PrincipalValues
open CZWeak CZLpData MaximalTruncationData
open ExpandedFA.SingularIntegrals.StandardConvolution

variable {d : ℕ}

lemma truncated_sub (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0}
    (hK : KernelRegularity K B) (p : Exponent) {f g : Point d → ℂ}
    (hf : MemLp f p.val volume) (hg : MemLp g p.val volume)
    {ε : ℝ} (hε : 0 < ε) (x : Point d) :
    truncated K (f - g) ε x = truncated K f ε x - truncated K g ε x := by
  unfold truncated
  simp only [Pi.sub_apply, mul_sub]
  exact integral_sub (MaximalTruncation.lp_truncated_integrable hd hK p hf hε x)
    (MaximalTruncation.lp_truncated_integrable hd hK p hg hε x)

lemma norm_truncated_le {K f : Point d → ℂ} {ε : ℝ} (hε : 0 < ε) (x : Point d)
    (hx : maximalTruncation K f x < ∞) :
    ‖truncated K f ε x‖ ≤ (maximalTruncation K f x).toReal := by
  have he : ‖truncated K f ε x‖ₑ ≤ maximalTruncation K f x :=
    le_iSup₂_of_le ε hε le_rfl
  exact_mod_cast (ENNReal.toReal_mono hx.ne he)

lemma truncated_memLp (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0}
    (hK : KernelRegularity K B) (p : Exponent) {f : Point d → ℂ}
    (hf : MemLp f p.val volume)
    (hfin : ∀ᵐ x ∂volume, maximalTruncation K f x < ∞)
    (hm : MemLp (fun x => (maximalTruncation K f x).toReal) p.val volume)
    {ε : ℝ} (hε : 0 < ε) : MemLp (truncated K f ε) p.val volume := by
  apply hm.mono' (MaximalTruncation.lp_truncated_continuous hd hK p hf hε).aestronglyMeasurable
  filter_upwards [hfin] with x hx
  exact norm_truncated_le hε x hx

/-- On test functions the limit is the given extension, by agreement on L²∩Lp. -/
lemma smooth_tendsto (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0} {T : Operator d}
    (hK : KernelRegularity K B) (hT : SmoothL2Action T K)
    (p : Exponent) (R : StrongOperator d p) (hR : Agrees T p R)
    (φ : MaximalTruncationData.Tests d)
    (hφ : MemLp (φ : Point d → ℂ) p.val volume) :
    ∀ᵐ x ∂volume, Tendsto (fun ε => truncated K φ ε x) (𝓝[>] 0)
      (𝓝 ((R (hφ.toLp φ) : Point d → ℂ) x)) := by
  have hφ2 : MemLp (φ : Point d → ℂ) 2 volume :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have he := (hR φ hφ hφ2).trans (hT φ)
  filter_upwards [he] with x hx
  rw [hx]
  exact (MaximalTruncation.smooth_principal_value d hd K B hK φ x).2

/-- An elementary three-error argument. Uniform control is only needed at
positive radii, and the result retains the full right-neighborhood filter. -/
lemma tendsto_of_uniform_approximation
    (F : ℝ → ℂ) (G : ℕ → ℝ → ℂ) (v : ℕ → ℂ) (b : ℕ → ℝ) (l : ℂ)
    (hb : Tendsto b atTop (𝓝 0)) (hv : Tendsto v atTop (𝓝 l))
    (hG : ∀ n, Tendsto (G n) (𝓝[>] 0) (𝓝 (v n)))
    (hbound : ∀ n ε, 0 < ε → ‖F ε - G n ε‖ ≤ b n) :
    Tendsto F (𝓝[>] 0) (𝓝 l) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hb' : ∀ᶠ n in atTop, b n < ε / 3 := hb.eventually (gt_mem_nhds (by linarith))
  have hv' : ∀ᶠ n in atTop, dist (v n) l < ε / 3 :=
    (Metric.tendsto_nhds.mp hv) _ (by linarith)
  obtain ⟨n, hn, hnv⟩ := (hb'.and hv').exists
  have hnG := (Metric.tendsto_nhds.mp (hG n)) (ε / 3) (by linarith)
  filter_upwards [hnG, self_mem_nhdsWithin] with r hr hr0
  calc
    dist (F r) l ≤ dist (F r) (G n r) + dist (G n r) (v n) + dist (v n) l :=
      calc
        _ ≤ dist (F r) (v n) + dist (v n) l := dist_triangle _ _ _
        _ ≤ _ := by gcongr; exact dist_triangle _ _ _
    _ < ε := by
      have h := hbound n r hr0
      simp only [dist_eq_norm] at ⊢
      rw [dist_eq_norm] at hr hnv
      linarith


/-- Smooth density and the maximal bound give convergence at almost every
point along arbitrary positive real radii, directly to the compatible action. -/
lemma ae_tendsto (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0} {T : Operator d}
    (hK : KernelRegularity K B) (hT : SmoothL2Action T K)
    (p : Exponent) (R : StrongOperator d p) (hR : Agrees T p R)
    (f : Point d → ℂ) (hf : MemLp f p.val volume) :
    ∀ᵐ x ∂volume, Tendsto (fun ε => truncated K f ε x) (𝓝[>] 0)
      (𝓝 ((R (hf.toLp f) : Point d → ℂ) x)) := by
  have hp0 : p.val ≠ 0 := ne_of_gt (zero_lt_one.trans p.one_lt)
  obtain ⟨C, hC⟩ := MaximalTruncation.maximal_bound
  obtain ⟨v, hv, hvl⟩ := mem_closure_iff_seq_limit.mp
    (Lp.dense_hasCompactSupport_contDiff (F := ℂ) (μ := (volume : Measure (Point d)))
      (p := p.val) p.lt_top.ne (hf.toLp f))
  choose g hg hgc hgs using hv
  let φ : ℕ → MaximalTruncationData.Tests d := fun n =>
    { toFun := g n
      contDiff' := hgs n
      hasCompactSupport' := hgc n
      tsupport_subset' := subset_univ _ }
  have hφ (n : ℕ) : MemLp (φ n : Point d → ℂ) p.val volume :=
    (φ n).continuous.memLp_of_hasCompactSupport (φ n).hasCompactSupport
  have hvφ (n : ℕ) : (hφ n).toLp (φ n) = v n := by
    apply Lp.ext
    exact (hφ n).coeFn_toLp.trans (hg n).symm
  have hφlim : Tendsto (fun n => (hφ n).toLp (φ n)) atTop (𝓝 (hf.toLp f)) := by
    simpa only [hvφ] using hvl
  have hdiff : Tendsto (fun n => eLpNorm (f - (φ n : Point d → ℂ)) p.val volume) atTop (𝓝 0) := by
    simp_rw [eLpNorm_sub_comm f]
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => (φ n : Point d → ℂ)) hφ f hf).mp hφlim
  let m : ℕ → Point d → ℝ := fun n x => (maximalTruncation K (f - (φ n : Point d → ℂ)) x).toReal
  have hmax (n : ℕ) := hC d hd K B T hK hT p (f - (φ n : Point d → ℂ)) (hf.sub (hφ n))
  have hmn : Tendsto (fun n => eLpNorm (m n) p.val volume) atTop (𝓝 0) := by
    have ht : Tendsto (fun n => (C d K B ‖T‖₊ p : ℝ≥0∞) *
        eLpNorm (f - (φ n : Point d → ℂ)) p.val volume) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hdiff (Or.inr ENNReal.coe_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => (zero_le : (0 : ℝ≥0∞) ≤ _)) (fun n => (hmax n).2.2.2)
  have hmm : TendstoInMeasure volume m atTop 0 :=
    tendstoInMeasure_of_tendsto_eLpNorm hp0 (by simpa using hmn)
  obtain ⟨a, ha, hma⟩ := hmm.exists_seq_tendsto_ae
  have hRlim := R.continuous.tendsto (hf.toLp f) |>.comp hφlim
  obtain ⟨b, hb, hRb⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hRlim.comp ha.tendsto_atTop)).exists_seq_tendsto_ae
  have hfinite : ∀ᵐ x ∂volume, ∀ n,
      maximalTruncation K (f - (φ (a (b n)) : Point d → ℂ)) x < ∞ :=
    ae_all_iff.mpr (fun n => (hmax (a (b n))).2.1)
  have hsmooth : ∀ᵐ x ∂volume, ∀ n,
      Tendsto (fun ε => truncated K (φ (a (b n))) ε x) (𝓝[>] 0)
        (𝓝 ((R ((hφ (a (b n))).toLp (φ (a (b n)))) : Point d → ℂ) x)) :=
    ae_all_iff.mpr (fun n => smooth_tendsto hd hK hT p R hR _ _)
  filter_upwards [hma, hRb, hfinite, hsmooth] with x hmx hRx hfx hsx
  apply tendsto_of_uniform_approximation
    (fun ε => truncated K f ε x)
    (fun n ε => truncated K (φ (a (b n))) ε x)
    (fun n => (R ((hφ (a (b n))).toLp (φ (a (b n)))) : Point d → ℂ) x)
    (fun n => m (a (b n)) x) _ (hmx.comp hb.tendsto_atTop) hRx hsx
  intro n ε hε
  rw [← truncated_sub hd hK p hf (hφ (a (b n))) hε x]
  exact norm_truncated_le hε x (hfx n)

/-- Dominated convergence in the finite Lp norm, for the right-neighborhood
filter. The majorant is an actual real Lp function. -/
lemma eLpNorm_tendsto_zero_of_dominated
    (p : Exponent) (F : ℝ → Point d → ℂ) (b : Point d → ℝ)
    (hb : MemLp b p.val volume)
    (hF : ∀ ε, 0 < ε → AEStronglyMeasurable (F ε) volume)
    (hbound : ∀ ε, 0 < ε → ∀ᵐ x ∂volume, ‖F ε x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun ε => F ε x) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => eLpNorm (F ε) p.val volume) (𝓝[>] 0) (𝓝 0) := by
  have hp0 : p.val ≠ 0 := ne_of_gt (zero_lt_one.trans p.one_lt)
  have hpr : 0 < p.val.toReal := ENNReal.toReal_pos hp0 p.lt_top.ne
  have hl : Tendsto (fun ε => ∫⁻ x, ‖F ε x‖ₑ ^ p.val.toReal) (𝓝[>] 0) (𝓝 0) := by
    have ht := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := (volume : Measure (Point d))) (l := 𝓝[>] (0 : ℝ))
      (F := fun ε x => ‖F ε x‖ₑ ^ p.val.toReal) (f := fun _ => 0)
      (fun x => ‖b x‖ₑ ^ p.val.toReal)
    simp only [lintegral_zero] at ht
    apply ht
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hF ε hε).enorm.pow_const _
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [hbound ε hε] with x hx
      apply ENNReal.rpow_le_rpow _ hpr.le
      simpa only [enorm_le_iff_norm_le, Real.norm_eq_abs] using hx.trans (le_abs_self (b x))
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 p.lt_top.ne hb.eLpNorm_lt_top).ne
    · filter_upwards [hlim] with x hx
      simpa only [enorm_zero, ENNReal.zero_rpow_of_pos hpr] using
        hx.enorm.ennrpow_const p.val.toReal
  have ht := hl.ennrpow_const (1 / p.val.toReal)
  simp only [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpr)] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 p.lt_top.ne (hF ε hε)).symm

theorem convergence : Specs.P102.U2.PrincipalValues.convergence := by
  intro d hd K B T hK hT p R hR f hf
  obtain ⟨C, hC⟩ := MaximalTruncation.maximal_bound
  have hmax := hC d hd K B T hK hT p f hf
  have hmem := fun ε hε => truncated_memLp hd hK p hf hmax.2.1 hmax.2.2.1 (ε := ε) hε
  have hae := ae_tendsto hd hK hT p R hR f hf
  refine ⟨hmem, hae, ?_⟩
  let r : Point d → ℂ := R (hf.toLp f)
  apply eLpNorm_tendsto_zero_of_dominated p
    (fun ε x => truncated K f ε x - r x)
    (fun x => (maximalTruncation K f x).toReal + ‖r x‖)
    (hmax.2.2.1.add (Lp.memLp (R (hf.toLp f))).norm)
  · intro ε hε
    exact ((hmem ε hε).sub (Lp.memLp _)).aestronglyMeasurable
  · intro ε hε
    filter_upwards [hmax.2.1] with x hx
    exact (norm_sub_le _ _).trans (add_le_add (norm_truncated_le hε x hx) le_rfl)
  · filter_upwards [hae] with x hx
    simpa only [r, sub_self] using hx.sub_const (r x)

/-- Complete maximal-truncation and principal-value theorem. -/
theorem full_theorem : Specs.P102.U2.PrincipalValues.full_theorem := by
  obtain ⟨C, hC⟩ := MaximalTruncation.maximal_bound
  obtain ⟨D, hD⟩ := MaximalTruncation.kernel_representation
  obtain ⟨C₁, L, hL⟩ := CZLp.full_extension
  refine ⟨C, ?_⟩
  intro d hd K B T hK hT
  obtain ⟨_, S, R, _, _, _, _, _, _, _, hRA, hPair, _⟩ :=
    hL d hd T K (D d * B) (hD d hd K B T hK hT).1
  exact ⟨R, hRA, hPair, fun p => convergence d hd K B T hK hT p (R p) (hRA p),
    fun p f hf => hC d hd K B T hK hT p f hf,
    fun p f hf => MaximalTruncation.truncation_realization d hd K B hK p f hf⟩

end P102.U2.PrincipalValues
