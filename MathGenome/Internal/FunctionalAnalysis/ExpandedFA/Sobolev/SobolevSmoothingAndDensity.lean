import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.WeakDerivativeSpaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.SmoothApproximateIdentities
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.SmoothPartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

noncomputable section
open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal Topology

namespace ExpandedFA.Sobolev.Smoothing
open ExpandedFA.Distributions SmoothApproximateIdentitiesSpec

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A normalized bump supplies a mollifier in every dimension, including zero. -/
theorem exists_mollifier (d : ℕ) : ∃ ρ : Domain d → ℝ, IsMollifier ρ := by
  let b : ContDiffBump (0 : Domain d) := ⟨1, 2, by norm_num, by norm_num⟩
  exact ⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed,
    b.nonneg_normed, b.integral_normed⟩

@[simp] theorem zeroExtend_apply_inside (u : DomainLp 𝕜 Ω p)
    {x : Domain d} (hx : x ∈ Ω) : zeroExtend u x = u x :=
  Set.indicator_of_mem hx _

@[simp] theorem zeroExtend_apply_outside (u : DomainLp 𝕜 Ω p)
    {x : Domain d} (hx : x ∉ Ω) : zeroExtend u x = 0 :=
  Set.indicator_of_notMem hx _

theorem zeroExtend_memLp (u : DomainLp 𝕜 Ω p) :
    MemLp (zeroExtend u) p volume :=
  (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).mpr (Lp.memLp u)

theorem zeroExtend_eLpNorm (u : DomainLp 𝕜 Ω p) :
    eLpNorm (zeroExtend u) p volume = ENNReal.ofReal ‖u‖ := by
  rw [zeroExtend, eLpNorm_indicator_eq_eLpNorm_restrict
    Ω.isOpen.measurableSet.nullMeasurableSet, ofReal_norm, Lp.enorm_def]

theorem zeroExtend_ae (u : DomainLp 𝕜 Ω p) :
    zeroExtend u =ᵐ[volume.restrict (Ω : Set (Domain d))] u :=
  (ae_restrict_mem Ω.isOpen.measurableSet).mono (fun _ hx => zeroExtend_apply_inside u hx)

theorem zeroExtend_locallyIntegrable (u : DomainLp 𝕜 Ω p) :
    LocallyIntegrable (zeroExtend u) volume :=
  (zeroExtend_memLp u).locallyIntegrable Fact.out

theorem regularize_contDiff (ρ : Domain d → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (u : DomainLp 𝕜 Ω p) :
    ContDiff ℝ (⊤ : ℕ∞) (regularize ρ ε u) := by
  have hk := scaledKernel_properties ρ hρ ε hε
  exact hk.2.1.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    hk.1 (zeroExtend_locallyIntegrable u)

theorem regularize_memLp (ρ : Domain d → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (u : DomainLp 𝕜 Ω p) :
    MemLp (regularize ρ ε u) p volume :=
  mollify_memLp ρ hρ p Fact.out _ (zeroExtend_memLp u) hε

/-- Whole-space approximation of the zero extension is useful even though its
distribution derivatives can have boundary terms. No derivative claim is used. -/
theorem regularize_zeroExtend_tendsto (hp : p ≠ ∞)
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ) (u : DomainLp 𝕜 Ω p) :
    Tendsto (fun ε => eLpNorm (regularize ρ ε u - zeroExtend u) p volume)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  (mollify_lp ρ hρ p Fact.out hp _ (zeroExtend_memLp u)).2

/-- Restricting the error gives convergence on any measurable subset of Ω,
without compactness. This lemma is applied separately to every weak derivative;
commutation with differentiation is a further obligation. -/
theorem regularize_restrict_tendsto (hp : p ≠ ∞)
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ) (u : DomainLp 𝕜 Ω p)
    {K : Set (Domain d)} (hK : MeasurableSet K) (hKΩ : K ⊆ Ω) :
    Tendsto (fun ε => eLpNorm (regularize ρ ε u - (u : Domain d → 𝕜)) p (volume.restrict K))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have heq : zeroExtend u =ᵐ[volume.restrict K] u :=
    (ae_restrict_mem hK).mono (fun _ hx => zeroExtend_apply_inside u (hKΩ hx))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (regularize_zeroExtend_tendsto hp ρ hρ u)
  · intro ε
    exact bot_le
  · intro ε
    change eLpNorm (regularize ρ ε u - (u : Domain d → 𝕜)) p (volume.restrict K) ≤ _
    rw [← eLpNorm_congr_ae ((EventuallyEq.rfl : regularize ρ ε u =ᵐ[volume.restrict K]
      regularize ρ ε u).sub heq)]
    exact eLpNorm_restrict_le _ _ _ _

theorem derivative_regularizations_tendsto {m : ℕ} (hp : p ≠ ∞)
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ) (u : SobolevSpace 𝕜 d Ω m p)
    {K : Set (Domain d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (α : DerivativeIndex d m) :
    Tendsto (fun ε => eLpNorm (regularize ρ ε (u.val α) - (u.val α : Domain d → 𝕜))
      p (volume.restrict K)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  regularize_restrict_tendsto hp ρ hρ _ hK.measurableSet hKΩ

theorem smooth_regularization :
    Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.SmoothRegularization := by
  intro 𝕜 _ d Ω p _ ρ hρ ε hε u
  exact regularize_contDiff ρ hρ hε u

theorem scaledKernel_eLpNorm_one (ρ : Domain d → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) : eLpNorm (ScaledKernelValue ρ ε) 1 volume = 1 := by
  have hk := scaledKernel_properties ρ hρ ε hε
  have hi : Integrable (ScaledKernelValue ρ ε) volume :=
    hk.1.continuous.integrable_of_hasCompactSupport hk.2.1
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable]
  simp_rw [← ofReal_norm, Real.norm_of_nonneg (hk.2.2.1 _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hk.2.2.1),
    hk.2.2.2, ENNReal.ofReal_one]

/-- A pointwise, sharp L∞ bound. The convolution is defined at every point,
even though the input belongs to an a.e. quotient space. -/
theorem regularize_norm_le (ρ : Domain d → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (u : DomainLp 𝕜 Ω ∞) (x : Domain d) :
    ‖regularize ρ ε u x‖ ≤ ‖u‖ := by
  have hk := scaledKernel_properties ρ hρ ε hε
  have hb := enorm_convolution_le (p := 1) (q := ∞)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜)
    hk.1.continuous.aestronglyMeasurable (zeroExtend_memLp u).aestronglyMeasurable x
  have he : ‖regularize ρ ε u x‖ₑ ≤ ENNReal.ofReal ‖u‖ := by
    calc
      _ ≤ ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜)‖ₑ *
          ENNReal.ofReal ‖u‖ := by
        simpa only [regularize, MollifyValue, scaledKernel_eLpNorm_one ρ hρ hε,
          zeroExtend_eLpNorm, mul_one] using hb
      _ ≤ 1 * ENNReal.ofReal ‖u‖ :=
        by
          gcongr
          exact ContinuousLinearMap.opENorm_lsmul_le
      _ = _ := one_mul _
  rw [← ofReal_norm] at he
  exact ENNReal.ofReal_le_ofReal_iff (norm_nonneg _ ) |>.mp he

/-- Local finite-exponent convergence for a globally essentially bounded input.
The auxiliary truncation is on a large ball; it never presumes that L∞ embeds
in a finite Lr space on the whole, potentially infinite-measure domain. -/
theorem mollify_local_tendsto (ρ : Domain d → ℝ) (hρ : IsMollifier ρ)
    (f : Domain d → 𝕜) (hf : MemLp f ∞ volume) {K : Set (Domain d)}
    (hK : IsCompact K) (r : ℝ≥0∞) (hr : 1 ≤ r) (hrt : r ≠ ∞) :
    Tendsto (fun ε => eLpNorm (MollifyValue ρ ε f - f) r (volume.restrict K))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let B : Set (Domain d) := Metric.closedBall 0 (R + 1)
  have hB : MeasurableSet B := measurableSet_closedBall
  have hBfin : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Domain d) (R + 1)).measure_lt_top.ne
  let := hBfin
  let fB := B.indicator f
  have hfB : MemLp fB r volume :=
    (memLp_indicator_iff_restrict hB.nullMeasurableSet).mpr
      ((hf.restrict B).mono_exponent le_top)
  have hKB : K ⊆ B := by
    intro x hx
    exact mem_closedBall_zero_iff.mpr ((hbound x hx).trans (by linarith))
  have ht : Tendsto (fun ε => eLpNorm (MollifyValue ρ ε fB - fB)
      r (volume.restrict K)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (mollify_lp ρ hρ r hr hrt fB hfB).2
    · intro ε
      exact bot_le
    · intro ε
      exact eLpNorm_restrict_le _ _ _ _
  apply ht.congr'
  filter_upwards [scaledKernel_support_eventually ρ hρ.2.1 (by norm_num : (0 : ℝ) < 1)]
    with ε hs
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  have heq : MollifyValue ρ ε fB x = MollifyValue ρ ε f x := by
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : ScaledKernelValue ρ ε y = 0
    · simp [hy]
    · have hnorm : ‖x - y‖ ≤ R + 1 := by
        have hyb := mem_ball_zero_iff.mp (hs hy)
        exact (norm_sub_le x y).trans (add_le_add (hbound x hx) hyb.le)
      rw [show fB (x-y) = f (x-y) from
        Set.indicator_of_mem (mem_closedBall_zero_iff.mpr hnorm) f]
  change MollifyValue ρ ε fB x - fB x = MollifyValue ρ ε f x - f x
  rw [heq]
  exact congrArg (_ - ·) (Set.indicator_of_mem (hKB hx) f)

theorem regularize_local_finite_tendsto (ρ : Domain d → ℝ) (hρ : IsMollifier ρ)
    (u : DomainLp 𝕜 Ω ∞) {K : Set (Domain d)} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (r : ℝ≥0∞) (hr : 1 ≤ r) (hrt : r ≠ ∞) :
    Tendsto (fun ε => eLpNorm (regularize ρ ε u - (u : Domain d → 𝕜))
      r (volume.restrict K)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht := mollify_local_tendsto ρ hρ _ (zeroExtend_memLp u) hK r hr hrt
  apply ht.congr'
  apply Eventually.of_forall
  intro ε
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  simp [regularize, zeroExtend_apply_inside u (hKΩ hx)]

/-- Uniform essential bounds upgrade L1 convergence to convergence against
every integrable scalar test. This elementary density argument avoids any
identification of the dual of L∞. -/
theorem integral_mul_tendsto_of_L1_of_bound {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} {l : Filter ι} (F : ι → X → 𝕜) (f : X → 𝕜)
    (M : ℝ) (hM : 0 ≤ M) (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (hf : AEStronglyMeasurable f μ)
    (hFb : ∀ i, ∀ᵐ x ∂μ, ‖F i x‖ ≤ M) (hfb : ∀ᵐ x ∂μ, ‖f x‖ ≤ M)
    (hi : ∀ i, Integrable (F i - f) μ)
    (ht : Tendsto (fun i => eLpNorm (F i - f) 1 μ) l (𝓝 0))
    (g : X → 𝕜) (hg : Integrable g μ) :
    Tendsto (fun i => ∫ x, g x * F i x ∂μ) l (𝓝 (∫ x, g x * f x ∂μ)) := by
  have hnorm : Tendsto (fun i => ∫ x, ‖F i x - f x‖ ∂μ) l (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
    simp only [ENNReal.toReal_zero, Function.comp_def] at h
    convert h using 1
    funext i
    rw [eLpNorm_one_eq_lintegral_enorm ((hF i).sub hf),
      ← integral_norm_eq_lintegral_enorm ((hF i).sub hf)]
    rfl
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let δ := η / (4 * (M + 1))
  have hδ : 0 < δ := div_pos hη (by positivity)
  obtain ⟨s, hs, hsmem⟩ := (memLp_one_iff_integrable.mpr hg).exists_simpleFunc_eLpNorm_sub_lt
    ENNReal.one_ne_top (ENNReal.ofReal_pos.mpr hδ).ne'
  have hgs := hg.sub (memLp_one_iff_integrable.mp hsmem)
  have htail : (∫ x, ‖g x - s x‖ ∂μ) < δ := by
    change (∫ x, ‖(g - ⇑s) x‖ ∂μ) < δ
    rw [integral_norm_eq_lintegral_enorm hgs.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm hgs.aestronglyMeasurable]
    have h := ENNReal.toReal_lt_toReal (ne_of_lt (hs.trans ENNReal.ofReal_lt_top))
      ENNReal.ofReal_ne_top |>.mpr hs
    simpa only [ENNReal.toReal_ofReal hδ.le] using h
  obtain ⟨C₀, hC₀⟩ := s.exists_forall_norm_le
  let C := |C₀| + 1
  have hC : 0 ≤ C := by positivity
  have hsC (x : X) : ‖s x‖ ≤ C := (hC₀ x).trans (by dsimp [C]; linarith [le_abs_self C₀])
  have hβ : 0 < η / (2 * (C + 1)) := div_pos hη (by positivity)
  filter_upwards [hnorm.eventually (gt_mem_nhds hβ)] with i hiη
  have herror : ∀ᵐ x ∂μ, ‖F i x - f x‖ ≤ 2 * M := by
    filter_upwards [hFb i, hfb] with x hFx hfx
    exact (norm_sub_le _ _).trans (by linarith)
  have hbound : ‖∫ x, g x * (F i x - f x) ∂μ‖ ≤
      2 * M * (∫ x, ‖g x - s x‖ ∂μ) + C * (∫ x, ‖F i x - f x‖ ∂μ) := by
    have hb := norm_integral_le_of_norm_le
      ((hgs.norm.const_mul (2 * M)).add ((hi i).norm.const_mul C))
      (show ∀ᵐ x ∂μ, ‖g x * (F i x - f x)‖ ≤
          2 * M * ‖g x - s x‖ + C * ‖F i x - f x‖ from by
        filter_upwards [herror] with x hx
        calc
          _ = ‖(g x - s x) * (F i x - f x) + s x * (F i x - f x)‖ := by congr 1; ring
          _ ≤ ‖(g x - s x) * (F i x - f x)‖ + ‖s x * (F i x - f x)‖ := norm_add_le _ _
          _ ≤ 2 * M * ‖g x - s x‖ + C * ‖F i x - f x‖ := by
            simp only [norm_mul]
            nlinarith [norm_nonneg (g x - s x), norm_nonneg (F i x - f x), hsC x])
    change ‖∫ x, g x * (F i x - f x) ∂μ‖ ≤
      ∫ x, 2 * M * ‖(g - ⇑s) x‖ + C * ‖(F i - f) x‖ ∂μ at hb
    rw [integral_add (hgs.norm.const_mul (2 * M)) ((hi i).norm.const_mul C),
      integral_const_mul, integral_const_mul] at hb
    exact hb
  have hsmall : 2 * M * (∫ x, ‖g x - s x‖ ∂μ) +
      C * (∫ x, ‖F i x - f x‖ ∂μ) < η := by
    have hδeq : 4 * (M + 1) * δ = η := mul_div_cancel₀ η (by positivity)
    have hβeq : 2 * (C + 1) * (η / (2 * (C + 1))) = η :=
      mul_div_cancel₀ η (by positivity)
    have hA : 0 ≤ ∫ x, ‖g x - s x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
    have hB : 0 ≤ ∫ x, ‖F i x - f x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
    nlinarith
  rw [dist_eq_norm, ← integral_sub (hg.mul_bdd (hF i) (hFb i)) (hg.mul_bdd hf hfb)]
  simpa only [← mul_sub] using hbound.trans_lt hsmall

theorem domainLp_top_ae_norm_le (u : DomainLp 𝕜 Ω ∞) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))), ‖u x‖ ≤ ‖u‖ := by
  have he : eLpNormEssSup u (volume.restrict (Ω : Set (Domain d))) =
      ENNReal.ofReal ‖u‖ := by
    rw [ofReal_norm, Lp.enorm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable u)]
  filter_upwards [enorm_ae_le_eLpNormEssSup u
    (volume.restrict (Ω : Set (Domain d)))] with x hx
  rw [he, ← ofReal_norm] at hx
  exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp hx

theorem regularize_weakStar_tendsto (ρ : Domain d → ℝ) (hρ : IsMollifier ρ)
    (u : DomainLp 𝕜 Ω ∞) {K : Set (Domain d)} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (g : Domain d → 𝕜) (hg : MemLp g 1 (volume.restrict K)) :
    Tendsto (fun ε => ∫ x in K, g x * regularize ρ ε u x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in K, g x * u x)) := by
  let μ := volume.restrict K
  have hμ : μ ≤ volume.restrict (Ω : Set (Domain d)) := Measure.restrict_mono hKΩ le_rfl
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hf : AEStronglyMeasurable u μ := (Lp.aestronglyMeasurable u).mono_measure hμ
  have hfb : ∀ᵐ x ∂μ, ‖u x‖ ≤ ‖u‖ :=
    (domainLp_top_ae_norm_le u).filter_mono (ae_mono hμ)
  let F : ℝ → Domain d → 𝕜 := fun ε => if 0 < ε then regularize ρ ε u else u
  have hF (ε : ℝ) : AEStronglyMeasurable (F ε) μ := by
    dsimp only [F]
    split_ifs with hε
    · exact (regularize_contDiff ρ hρ hε u).continuous.aestronglyMeasurable
    · exact hf
  have hFb (ε : ℝ) : ∀ᵐ x ∂μ, ‖F ε x‖ ≤ ‖u‖ := by
    dsimp only [F]
    split_ifs with hε
    · exact Eventually.of_forall (regularize_norm_le ρ hρ hε u)
    · exact hfb
  have hi (ε : ℝ) : Integrable (F ε - (u : Domain d → 𝕜)) μ := by
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound ((hF ε).sub hf) (2 * ‖u‖)
    filter_upwards [hFb ε, hfb] with x hx hux
    exact (norm_sub_le _ _).trans (by linarith)
  have ht : Tendsto (fun ε => eLpNorm (F ε - (u : Domain d → 𝕜)) 1 μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply (regularize_local_finite_tendsto ρ hρ u hK hKΩ 1 le_rfl ENNReal.one_ne_top).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp [F, Set.mem_Ioi.mp hε, μ]
  have hw := integral_mul_tendsto_of_L1_of_bound F (u : Domain d → 𝕜)
    ‖u‖ (norm_nonneg _) hF hf hFb hfb hi ht g (memLp_one_iff_integrable.mp hg)
  apply hw.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp [F, Set.mem_Ioi.mp hε, μ]

lemma testPartial_single_comm (i j : Fin d) (φ : Tests 𝕜 Ω) :
    testPartialCLM [i] (testPartialCLM [j] φ) =
      testPartialCLM [j] (testPartialCLM [i] φ) := by
  ext x
  simp only [testPartial_single_apply]
  have he (j : Fin d) : (⇑(testPartialCLM [j] φ)) =
      fun y => fderiv ℝ φ y (coordinateVector j) := funext (testPartial_single_apply j φ)
  rw [he j, he i]
  rw [fderiv_clm_apply ((φ.contDiff.fderiv_right (m := 1) (by simp)).differentiable (by simp) x)
      (differentiableAt_const _),
    fderiv_clm_apply ((φ.contDiff.fderiv_right (m := 1) (by simp)).differentiable (by simp) x)
      (differentiableAt_const _)]
  simpa using φ.contDiff.contDiffAt.isSymmSndFDerivAt (by simp) (coordinateVector i) (coordinateVector j)

lemma testPartial_single_word (i : Fin d) (w : List (Fin d)) (φ : Tests 𝕜 Ω) :
    testPartialCLM [i] (testPartialCLM w φ) =
      testPartialCLM w (testPartialCLM [i] φ) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change testPartialCLM [i] (testPartialCLM [j] (testPartialCLM w φ)) =
      testPartialCLM [j] (testPartialCLM w (testPartialCLM [i] φ))
    rw [testPartial_single_comm, ih]

lemma testPartial_reverse (w : List (Fin d)) (φ : Tests 𝕜 Ω) :
    testPartialCLM w.reverse φ = testPartialCLM w φ := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [List.reverse_cons, testPartial_append, ← testPartial_single_word, ih]
    rfl

lemma testPartial_perm {w z : List (Fin d)} (h : w.Perm z) (φ : Tests 𝕜 Ω) :
    testPartialCLM w φ = testPartialCLM z φ := by
  induction h with
  | nil => rfl
  | cons i h ih =>
    change testPartialCLM [i] (testPartialCLM _ φ) = testPartialCLM [i] (testPartialCLM _ φ)
    rw [ih]
  | swap i j w =>
    exact testPartial_single_comm j i (testPartialCLM w φ)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

lemma word_count_sum (w : List (Fin d)) : (∑ i, w.count i) = w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.count_cons, beq_iff_eq, List.length_cons]
    rw [Finset.sum_add_distrib]
    simp [ih]

lemma canonical_word_perm (w : List (Fin d)) :
    (multiIndexWord (fun i => w.count i)).Perm w := by
  apply List.perm_iff_count.mpr
  intro i
  simp

lemma distributionDerivative_perm {w z : List (Fin d)} (h : w.Perm z)
    (u : ScalarDistribution 𝕜 Ω) :
    distributionDerivative 𝕜 d Ω w u = distributionDerivative 𝕜 d Ω z u := by
  ext φ
  simp only [distributionDerivative_apply, h.length_eq, testPartial_perm h]

variable {m : ℕ}
def wordIndex (w : List (Fin d)) (h : w.length ≤ m) : DerivativeIndex d m :=
  boundedIndex (fun i => w.count i) (by simpa only [word_count_sum] using h)

def wordLp (u : SobolevSpace 𝕜 d Ω m p) (w : List (Fin d)) : DomainLp 𝕜 Ω p :=
  if h : w.length ≤ m then u.val (wordIndex w h) else 0

lemma wordLp_distribution (u : SobolevSpace 𝕜 d Ω m p)
    (w : List (Fin d)) (h : w.length ≤ m) :
    lpDistribution (wordLp u w) = distributionDerivative 𝕜 d Ω w (lpDistribution (underlyingLp u)) := by
  rw [wordLp, dite_eq_left h]
  exact (u.property (wordIndex w h)).trans
    (distributionDerivative_perm (canonical_word_perm w) _)


def testCoefficient (η : Tests 𝕜 Ω) : SmoothCoefficient 𝕜 Ω :=
  ⟨η, η.contDiff.contDiffOn⟩

lemma testCoefficient_partial (i : Fin d) (η : Tests 𝕜 Ω) :
    testCoefficient (testPartialCLM [i] η) = coefficientPartial i (testCoefficient η) := by
  apply Subtype.ext
  exact funext (testPartial_single_apply i η)

def cutoffLp (η : Tests 𝕜 Ω) (v : DomainLp 𝕜 Ω p) : DomainLp 𝕜 Ω p :=
  (show MemLp (fun x => η x * v x) p (volume.restrict (Ω : Set (Domain d))) from
    (η.continuous.memLp_of_hasCompactSupport (p := ∞) η.hasCompactSupport).mul (Lp.memLp v)).toLp _

lemma cutoffLp_coe (η : Tests 𝕜 Ω) (v : DomainLp 𝕜 Ω p) :
    cutoffLp η v =ᵐ[volume.restrict (Ω : Set (Domain d))] fun x => η x * v x :=
  MemLp.coeFn_toLp _

lemma cutoffLp_distribution (η : Tests 𝕜 Ω) (v : DomainLp 𝕜 Ω p) :
    lpDistribution (cutoffLp η v) = multiplyDistribution (testCoefficient η) (lpDistribution v) := by
  ext φ
  simp only [lpDistribution_apply, multiplyDistribution_apply]
  apply integral_congr_ae
  filter_upwards [cutoffLp_coe η v] with x hx
  change φ x * cutoffLp η v x = (η x * φ x) * v x
  rw [hx]
  ring

lemma distributionDerivative_append (w z : List (Fin d)) (v : ScalarDistribution 𝕜 Ω) :
    distributionDerivative 𝕜 d Ω (w ++ z) v =
      distributionDerivative 𝕜 d Ω z (distributionDerivative 𝕜 d Ω w v) := by
  ext φ
  simp only [distributionDerivative_apply, List.length_append, pow_add, testPartial_append]
  ring

lemma distributionDerivative_single (i : Fin d) (v : ScalarDistribution 𝕜 Ω) :
    distributionDerivative 𝕜 d Ω [i] v = -v.comp (testPartialCLM [i]) := by
  ext φ
  simp [distributionDerivative_apply]

-- Recursively expanded Leibniz jet; only the distributional word needs a length bound.
def cutoffJet (u : SobolevSpace 𝕜 d Ω m p) :
    List (Fin d) → Tests 𝕜 Ω → List (Fin d) → DomainLp 𝕜 Ω p
  | [], η, z => cutoffLp η (wordLp u z)
  | i :: w, η, z => cutoffJet u w (testPartialCLM [i] η) z + cutoffJet u w η (z ++ [i])

lemma cutoffJet_distribution (u : SobolevSpace 𝕜 d Ω m p) (w : List (Fin d))
    (η : Tests 𝕜 Ω) (z : List (Fin d)) (h : w.length + z.length ≤ m) :
    lpDistribution (cutoffJet u w η z) = distributionDerivative 𝕜 d Ω w
      (multiplyDistribution (testCoefficient η)
        (distributionDerivative 𝕜 d Ω z (lpDistribution (underlyingLp u)))) := by
  induction w generalizing η z with
  | nil =>
    simp only [cutoffJet, distributionDerivative_nil, cutoffLp_distribution]
    rw [wordLp_distribution u z (by simpa using h)]
  | cons i w ih =>
    change lpDistributionLM (_ + _) = _
    rw [map_add]
    change lpDistribution (cutoffJet u w (testPartialCLM [i] η) z) +
      lpDistribution (cutoffJet u w η (z ++ [i])) = _
    rw [ih _ z (by simp only [List.length_cons] at h; omega),
      ih η (z ++ [i]) (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at h; omega)]
    rw [distributionDerivative_cons, distribution_leibniz, distributionDerivative_add,
      ← testCoefficient_partial, ← distributionDerivative_single,
      ← distributionDerivative_append]

@[simp] lemma wordLp_nil (u : SobolevSpace 𝕜 d Ω m p) : wordLp u [] = underlyingLp u := by
  apply lpDistribution_injective
  simpa using wordLp_distribution u [] (by simp)

@[simp] lemma multiIndexWord_zeroIndex : multiIndexWord (natIndex (zeroIndex d m)) = [] := by
  apply List.length_eq_zero_iff.mp
  simp [natIndex, zeroIndex]

/-- Compact smooth multiplication preserves the complete arbitrary-order derivative graph. -/
def cutoffSobolev (η : Tests 𝕜 Ω) (u : SobolevSpace 𝕜 d Ω m p) : SobolevSpace 𝕜 d Ω m p :=
  ⟨WithLp.toLp 1 (fun α => cutoffJet u (multiIndexWord (natIndex α)) η []), by
    intro α
    change lpDistribution (cutoffJet u (multiIndexWord (natIndex α)) η []) =
      distributionDerivative 𝕜 d Ω (multiIndexWord (natIndex α))
        (lpDistribution (cutoffJet u (multiIndexWord (natIndex (zeroIndex d m))) η []))
    rw [multiIndexWord_zeroIndex]
    simp only [cutoffJet, wordLp_nil, cutoffLp_distribution]
    simpa only [distributionDerivative_nil] using
      cutoffJet_distribution u (multiIndexWord (natIndex α)) η []
        (by simpa [natIndex] using α.property)⟩

@[simp] lemma cutoffSobolev_underlying (η : Tests 𝕜 Ω) (u : SobolevSpace 𝕜 d Ω m p) :
    underlyingLp (cutoffSobolev η u) = cutoffLp η (underlyingLp u) := by
  change cutoffJet u (multiIndexWord (natIndex (zeroIndex d m))) η [] = _
  rw [multiIndexWord_zeroIndex]
  simp only [cutoffJet, wordLp_nil]

lemma cutoffSobolev_coe (η : Tests 𝕜 Ω) (u : SobolevSpace 𝕜 d Ω m p) :
    underlyingLp (cutoffSobolev η u) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => η x * underlyingLp u x := by
  rw [cutoffSobolev_underlying]
  exact cutoffLp_coe η _

lemma partialFunction_contDiff (w : List (Fin d)) (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (partialFunction w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

abbrev smoothJet (z : List (Fin d)) (f : Domain d → 𝕜) := partialFunction z.reverse f

def smoothMulTest (η : Tests 𝕜 Ω) (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Tests 𝕜 Ω :=
  ⟨fun x => η x * f x, η.contDiff.mul hf, η.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans η.tsupport_subset⟩

lemma smoothMulTest_partial (i : Fin d) (η : Tests 𝕜 Ω)
    (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    testPartialCLM [i] (smoothMulTest η f hf) =
      smoothMulTest (testPartialCLM [i] η) f hf +
        smoothMulTest η (partialFunction [i] f) (partialFunction_contDiff [i] f hf) := by
  ext x
  rw [testPartial_single_apply]
  change fderiv ℝ (fun y => η y * f y) x (coordinateVector i) = _
  rw [show (fun y => η y * f y) = (η : Domain d → 𝕜) * f from rfl,
    fderiv_mul (η.contDiff.differentiable (by simp) x) (hf.differentiable (by simp) x)]
  simp [smoothMulTest, partialFunction, testPartial_single_apply, mul_comm, add_comm]

lemma testToDomainLp_add (φ ψ : Tests 𝕜 Ω) :
    testToDomainLp (p := p) (φ + ψ) = testToDomainLp φ + testToDomainLp ψ := by
  apply Lp.ext
  filter_upwards [testToDomainLp_coe (p := p) (φ + ψ),
    Lp.coeFn_add (testToDomainLp (p := p) φ) (testToDomainLp (p := p) ψ),
    testToDomainLp_coe (p := p) φ, testToDomainLp_coe (p := p) ψ] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂]
  change φ x + ψ x = testToDomainLp (p := p) φ x + testToDomainLp (p := p) ψ x
  rw [h₃, h₄]

def cutoffError (u : SobolevSpace 𝕜 d Ω m p) (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (w : List (Fin d)) (η : Tests 𝕜 Ω) (z : List (Fin d)) : DomainLp 𝕜 Ω p :=
  testToDomainLp (testPartialCLM w.reverse
    (smoothMulTest η (smoothJet z f) (partialFunction_contDiff z.reverse f hf))) - cutoffJet u w η z

lemma cutoffError_cons (u : SobolevSpace 𝕜 d Ω m p) (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin d) (w : List (Fin d)) (η : Tests 𝕜 Ω) (z : List (Fin d)) :
    cutoffError u f hf (i :: w) η z = cutoffError u f hf w (testPartialCLM [i] η) z +
      cutoffError u f hf w η (z ++ [i]) := by
  have hjet : smoothJet (z ++ [i]) f = partialFunction [i] (smoothJet z f) := by
    simp only [smoothJet, List.reverse_append, List.reverse_singleton, List.singleton_append, partialFunction]
  simp only [cutoffError, List.reverse_cons, testPartial_append, smoothMulTest_partial,
    map_add, testToDomainLp_add, cutoffJet]
  have ht : smoothMulTest η (partialFunction [i] (smoothJet z f))
      (partialFunction_contDiff [i] (smoothJet z f) (partialFunction_contDiff z.reverse f hf)) =
      smoothMulTest η (smoothJet (z ++ [i]) f) (partialFunction_contDiff (z ++ [i]).reverse f hf) := by
    ext x
    exact congrArg (η x * ·) (congrFun hjet.symm x)
  rw [ht]
  abel

lemma cutoffError_nil_coe (u : SobolevSpace 𝕜 d Ω m p) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (η : Tests 𝕜 Ω) (z : List (Fin d)) :
    cutoffError u f hf [] η z =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => η x * (smoothJet z f x - wordLp u z x) := by
  unfold cutoffError
  simp only [List.reverse_nil, testPartialCLM, ContinuousLinearMap.id_apply, cutoffJet]
  filter_upwards [Lp.coeFn_sub
      (testToDomainLp (p := p) (smoothMulTest η (smoothJet z f) (partialFunction_contDiff z.reverse f hf)))
      (cutoffLp η (wordLp u z)),
    testToDomainLp_coe (p := p) (smoothMulTest η (smoothJet z f) (partialFunction_contDiff z.reverse f hf)),
    cutoffLp_coe η (wordLp u z)] with x hx h₁ h₂
  rw [hx]
  change testToDomainLp (p := p) (smoothMulTest η (smoothJet z f) _) x - cutoffLp η (wordLp u z) x = _
  rw [h₁, h₂]
  change η x * smoothJet z f x - η x * wordLp u z x = _
  ring

lemma eLpNorm_cutoff_localize (η : Tests 𝕜 Ω) (g : Domain d → 𝕜) (K : Set (Domain d))
    (hK : MeasurableSet K) (hs : tsupport η ⊆ K) (hKΩ : K ⊆ Ω) :
    eLpNorm (fun x => η x * g x) p (volume.restrict (Ω : Set (Domain d))) =
      eLpNorm (fun x => η x * g x) p (volume.restrict K) := by
  have heq : K.indicator (fun x => η x * g x) = fun x => η x * g x := by
    funext x
    by_cases hx : x ∈ K
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), zero_mul]
  rw [← heq, eLpNorm_indicator_eq_eLpNorm_restrict hK.nullMeasurableSet,
    Measure.restrict_restrict hK, inter_eq_left.mpr hKΩ]
  rw [heq]

lemma cutoffError_nil_enorm_le (u : SobolevSpace 𝕜 d Ω m p) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (η : Tests 𝕜 Ω) (z : List (Fin d))
    (K : Set (Domain d)) (hK : MeasurableSet K) (hs : tsupport η ⊆ K) (hKΩ : K ⊆ Ω) :
    ENNReal.ofReal ‖cutoffError u f hf [] η z‖ ≤ eLpNorm η ∞ (volume : Measure (Domain d)) *
      eLpNorm (fun x => smoothJet z f x - wordLp u z x) p (volume.restrict K) := by
  rw [ofReal_norm, Lp.enorm_def, eLpNorm_congr_ae (cutoffError_nil_coe u f hf η z),
    eLpNorm_cutoff_localize η _ K hK hs hKΩ]
  calc
    eLpNorm (fun x => η x * (smoothJet z f x - wordLp u z x)) p (volume.restrict K) ≤
        eLpNorm η ∞ (volume.restrict K) *
          eLpNorm (fun x => smoothJet z f x - wordLp u z x) p (volume.restrict K) := by
      convert
        (eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm (μ := volume.restrict K) (p := p)
          (φ := (η : Domain d → 𝕜)) (f := fun x => smoothJet z f x - wordLp u z x)
          η.continuous.aestronglyMeasurable) using 1
    _ ≤ _ := by
      gcongr
      exact Measure.restrict_le_self

lemma testPartial_single_support (i : Fin d) (η : Tests 𝕜 Ω) :
    tsupport (testPartialCLM [i] η) ⊆ tsupport η := by
  have he : (⇑(testPartialCLM [i] η)) = fun x => fderiv ℝ η x (coordinateVector i) :=
    funext (testPartial_single_apply i η)
  rw [he]
  exact tsupport_fderiv_apply_subset ℝ (coordinateVector i)

lemma cutoffError_small (u : SobolevSpace 𝕜 d Ω m p) (w : List (Fin d))
    (η : Tests 𝕜 Ω) (z : List (Fin d)) (h : w.length + z.length ≤ m)
    (K : Set (Domain d)) (hK : MeasurableSet K) (hs : tsupport η ⊆ K) (hKΩ : K ⊆ Ω)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f),
      (∀ q : List (Fin d), q.length ≤ m →
        eLpNorm (fun x => smoothJet q f x - wordLp u q x) p (volume.restrict K) < ENNReal.ofReal δ) →
      ‖cutoffError u f hf w η z‖ < ε := by
  induction w generalizing η z ε with
  | nil =>
    let A := eLpNorm η ∞ (volume : Measure (Domain d))
    have hA : A ≠ ∞ :=
      (η.continuous.memLp_of_hasCompactSupport (p := ∞) (μ := volume) η.hasCompactSupport).eLpNorm_ne_top
    let C : ℝ := A.toReal + 1
    have hC : 0 < C := by dsimp [C]; positivity
    have hAC : A ≤ ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_toReal hA]
      exact ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith)
    refine ⟨ε / C, div_pos hε hC, ?_⟩
    intro f hf hg
    have he := hg z (by simpa using h)
    have hb : ENNReal.ofReal ‖cutoffError u f hf [] η z‖ < ENNReal.ofReal ε := by
      calc
        _ ≤ A * eLpNorm (fun x => smoothJet z f x - wordLp u z x) p (volume.restrict K) :=
          cutoffError_nil_enorm_le u f hf η z K hK hs hKΩ
        _ ≤ ENNReal.ofReal C * eLpNorm (fun x => smoothJet z f x - wordLp u z x) p (volume.restrict K) := by
          exact mul_le_mul_left hAC _
        _ < ENNReal.ofReal C * ENNReal.ofReal (ε / C) := by
          simpa only [mul_comm] using ENNReal.mul_lt_mul_left
            (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top he
        _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul hC.le]
          congr 1
          field_simp
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hb
  | cons i w ih =>
    obtain ⟨δ₁, hδ₁, h₁⟩ := ih (testPartialCLM [i] η) z
      (by simp only [List.length_cons] at h; omega)
      ((testPartial_single_support i η).trans hs) (ε / 2) (by linarith)
    obtain ⟨δ₂, hδ₂, h₂⟩ := ih η (z ++ [i])
      (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at h; omega)
      hs (ε / 2) (by linarith)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    intro f hf hg
    have hb₁ := h₁ f hf (fun q hq => (hg q hq).trans_le
      (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    have hb₂ := h₂ f hf (fun q hq => (hg q hq).trans_le
      (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
    rw [cutoffError_cons]
    exact (norm_add_le _ _).trans_lt (by linarith)

/-- Quantitative local jet control gives a small complete Sobolev cutoff error. -/
lemma compact_cutoff_error_words (u : SobolevSpace 𝕜 d Ω m p)
    (η : Tests 𝕜 Ω) (K : Set (Domain d)) (hK : MeasurableSet K)
    (hs : tsupport η ⊆ K) (hKΩ : K ⊆ Ω) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f),
      (∀ q : List (Fin d), q.length ≤ m →
        eLpNorm (fun x => smoothJet q f x - wordLp u q x) p (volume.restrict K) < ENNReal.ofReal δ) →
      ∃ e : SobolevSpace 𝕜 d Ω m p,
        underlyingLp e =ᵐ[volume.restrict (Ω : Set (Domain d))]
          (fun x => η x * (f x - underlyingLp u x)) ∧ ‖e‖ < ε := by
  classical
  let N : ℝ := Fintype.card (DerivativeIndex d m)
  let τ : ℝ := ε / (N + 1)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hτ : 0 < τ := div_pos hε (by positivity)
  have hscale (α : DerivativeIndex d m) := cutoffError_small u (multiIndexWord (natIndex α)) η []
    (by simpa [natIndex] using α.property) K hK hs hKΩ τ hτ
  choose δ hδ hδsmall using hscale
  have hnonempty : (Finset.univ : Finset (DerivativeIndex d m)).Nonempty :=
    ⟨zeroIndex d m, Finset.mem_univ _⟩
  let δ₀ : ℝ := Finset.univ.inf' hnonempty δ
  have hδ₀ : 0 < δ₀ := by
    obtain ⟨α, _, heq⟩ := Finset.exists_mem_eq_inf' hnonempty δ
    change 0 < Finset.univ.inf' hnonempty δ
    rw [heq]
    exact hδ α
  have hδle (α : DerivativeIndex d m) : δ₀ ≤ δ α := Finset.inf'_le _ (Finset.mem_univ α)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro f hf hg
  let e : SobolevSpace 𝕜 d Ω m p := testToSobolev m (smoothMulTest η f hf) - cutoffSobolev η u
  have heα (α : DerivativeIndex d m) : e.val α = cutoffError u f hf
      (multiIndexWord (natIndex α)) η [] := rfl
  refine ⟨e, ?_, ?_⟩
  · have ht : underlyingLp (testToSobolev (p := p) m (smoothMulTest η f hf)) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => η x * f x := by
      change (testToSobolev (p := p) m (smoothMulTest η f hf)).val (zeroIndex d m) =ᵐ[volume.restrict (Ω : Set (Domain d))] _
      rw [testToSobolev_underlying]
      exact testToDomainLp_coe _
    filter_upwards [Lp.coeFn_sub
        (underlyingLp (testToSobolev (p := p) m (smoothMulTest η f hf)))
        (underlyingLp (cutoffSobolev η u)), ht, cutoffSobolev_coe η u] with x hx ht₁ ht₂
    change ((underlyingLp (testToSobolev (p := p) m (smoothMulTest η f hf)) -
      underlyingLp (cutoffSobolev η u)) : DomainLp 𝕜 Ω p) x = _
    rw [hx]
    change underlyingLp (testToSobolev (p := p) m (smoothMulTest η f hf)) x -
      underlyingLp (cutoffSobolev η u) x = _
    rw [ht₁, ht₂]
    ring
  · have hb (α : DerivativeIndex d m) : ‖e.val α‖ < τ := by
      rw [heα]
      exact hδsmall α f hf (fun q hq => (hg q hq).trans_le (ENNReal.ofReal_le_ofReal (hδle α)))
    have hr : N * τ < ε := by
      dsimp [τ]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < N + 1)]
      nlinarith
    calc
      ‖e‖ = ∑ α : DerivativeIndex d m, ‖e.val α‖ := sobolev_norm_formula 𝕜 d Ω m p e
      _ ≤ ∑ _ : DerivativeIndex d m, τ := Finset.sum_le_sum (fun α _ => (hb α).le)
      _ = N * τ := by simp [N]
      _ < ε := hr


lemma partialFunction_single_comm (i j : Fin d) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    partialFunction [i] (partialFunction [j] f) = partialFunction [j] (partialFunction [i] f) := by
  funext x
  change fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector j)) x (coordinateVector i) =
    fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector i)) x (coordinateVector j)
  rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by simp)).differentiable (by simp) x)
      (differentiableAt_const _),
    fderiv_clm_apply ((hf.fderiv_right (m := 1) (by simp)).differentiable (by simp) x)
      (differentiableAt_const _)]
  simpa using hf.contDiffAt.isSymmSndFDerivAt (by simp) (coordinateVector i) (coordinateVector j)

lemma partialFunction_perm {w z : List (Fin d)} (h : w.Perm z) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : partialFunction w f = partialFunction z f := by
  induction h with
  | nil => rfl
  | cons i h ih =>
    change partialFunction [i] (partialFunction _ f) = partialFunction [i] (partialFunction _ f)
    rw [ih]
  | swap i j w =>
    exact partialFunction_single_comm j i (partialFunction w f) (partialFunction_contDiff w f hf)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂


lemma partialFunction_canonical (w : List (Fin d)) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    partialFunction w.reverse f =
      partialFunction (multiIndexWord (fun i => w.count i)).reverse f :=
  by
  apply partialFunction_perm _ f hf
  apply List.perm_iff_count.mpr
  intro i
  simp


lemma smoothJet_wordIndex (z : List (Fin d)) (hz : z.length ≤ m)
    (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    smoothJet z f = ExpandedFA.Sobolev.Smoothing.classicalDerivative (wordIndex z hz) f := by
  change partialFunction z.reverse f = partialFunction
    (multiIndexWord (natIndex (wordIndex z hz))).reverse f
  rw [partialFunction_canonical z f hf]
  rfl

lemma word_error_lt_of_canonical (u : SobolevSpace 𝕜 d Ω m p)
    (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (K : Set (Domain d)) (δ : ℝ≥0∞)
    (H : ∀ α : DerivativeIndex d m, eLpNorm
      (ExpandedFA.Sobolev.Smoothing.classicalDerivative α f - (u.val α : Domain d → 𝕜))
        p (volume.restrict K) < δ)
    (z : List (Fin d)) (hz : z.length ≤ m) :
    eLpNorm (smoothJet z f - (wordLp u z : Domain d → 𝕜)) p (volume.restrict K) < δ := by
  rw [smoothJet_wordIndex z hz f hf, wordLp, dite_eq_left hz]
  exact H (wordIndex z hz)


lemma compact_cutoff_error_canonical_of_words (u : SobolevSpace 𝕜 d Ω m p)
    (Hwords : ∀ (η : Tests 𝕜 Ω) (K : Set (Domain d)), MeasurableSet K →
      tsupport η ⊆ K → K ⊆ Ω → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ f : Domain d → 𝕜, ∀ hf : ContDiff ℝ (⊤ : ℕ∞) f,
          (∀ q : List (Fin d), q.length ≤ m →
            eLpNorm (fun x => smoothJet q f x - wordLp u q x) p (volume.restrict K) <
              ENNReal.ofReal δ) →
          ∃ e : SobolevSpace 𝕜 d Ω m p,
            underlyingLp e =ᵐ[volume.restrict (Ω : Set (Domain d))]
              (fun x => η x * (f x - underlyingLp u x)) ∧ ‖e‖ < ε) :
    ∀ η : Tests 𝕜 Ω, ∀ τ : ℝ, 0 < τ → ∃ δ : ℝ, 0 < δ ∧
      ∀ f : Domain d → 𝕜, ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ α : DerivativeIndex d m,
          eLpNorm (classicalDerivative α f - (u.val α : Domain d → 𝕜)) p
            (volume.restrict (tsupport η)) < ENNReal.ofReal δ) →
        ∃ e : SobolevSpace 𝕜 d Ω m p,
          e.val (zeroIndex d m) =ᵐ[volume.restrict (Ω : Set (Domain d))]
            (fun x => η x * (f x - u.val (zeroIndex d m) x)) ∧ ‖e‖ < τ := by
  intro η τ hτ
  obtain ⟨δ, hδ, Hδ⟩ := Hwords η (tsupport η) (isClosed_tsupport η).measurableSet
    Subset.rfl η.tsupport_subset τ hτ
  refine ⟨δ, hδ, ?_⟩
  intro f hf herr
  apply Hδ f hf
  intro q hq
  exact word_error_lt_of_canonical u f hf (tsupport η) (ENNReal.ofReal δ) herr q hq


def liftRealTest (η : Tests ℝ Ω) : Tests 𝕜 Ω :=
  ⟨fun x => (η x : 𝕜),
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp η.contDiff,
    η.hasCompactSupport.comp_left (by simp),
    (tsupport_comp_subset (g := fun r : ℝ => (r : 𝕜)) (by simp) η).trans η.tsupport_subset⟩

@[simp] lemma liftRealTest_apply (η : Tests ℝ Ω) (x : Domain d) :
    liftRealTest (𝕜 := 𝕜) η x = (η x : 𝕜) := rfl

@[simp] lemma liftRealTest_tsupport (η : Tests ℝ Ω) :
    tsupport (liftRealTest (𝕜 := 𝕜) η) = tsupport η := by
  change closure (Function.support (fun x => (η x : 𝕜))) = closure (Function.support η)
  congr 1
  ext x
  simp only [Function.mem_support]
  exact not_congr RCLike.ofReal_eq_zero

lemma liftRealTest_mul (η : Tests ℝ Ω) (f : Domain d → 𝕜) (x : Domain d) :
    liftRealTest (𝕜 := 𝕜) η x * f x = η x • f x := by
  simp only [liftRealTest_apply, RCLike.real_smul_eq_coe_mul]


lemma real_cutoff_estimate_of_complex (u : SobolevSpace 𝕜 d Ω m p)
    (H : ∀ η : Tests 𝕜 Ω, ∀ τ : ℝ, 0 < τ → ∃ δ : ℝ, 0 < δ ∧
      ∀ f : Domain d → 𝕜, ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ α : DerivativeIndex d m,
          eLpNorm (classicalDerivative α f - (u.val α : Domain d → 𝕜)) p
            (volume.restrict (tsupport η)) < ENNReal.ofReal δ) →
        ∃ e : SobolevSpace 𝕜 d Ω m p,
          e.val (zeroIndex d m) =ᵐ[volume.restrict (Ω : Set (Domain d))]
            (fun x => η x * (f x - u.val (zeroIndex d m) x)) ∧ ‖e‖ < τ) :
    ∀ η : Tests ℝ Ω, ∀ τ : ℝ, 0 < τ → ∃ δ : ℝ, 0 < δ ∧
      ∀ f : Domain d → 𝕜, ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ α : DerivativeIndex d m,
          eLpNorm (classicalDerivative α f - (u.val α : Domain d → 𝕜)) p
            (volume.restrict (tsupport η)) < ENNReal.ofReal δ) →
        ∃ e : SobolevSpace 𝕜 d Ω m p,
          e.val (zeroIndex d m) =ᵐ[volume.restrict (Ω : Set (Domain d))]
            (fun x => η x • (f x - u.val (zeroIndex d m) x)) ∧ ‖e‖ < τ := by
  intro η τ hτ
  obtain ⟨δ, hδ, Hδ⟩ := H (liftRealTest η) τ hτ
  refine ⟨δ, hδ, ?_⟩
  intro f hf herr
  obtain ⟨e, he, hn⟩ := Hδ f hf (by simpa only [liftRealTest_tsupport] using herr)
  refine ⟨e, ?_, hn⟩
  filter_upwards [he] with x hx
  rw [hx]
  simp only [liftRealTest_apply, RCLike.real_smul_eq_coe_mul]


lemma partial_convolution_test (φ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (f : Domain d → 𝕜) (hf : LocallyIntegrable f volume) (w : List (Fin d)) :
    partialFunction w (convolution φ f (ContinuousLinearMap.mul ℝ 𝕜) volume) =
      convolution (testPartialCLM w φ) f (ContinuousLinearMap.mul ℝ 𝕜) volume := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    change fderiv ℝ (partialFunction w _) x (coordinateVector i) = _
    rw [ih]
    let L := (ContinuousLinearMap.mul ℝ 𝕜).flip
    have he : convolution (testPartialCLM w φ) f (ContinuousLinearMap.mul ℝ 𝕜) volume =
        convolution f (testPartialCLM w φ) L volume := (convolution_flip _).symm
    rw [he, ((testPartialCLM w φ).hasCompactSupport.hasFDerivAt_convolution_right L hf
      ((testPartialCLM w φ).contDiff.of_le (by simp)) x).fderiv,
      convolution_precompR_apply L hf ((testPartialCLM w φ).hasCompactSupport.fderiv ℝ)
        ((testPartialCLM w φ).contDiff.continuous_fderiv (by simp))]
    rw [← convolution_flip (ContinuousLinearMap.mul ℝ 𝕜)]
    rfl

/-- The translated reflected test is the test used in weak differentiation. -/
def reflectTest (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (x : Domain d) :
    Tests 𝕜 (⊤ : Opens (Domain d)) where
  toFun := fun y => φ (x-y)
  contDiff' := φ.contDiff.comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.subLeft x)
  tsupport_subset' := subset_univ _

lemma testPartial_reflect_single (φ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (x : Domain d) (i : Fin d) :
    testPartialCLM [i] (reflectTest φ x) = -reflectTest (testPartialCLM [i] φ) x := by
  ext y
  rw [testPartial_single_apply]
  change fderiv ℝ (fun z => φ (x-z)) y (coordinateVector i) =
    -fderiv ℝ φ (x-y) (coordinateVector i)
  have h := (φ.contDiff.differentiable (by simp) (x-y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_sub x)
  dsimp only [Function.comp_def] at h
  rw [h.fderiv]
  simp

lemma testPartial_reflect (φ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (x : Domain d) (w : List (Fin d)) :
    testPartialCLM w (reflectTest φ x) =
      (-1 : 𝕜)^w.length • reflectTest (testPartialCLM w φ) x := by
  induction w with
  | nil => simp [testPartialCLM]
  | cons i w ih =>
    change testPartialCLM [i] (testPartialCLM w (reflectTest φ x)) = _
    rw [ih, map_smul, testPartial_reflect_single]
    simp only [List.length_cons, pow_succ, smul_neg, neg_smul, mul_neg, mul_one]
    rfl

lemma convolution_test_zeroExtend {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (u : DomainLp 𝕜 Ω p) (x : Domain d) :
    convolution φ (zeroExtend u) (ContinuousLinearMap.mul ℝ 𝕜) volume x =
      ∫ y in (Ω : Set (Domain d)), φ (x-y) * u y := by
  rw [convolution_eq_swap]
  change (∫ y, φ (x-y) * (Ω : Set (Domain d)).indicator u y) = _
  rw [← integral_indicator Ω.isOpen.measurableSet]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => (Set.indicator_mul_right (i := y) (Ω : Set (Domain d)) (fun y => φ (x-y)) u).symm

/-- Restriction of an ambient test whose support lies in Ω. -/
def restrictAmbientTest (φ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (hφ : tsupport φ ⊆ Ω) : Tests 𝕜 Ω :=
  ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩

lemma testPartial_restrictAmbient (φ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (hφ : tsupport φ ⊆ Ω) (w : List (Fin d)) :
    ⇑(testPartialCLM w (restrictAmbientTest φ hφ)) = ⇑(testPartialCLM w φ) := by
  rw [testPartial_formula, testPartial_formula]
  rfl

lemma interior_convolution_identity {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : SobolevSpace 𝕜 d Ω m p) (α : DerivativeIndex d m)
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (x : Domain d)
    (hx : tsupport (reflectTest φ x) ⊆ Ω) :
    classicalDerivative α
      (convolution φ (zeroExtend (u.val (zeroIndex d m))) (ContinuousLinearMap.mul ℝ 𝕜) volume) x =
    convolution φ (zeroExtend (u.val α)) (ContinuousLinearMap.mul ℝ 𝕜) volume x := by
  let w := multiIndexWord (natIndex α)
  let ψ : Tests 𝕜 Ω := restrictAmbientTest (reflectTest φ x) hx
  have h := congrArg (fun T : ScalarDistribution 𝕜 Ω => T ψ) (u.property α)
  change lpDistribution (u.val α) ψ =
    distributionDerivative 𝕜 d Ω w (lpDistribution (u.val (zeroIndex d m))) ψ at h
  rw [distributionDerivative_apply, lpDistribution_apply, lpDistribution_apply] at h
  have htest : ⇑(testPartialCLM w ψ) = fun y =>
      (-1 : 𝕜)^w.length * (testPartialCLM w φ) (x-y) := by
    rw [show ψ = restrictAmbientTest (reflectTest φ x) hx from rfl,
      testPartial_restrictAmbient, testPartial_reflect]
    rfl
  rw [htest] at h
  simp_rw [mul_assoc] at h
  rw [integral_const_mul] at h
  have hsign : (-1 : 𝕜)^w.length * (-1 : 𝕜)^w.length = 1 := by
    rw [← mul_pow]
    simp
  rw [← mul_assoc, hsign, one_mul] at h
  change partialFunction w.reverse _ x = _
  rw [partial_convolution_test φ _ (zeroExtend_locallyIntegrable _), testPartial_reverse,
    convolution_test_zeroExtend, convolution_test_zeroExtend]
  exact h.symm

/-- Lift the real kernel to the manuscript scalar field. -/
def scaledKernelTest (ρ : Domain d → ℝ) (hρ : IsMollifier ρ)
    (ε : ℝ) (hε : 0 < ε) : Tests 𝕜 (⊤ : Opens (Domain d)) where
  toFun := fun y => (ScaledKernelValue ρ ε y : 𝕜)
  contDiff' := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp
    (scaledKernel_properties ρ hρ ε hε).1
  hasCompactSupport' := (scaledKernel_properties ρ hρ ε hε).2.1.comp_left (by simp)
  tsupport_subset' := subset_univ _

lemma regularize_eq_kernelTest {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (u : DomainLp 𝕜 Ω p) :
    regularize ρ ε u = convolution (scaledKernelTest ρ hρ ε hε : Tests 𝕜 ⊤)
      (zeroExtend u) (ContinuousLinearMap.mul ℝ 𝕜) volume := by
  funext x
  apply integral_congr_ae
  exact Eventually.of_forall fun y => RCLike.real_smul_eq_coe_mul _ _

lemma reflected_kernel_support_eventually (ρ : Domain d → ℝ) (hρ : IsMollifier ρ)
    {K : Set (Domain d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ x ∈ K,
      tsupport (reflectTest (scaledKernelTest (𝕜 := 𝕜) ρ hρ ε hε) x) ⊆ Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  filter_upwards [scaledKernel_support_eventually ρ hρ.2.1 hδ] with ε hs hε x hx y hy
  have hts : tsupport (ScaledKernelValue ρ ε) ⊆ closedBall 0 δ :=
    closure_minimal (hs.trans ball_subset_closedBall) isClosed_closedBall
  have hlift : tsupport (scaledKernelTest (𝕜 := 𝕜) ρ hρ ε hε) ⊆
      tsupport (ScaledKernelValue ρ ε) :=
    tsupport_comp_subset (g := fun r : ℝ => (r : 𝕜)) (by simp) _
  have hrefl : x-y ∈ tsupport (scaledKernelTest (𝕜 := 𝕜) ρ hρ ε hε) :=
    tsupport_comp_subset_preimage _ (continuous_const.sub continuous_id) hy
  apply hδΩ
  apply mem_cthickening_of_dist_le y x δ K hx
  have hn := mem_closedBall_zero_iff.mp (hts (hlift hrefl))
  simpa only [dist_eq_norm, norm_sub_rev] using hn

theorem interior_derivative_identity :
    Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.InteriorDerivativeIdentity := by
  intro 𝕜 _ d Ω m p _ ρ hρ u K hK hKΩ
  filter_upwards [reflected_kernel_support_eventually (𝕜 := 𝕜) ρ hρ hK hKΩ,
    self_mem_nhdsWithin] with ε hs hε α x hx
  have he := Set.mem_Ioi.mp hε
  rw [regularize_eq_kernelTest ρ hρ he, regularize_eq_kernelTest ρ hρ he]
  exact interior_convolution_identity u α _ x (hs he x hx)

/-- Assembly of the local conclusions from the derivative identity. -/
theorem local_consequences_of_identity
    (H : Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.InteriorDerivativeIdentity) :
    Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.FinitePConvergence ∧
    Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.UniformDerivativeBounds ∧
    Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.LocalFiniteRConvergence ∧
    Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.WeakStarDerivativeConvergence := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro 𝕜 _ d Ω m p _ hp ρ hρ u K hK hKΩ α
    apply (derivative_regularizations_tendsto hp ρ hρ u hK hKΩ α).congr'
    filter_upwards [H 𝕜 d Ω m p ρ hρ u K hK hKΩ] with ε he
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    change regularize ρ ε (u.val α) x - u.val α x =
      classicalDerivative α (regularize ρ ε (u.val (zeroIndex d m))) x - u.val α x
    rw [he α x hx]
  · intro 𝕜 _ d Ω m ρ hρ u K hK hKΩ
    filter_upwards [H 𝕜 d Ω m ∞ ρ hρ u K hK hKΩ,
      self_mem_nhdsWithin] with ε he hε α x hx
    rw [he α x hx]
    exact regularize_norm_le ρ hρ hε (u.val α) x
  · intro 𝕜 _ d Ω m ρ hρ u K hK hKΩ r hr hrt α
    apply (regularize_local_finite_tendsto ρ hρ (u.val α) hK hKΩ r hr hrt).congr'
    filter_upwards [H 𝕜 d Ω m ∞ ρ hρ u K hK hKΩ] with ε he
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    change regularize ρ ε (u.val α) x - u.val α x =
      classicalDerivative α (regularize ρ ε (u.val (zeroIndex d m))) x - u.val α x
    rw [he α x hx]
  · intro 𝕜 _ d Ω m ρ hρ u K hK hKΩ α g hg
    apply (regularize_weakStar_tendsto ρ hρ (u.val α) hK hKΩ g hg).congr'
    filter_upwards [H 𝕜 d Ω m ∞ ρ hρ u K hK hKΩ] with ε he
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    rw [he α x hx]

theorem finite_p_convergence :
    Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.FinitePConvergence :=
  (local_consequences_of_identity interior_derivative_identity).1

/-- A single positive scale makes all the finitely many interior jet errors
smaller than a prescribed tolerance. This is the scale-selection step for
partition-of-unity approximation. -/
theorem exists_regularization_jet_error_lt {m : ℕ} (hp : p ≠ ∞)
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ) (u : SobolevSpace 𝕜 d Ω m p)
    {K : Set (Domain d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ α : DerivativeIndex d m,
      eLpNorm
        (classicalDerivative α (regularize ρ ε (u.val (zeroIndex d m))) -
          (u.val α : Domain d → 𝕜)) p (volume.restrict K) < ENNReal.ofReal δ := by
  have hs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ α : DerivativeIndex d m,
      eLpNorm
        (classicalDerivative α (regularize ρ ε (u.val (zeroIndex d m))) -
          (u.val α : Domain d → 𝕜)) p (volume.restrict K) < ENNReal.ofReal δ := by
    apply eventually_all.mpr
    intro α
    exact (finite_p_convergence 𝕜 d Ω m p hp ρ hρ u K hK hKΩ α).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ))
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, herrors⟩ := (hpos.and hs).exists
  exact ⟨ε, hε, herrors⟩

theorem uniform_derivative_bounds :
    Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.UniformDerivativeBounds :=
  (local_consequences_of_identity interior_derivative_identity).2.1

theorem local_finite_r_convergence :
    Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.LocalFiniteRConvergence :=
  (local_consequences_of_identity interior_derivative_identity).2.2.1

theorem weak_star_derivative_convergence :
    Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.WeakStarDerivativeConvergence :=
  (local_consequences_of_identity interior_derivative_identity).2.2.2

/-- Smooth density at order zero, including all arbitrary open domains. -/
theorem smooth_density_order_zero (hp : p ≠ ∞) :
    Dense (Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.SmoothMembers 𝕜 d Ω 0 p) := by
  let : Unique (DerivativeIndex d 0) :=
    ⟨⟨zeroIndex d 0⟩, fun α => Subtype.ext (funext (fun i => Fin.eq_zero _))⟩
  intro u
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨v, ⟨f, hvf, hfc, hfd⟩, hv⟩ := Metric.mem_closure_iff.mp
    ((Lp.dense_hasCompactSupport_contDiff (E := Domain d) (F := 𝕜)
      (μ := volume.restrict (Ω : Set (Domain d))) hp) (u.val (zeroIndex d 0))) ε hε
  let z : SobolevSpace 𝕜 d Ω 0 p :=
    ⟨WithLp.toLp 1 (fun _ : DerivativeIndex d 0 => v), by
      intro α
      change lpDistribution v =
        Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
          𝕜 d Ω (natIndex α) (lpDistribution v)
      have hα : natIndex α = fun _ => 0 := by
        funext i
        exact congrArg Fin.val (Fin.eq_zero (α.val i))
      rw [hα, derivative_zero]⟩
  refine ⟨z, ⟨f, hfd.contDiffOn, hvf⟩, ?_⟩
  have heq : dist u z = dist (u.val (zeroIndex d 0)) v := by
    rw [dist_eq_norm, sobolev_norm_formula]
    change (∑ α : DerivativeIndex d 0, ‖(u-z).val α‖) = _
    simp only [Fintype.sum_unique]
    rw [dist_eq_norm]
    rfl
  simpa only [heq] using hv

local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p⟩

def testLpPairing (φ : Tests 𝕜 Ω) : DomainLp 𝕜 Ω p →L[𝕜] 𝕜 :=
  ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
    (volume.restrict (Ω : Set (Domain d))) p p.conjExponent).flip
    ((φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ)

@[simp] theorem testLpPairing_apply (φ : Tests 𝕜 Ω) (u : DomainLp 𝕜 Ω p) :
    testLpPairing φ u = lpDistribution u φ := by
  rw [testLpPairing, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral, lpDistribution_apply]
  apply integral_congr_ae
  have hφ : MemLp (φ : Domain d → 𝕜) p.conjExponent
      (volume.restrict (Ω : Set (Domain d))) :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  filter_upwards [hφ.coeFn_toLp] with x hx
  rw [hx, mul_comm]
  rfl

theorem derivativeGraph_isClosed {m : ℕ} :
    IsClosed (derivativeGraph 𝕜 Ω m p : Set (DerivativeTuple 𝕜 Ω m p)) := by
  have hrepr : (derivativeGraph 𝕜 Ω m p : Set (DerivativeTuple 𝕜 Ω m p)) =
      ⋂ α : DerivativeIndex d m, ⋂ φ : Tests 𝕜 Ω,
        {v | testLpPairing φ (v α) =
          (-1 : 𝕜) ^ (multiIndexWord (natIndex α)).length *
            testLpPairing (testPartialCLM (multiIndexWord (natIndex α)) φ)
              (v (zeroIndex d m))} := by
    ext v
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    change (∀ α, lpDistribution (v α) = _) ↔ _
    constructor
    · intro hv α φ
      have h := congrArg (fun T : ScalarDistribution 𝕜 Ω => T φ) (hv α)
      simpa [testLpPairing_apply, lpDistributionLM,
        Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue,
        Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue] using h
    · intro hv α
      ext φ
      simpa [testLpPairing_apply, lpDistributionLM,
        Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue,
        Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue] using hv α φ
  rw [hrepr]
  apply isClosed_iInter
  intro α
  apply isClosed_iInter
  intro φ
  apply isClosed_eq
  · exact (testLpPairing φ).continuous.comp (PiLp.proj (𝕜 := 𝕜) 1
      (fun _ : DerivativeIndex d m => DomainLp 𝕜 Ω p) α).continuous
  · exact continuous_const.mul ((testLpPairing
      (testPartialCLM (multiIndexWord (natIndex α)) φ)).continuous.comp
        (PiLp.proj (𝕜 := 𝕜) 1 (fun _ : DerivativeIndex d m => DomainLp 𝕜 Ω p)
          (zeroIndex d m)).continuous)

theorem locallyFinite_finsum_smooth {κ : Type} (η : κ → Tests ℝ Ω)
    (hη : LocallyFinite (fun j => (Subtype.val : Ω → Domain d) ⁻¹' tsupport (η j)))
    (f : κ → Domain d → 𝕜) (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∑ᶠ j, η j x • f j x) Ω := by
  classical
  have hlf : LocallyFinite (fun j => Function.support (fun y : Ω => η j y • f j y)) :=
    hη.subset fun j y hy => subset_tsupport (η j) (by
      intro hzero
      exact hy (by simp [hzero]))
  intro x hx
  obtain ⟨S, hS⟩ := finsum_eventually_eq_sum hlf (⟨x, hx⟩ : Ω)
  have hmap : Filter.map (Subtype.val : Ω → Domain d) (𝓝 (⟨x, hx⟩ : Ω)) = 𝓝 x :=
    map_nhds_subtype_coe_eq_nhds hx (Ω.isOpen.mem_nhds hx)
  have hS' : (fun y => ∑ᶠ j, η j y • f j y) =ᶠ[𝓝 x]
      (fun y => ∑ j ∈ S, η j y • f j y) := by
    rw [← hmap]
    exact hS
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ j ∈ S, η j y • f j y) :=
    ContDiff.sum fun j _ => (η j).contDiff.smul (hf j)
  exact (hsmooth.contDiffAt.congr_of_eventuallyEq hS').contDiffWithinAt

theorem weighted_smooth_gluing {m : ℕ} {κ : Type} [Countable κ]
    (η : κ → Tests ℝ Ω)
    (hη : LocallyFinite (fun j => (Subtype.val : Ω → Domain d) ⁻¹' tsupport (η j)))
    (hηsum : ∀ x ∈ Ω, ∑ᶠ j, η j x = 1)
    (f : κ → Domain d → 𝕜) (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j))
    (u : SobolevSpace 𝕜 d Ω m p) (e : κ → SobolevSpace 𝕜 d Ω m p)
    (he : ∀ j, (e j).val (zeroIndex d m) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      (fun x => η j x • (f j x - u.val (zeroIndex d m) x)))
    (hnorm : Summable (fun j => ‖e j‖)) :
    ∃ v : SobolevSpace 𝕜 d Ω m p, ∃ F : Domain d → 𝕜,
      ContDiffOn ℝ (⊤ : ℕ∞) F Ω ∧
      v.val (zeroIndex d m) =ᵐ[volume.restrict (Ω : Set (Domain d))] F ∧
      ‖v - u‖ ≤ ∑' j, ‖e j‖ := by
  classical
  let : CompleteSpace (SobolevSpace 𝕜 d Ω m p) :=
    (derivativeGraph_isClosed (𝕜 := 𝕜) (Ω := Ω) (p := p) (m := m)).isComplete.completeSpace_coe
  have hes : Summable e := hnorm.of_norm
  let E : SobolevSpace 𝕜 d Ω m p := ∑' j, e j
  let P : SobolevSpace 𝕜 d Ω m p →L[𝕜] DomainLp 𝕜 Ω p :=
    (PiLp.proj (𝕜 := 𝕜) 1 (fun _ : DerivativeIndex d m => DomainLp 𝕜 Ω p)
      (zeroIndex d m)).comp (derivativeGraph 𝕜 Ω m p).subtypeL
  have hP : E.val (zeroIndex d m) = ∑' j, (e j).val (zeroIndex d m) :=
    P.map_tsum hes
  have hcoordnorm : Summable (fun j => ‖(e j).val (zeroIndex d m)‖) :=
    hnorm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => PiLp.norm_apply_le (e j).val _)
  have hE : E.val (zeroIndex d m) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      (fun x => ∑' j, (e j).val (zeroIndex d m) x) := by
    rw [hP]
    exact Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hcoordnorm)
  let F : Domain d → 𝕜 := fun x => ∑ᶠ j, η j x • f j x
  refine ⟨u + E, F, locallyFinite_finsum_smooth η hη f hf, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add (u.val (zeroIndex d m)) (E.val (zeroIndex d m)),
      hE, ae_all_iff.mpr he, ae_restrict_mem Ω.isOpen.measurableSet] with x hadd hEx hex hx
    have hηx : Function.HasFiniteSupport (fun j => η j x) :=
      (hη.point_finite (⟨x, hx⟩ : Ω)).subset fun j hj => subset_tsupport (η j) hj
    have hfin (g : κ → 𝕜) : Function.HasFiniteSupport (fun j => η j x • g j) :=
      hηx.subset fun j hj => by
        intro hzero
        exact hj (by simp [hzero])
    have hseries : (∑' j, (e j).val (zeroIndex d m) x) = F x - u.val (zeroIndex d m) x := by
      calc
        _ = ∑' j, η j x • (f j x - u.val (zeroIndex d m) x) := tsum_congr hex
        _ = ∑ᶠ j, η j x • (f j x - u.val (zeroIndex d m) x) :=
          tsum_eq_finsum (hfin _)
        _ = F x - u.val (zeroIndex d m) x := by
          simp_rw [smul_sub]
          rw [finsum_sub_distrib (hfin _) (hfin _), ← finsum_smul' hηx,
            hηsum x hx, one_smul]
    change ((u.val (zeroIndex d m) + E.val (zeroIndex d m)) : DomainLp 𝕜 Ω p) x = F x
    rw [hadd]
    change u.val (zeroIndex d m) x + E.val (zeroIndex d m) x = F x
    rw [hEx, hseries]
    simp [sub_eq_add_neg, add_comm]
  · simpa only [add_sub_cancel_left] using norm_tsum_le_tsum_norm hnorm


/-- Assembly of global approximation from a compact-cutoff jet estimate.
Only the approximation errors are summed in the Sobolev norm. -/
theorem smooth_approximation_of_cutoff_error_estimate {m : ℕ} (hp : p ≠ ∞)
    (u : SobolevSpace 𝕜 d Ω m p)
    (H : ∀ η : Tests ℝ Ω, ∀ τ : ℝ, 0 < τ → ∃ δ : ℝ, 0 < δ ∧
      ∀ f : Domain d → 𝕜, ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ α : DerivativeIndex d m,
          eLpNorm (classicalDerivative α f - (u.val α : Domain d → 𝕜)) p
            (volume.restrict (tsupport η)) < ENNReal.ofReal δ) →
        ∃ e : SobolevSpace 𝕜 d Ω m p,
          e.val (zeroIndex d m) =ᵐ[volume.restrict (Ω : Set (Domain d))]
            (fun x => η x • (f x - u.val (zeroIndex d m) x)) ∧ ‖e‖ < τ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : SobolevSpace 𝕜 d Ω m p,
      v ∈ Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.SmoothMembers 𝕜 d Ω m p ∧
      dist u v < ε := by
  classical
  obtain ⟨κ, hκ, η, _, hη, hηsum, _⟩ := smooth_partition_of_unity d Ω Unit
    (fun _ => (Set.univ : Set (Domain d))) (fun _ => isOpen_univ)
    (by intro x _; exact mem_iUnion.mpr ⟨(), mem_univ x⟩)
  let : Countable κ := hκ
  let : Encodable κ := Encodable.ofCountable κ
  obtain ⟨b, hb, c, hbc, hc⟩ := posSumOfEncodable (half_pos hε) κ
  choose δ hδ hδapprox using fun j => H (η j) (b j) (hb j)
  obtain ⟨ρ, hρ⟩ := exists_mollifier d
  have hscale (j : κ) : ∃ s : ℝ, 0 < s ∧ ∀ α : DerivativeIndex d m,
      eLpNorm
        (classicalDerivative α (regularize ρ s (u.val (zeroIndex d m))) -
          (u.val α : Domain d → 𝕜)) p (volume.restrict (tsupport (η j))) <
            ENNReal.ofReal (δ j) :=
    exists_regularization_jet_error_lt hp ρ hρ u (η j).hasCompactSupport
      (η j).tsupport_subset (hδ j)
  choose s hs herrors using hscale
  choose e he henorm using fun j => hδapprox j
    (regularize ρ (s j) (u.val (zeroIndex d m))) (regularize_contDiff ρ hρ (hs j) _)
    (herrors j)
  have hnormsum : Summable (fun j => ‖e j‖) :=
    hbc.summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => (henorm j).le)
  have hsum : ∑' j, ‖e j‖ ≤ c := by
    calc
      _ ≤ ∑' j, b j := hnormsum.tsum_le_tsum (fun j => (henorm j).le) hbc.summable
      _ = c := hbc.tsum_eq
  obtain ⟨v, F, hF, hvF, hv⟩ := weighted_smooth_gluing η hη hηsum
    (fun j => regularize ρ (s j) (u.val (zeroIndex d m)))
    (fun j => regularize_contDiff ρ hρ (hs j) _) u e he hnormsum
  refine ⟨v, ⟨F, hF, hvF⟩, ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact hv.trans_lt ((hsum.trans hc).trans_lt (half_lt_self hε))


/-- Smooth functions on an arbitrary open domain are dense in every finite-p
integer-order Sobolev space, with the original sum-component norm. -/
theorem smooth_density :
    Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.SmoothDensity := by
  intro 𝕜 _ d Ω m p _ hp u
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  exact smooth_approximation_of_cutoff_error_estimate hp u
    (real_cutoff_estimate_of_complex u
      (compact_cutoff_error_canonical_of_words u (compact_cutoff_error_words u))) hε

end ExpandedFA.Sobolev.Smoothing
