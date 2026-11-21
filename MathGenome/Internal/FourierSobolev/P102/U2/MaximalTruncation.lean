import MathGenome.Internal.FourierSobolev.Specs.P102.U2.MaximalTruncation
import MathGenome.Internal.FourierSobolev.P102.U2.CZLp
import MathGenome.Internal.FourierSobolev.P102.U2.MaximalStrong
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.StandardConvolutionOperator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace P102.U2.MaximalTruncation
open CZWeak CZLpData MaximalTruncationData
open ExpandedFA.SingularIntegrals.StandardConvolution

variable {d : ℕ}

/-- Changing an input representative changes none of the actual truncations,
including their values at exceptional centers. -/
lemma truncated_congr_ae (K : Point d → ℂ) {f g : Point d → ℂ}
    (hfg : f =ᵐ[volume] g) (ε : ℝ) (x : Point d) :
    truncated K f ε x = truncated K g ε x := by
  apply setIntegral_congr_ae (by measurability)
  filter_upwards [hfg] with y hy _
  rw [hy]

lemma maximalTruncation_congr_ae (K : Point d → ℂ) {f g : Point d → ℂ}
    (hfg : f =ᵐ[volume] g) : maximalTruncation K f = maximalTruncation K g := by
  funext x
  simp only [maximalTruncation, truncated_congr_ae K hfg]

lemma continuousOn_translate {K : Point d → ℂ}
    (hK : ContinuousOn K ({0}ᶜ : Set (Point d)))
    (S : Set (Point d)) (x : Point d) (hx : x ∉ S) :
    ContinuousOn (fun y => K (x - y)) S := by
  apply hK.comp (continuous_const.sub continuous_id).continuousOn
  intro y hy
  change x - y ≠ 0
  exact sub_ne_zero.mpr (fun h => hx (h ▸ hy))

/-- Local continuity of K alone suffices for absolute off-support existence. -/
lemma off_support_integrable {K b : Point d → ℂ}
    (hK : ContinuousOn K ({0}ᶜ : Set (Point d)))
    (hb : Integrable b volume) (S : Set (Point d)) (hS : IsCompact S)
    (hs : ∀ᵐ y ∂volume, y ∉ S → b y = 0) (x : Point d) (hx : x ∉ S) :
    Integrable (fun y => K (x - y) * b y) volume := by
  have hi : IntegrableOn (fun y => K (x - y) * b y) S volume :=
    IntegrableOn.continuousOn_mul (continuousOn_translate hK S x hx) hb.integrableOn hS
  have he : (fun y => K (x - y) * b y) =ᵐ[volume]
      S.indicator (fun y => K (x - y) * b y) := by
    filter_upwards [hs] with y hy
    by_cases h : y ∈ S
    · simp [h]
    · simp [h, hy h]
  exact (hi.integrable_indicator hS.measurableSet).congr he.symm

lemma integrable_of_compact_support_L2 {b : Point d → ℂ}
    (hb : MemLp b 2 volume) (S : Set (Point d)) (hS : IsCompact S)
    (hs : ∀ᵐ y ∂volume, y ∉ S → b y = 0) : Integrable b volume := by
  have : IsFiniteMeasure ((volume : Measure (Point d)).restrict S) :=
    ⟨by simpa using hS.measure_lt_top⟩
  have hi : IntegrableOn b S volume := (hb.restrict S).integrable (by norm_num)
  apply (hi.integrable_indicator hS.measurableSet).congr
  filter_upwards [hs] with y hy
  by_cases h : y ∈ S
  · simp [h]
  · simp [h, hy h]

/-- Every smooth truncation is absolutely integrable, including at centers
inside the support. No size bound or cancellation certificate is needed here. -/
lemma smooth_truncated_integrable {K : Point d → ℂ}
    (hK : ContinuousOn K ({0}ᶜ : Set (Point d)))
    (φ : MaximalTruncationData.Tests d) (x : Point d) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun y => K (x - y) * φ y) {y | ε < ‖x - y‖} volume := by
  let S := tsupport φ ∩ {y : Point d | ε ≤ ‖x - y‖}
  have hS : IsCompact S := φ.hasCompactSupport.inter_right
    (isClosed_le continuous_const (continuous_const.sub continuous_id).norm)
  have hx : x ∉ S := by
    intro h
    have : ε ≤ ‖x - x‖ := h.2
    simp only [sub_self, norm_zero] at this
    exact (not_le.mpr hε) this
  have hi : IntegrableOn (fun y => K (x - y) * φ y) S volume :=
    IntegrableOn.continuousOn_mul (continuousOn_translate hK S x hx)
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn hS
  apply (hi.integrable_indicator hS.measurableSet).integrableOn.congr
  have hA : MeasurableSet {y : Point d | ε < ‖x - y‖} := by measurability
  filter_upwards [ae_restrict_mem hA] with y hy
  by_cases hs : y ∈ tsupport φ
  · have : y ∈ S := ⟨hs, hy.le⟩
    simp [this]
  · have hφ : φ y = 0 := image_eq_zero_of_notMem_tsupport hs
    simp [hφ]

/-- Outside a compact a.e. support, all sufficiently small truncations are
literally the full off-support integral. This is independent of integrability. -/
lemma truncated_eventually_eq {K b : Point d → ℂ}
    (S : Set (Point d)) (hS : IsClosed S)
    (hs : ∀ᵐ y ∂volume, y ∉ S → b y = 0) (x : Point d) (hx : x ∉ S) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      truncated K b ε x = ∫ y, K (x - y) * b y := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS.isOpen_compl x hx
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  filter_upwards [he] with ε hε
  rw [truncated, ← integral_indicator (by measurability :
    MeasurableSet {y : Point d | ε < ‖x - y‖})]
  apply integral_congr_ae
  filter_upwards [hs] with y hy
  by_cases h : ε < ‖x - y‖
  · simp [h]
  · have hys : y ∉ S := hball (by
      rw [mem_ball, dist_eq_norm_sub, norm_sub_rev]
      exact (le_of_not_gt h).trans_lt hε)
    simp [h, hy hys]

lemma principalValue_off_support (K : Point d → ℂ)
    (φ : MaximalTruncationData.Tests d) (x : Point d) (hx : x ∉ tsupport φ) :
    principalValue K φ x = ∫ y, K (x - y) * φ y := by
  have he := truncated_eventually_eq (K := K) (b := φ) (tsupport φ)
    (isClosed_tsupport φ)
    (Filter.Eventually.of_forall fun y hy => image_eq_zero_of_notMem_tsupport hy) x hx
  have ht : Tendsto (fun ε => truncated K φ ε x) (𝓝[>] 0)
      (𝓝 (∫ y, K (x - y) * φ y)) :=
    tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)
  exact ht.limUnder_eq

/-- The assumed L² action gives the genuine smooth off-support formula. -/
lemma smooth_off_support {K : Point d → ℂ} {T : Operator d}
    (hT : SmoothL2Action T K) (φ : MaximalTruncationData.Tests d) :
    ∀ᵐ x ∂volume, x ∉ tsupport φ →
      T (testL2 φ) x = ∫ y, K (x - y) * φ y := by
  filter_upwards [hT φ] with x hx hxs
  exact hx.trans (principalValue_off_support K φ x hxs)


/-- A smooth cutoff away from the center turns a merely continuous off-origin
kernel into a compactly supported continuous L² weight. -/
lemma cutoff_weight_memLp {K : Point d → ℂ}
    (hK : ContinuousOn K ({0}ᶜ : Set (Point d)))
    (χ : MaximalTruncationData.Tests d) (x : Point d) (hx : x ∉ tsupport χ) :
    MemLp (fun y => K (x - y) * χ y) 2 volume := by
  have hc : ContinuousOn (fun y => K (x - y) * χ y) ({x}ᶜ) :=
    (continuousOn_translate hK {x}ᶜ x (by simp)).mul χ.continuous.continuousOn
  have hs : tsupport (fun y => K (x - y) * χ y) ⊆ {x}ᶜ := by
    intro y hy h
    exact hx (mem_singleton_iff.mp h ▸ tsupport_mul_subset_right hy)
  exact (hc.continuous_of_tsupport_subset isClosed_singleton.isOpen_compl hs).memLp_of_hasCompactSupport
    χ.hasCompactSupport.mul_left

/-- Density and a continuous L² pairing extend the smooth off-support formula
outside any fixed cutoff. No distribution or translation invariance hypothesis
is added to the operator. -/
lemma off_support_of_cutoff {K : Point d → ℂ} (T : Operator d)
    (hK : ContinuousOn K ({0}ᶜ : Set (Point d))) (hT : SmoothL2Action T K)
    (f : Point d → ℂ) (S : Set (Point d)) (h2 : MemLp f 2 volume)
    (hs : ∀ᵐ y ∂volume, y ∉ S → f y = 0)
    (χ : MaximalTruncationData.Tests d) (hχ : EqOn χ 1 S) :
    ∀ᵐ x ∂volume, x ∉ tsupport χ →
      T (h2.toLp f) x = ∫ y, K (x - y) * f y := by
  have hd := Lp.dense_hasCompactSupport_contDiff (F := ℂ)
    (μ := (volume : Measure (Point d))) (p := 2) (by norm_num)
  obtain ⟨u, hu, hul⟩ := mem_closure_iff_seq_limit.mp (hd (h2.toLp f))
  choose g hg hgcompact hgsmooth using hu
  let φ : ℕ → MaximalTruncationData.Tests d := fun n =>
    { toFun := fun y => χ y * g n y
      contDiff' := χ.contDiff.mul (hgsmooth n)
      hasCompactSupport' := χ.hasCompactSupport.mul_right
      tsupport_subset' := subset_univ _ }
  have hφ (n : ℕ) : testMultiplier χ (u n) = testL2 (φ n) := by
    apply Lp.ext
    filter_upwards [testMultiplier_coe χ (u n), testL2_coe (φ n), hg n] with y hy hz hu
    calc
      _ = χ y * u n y := hy
      _ = χ y * g n y := congrArg (fun a => χ y * a) hu
      _ = _ := hz.symm
  have hχf : testMultiplier χ (h2.toLp f) = h2.toLp f := by
    apply Lp.ext
    filter_upwards [testMultiplier_coe χ (h2.toLp f), h2.coeFn_toLp, hs] with y hy hz hsy
    rw [hy]
    by_cases h : y ∈ S
    · simp [hχ h]
    · simp [hz, hsy h]
  have hlim : Tendsto (fun n => T (testL2 (φ n))) atTop (𝓝 (T (h2.toLp f))) := by
    have ht : Tendsto (fun n => T (testMultiplier χ (u n))) atTop
        (𝓝 (T (testMultiplier χ (h2.toLp f)))) :=
      (T.continuous.tendsto _).comp
        ((testMultiplier χ).continuous.tendsto _ |>.comp hul)
    simpa only [hφ, hχf] using ht
  obtain ⟨j, hj, hjlim⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hrep : ∀ᵐ x ∂volume, ∀ n, x ∉ tsupport χ →
      T (testL2 (φ n)) x = ∫ y, K (x - y) * φ n y := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [smooth_off_support hT (φ n)] with x hx hxc
    apply hx
    exact fun h => hxc (tsupport_mul_subset_left h)
  filter_upwards [hjlim, hrep] with x hxl hxr hx
  have hw := cutoff_weight_memLp hK χ x hx
  let P : CZWeak.L2 d →L[ℂ] ℂ :=
    (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2 (hw.toLp _)
  have hP (n : ℕ) : P (u n) = ∫ y, K (x - y) * φ n y := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp, hg n] with y hy hu
    simp [hy, hu, φ, mul_assoc]
  have hPf : P (h2.toLp f) = ∫ y, K (x - y) * f y := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp, h2.coeFn_toLp, hs] with y hy hz hsy
    simp only [hy, hz]
    by_cases h : y ∈ S
    · simp [hχ h]
    · simp [hsy h]
  have hp := (P.continuous.tendsto _).comp (hul.comp hj.tendsto_atTop)
  rw [hPf] at hp
  have hvalues : (fun n => T (testL2 (φ (j n))) x) = fun n => P (u (j n)) := by
    funext n
    exact (hxr (j n) hx).trans (hP (j n)).symm
  rw [hvalues] at hxl
  exact tendsto_nhds_unique hxl hp

/-- Countably many cutoff complements cover the exterior of the compact a.e.
support, making the exceptional set independent of the exterior point. -/
lemma compact_L2_off_support {K : Point d → ℂ} (T : Operator d)
    (hK : ContinuousOn K ({0}ᶜ : Set (Point d))) (hT : SmoothL2Action T K)
    (f : Point d → ℂ) (h2 : MemLp f 2 volume) (S : Set (Point d))
    (hS : IsCompact S) (hs : ∀ᵐ y ∂volume, y ∉ S → f y = 0) :
    ∀ᵐ x ∂volume, x ∉ S →
      T (h2.toLp f) x = ∫ y, K (x - y) * f y := by
  choose χ hχ hχaway using fun x : ↥(Sᶜ) =>
    cutoff_away_point (𝕜 := ℂ) S hS x.val x.property
  let U : ↥(Sᶜ) → Set (Point d) := fun i => (tsupport (χ i))ᶜ
  have hcover : Sᶜ ⊆ ⋃ i, U i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hχaway ⟨x, hx⟩⟩
  obtain ⟨c, hc, hcov⟩ :=
    (HereditarilyLindelofSpace.isLindelof Sᶜ).elim_countable_subcover U
      (fun i => (isClosed_tsupport (χ i)).isOpen_compl) hcover
  let : Countable c := hc.to_subtype
  have hall : ∀ᵐ x ∂volume, ∀ i : c, x ∈ U i.val →
      T (h2.toLp f) x = ∫ y, K (x - y) * f y :=
    ae_all_iff.mpr fun i => off_support_of_cutoff T hK hT f S h2 hs (χ i.val) (hχ i.val)
  filter_upwards [hall] with x hx hxs
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcov hxs)
  exact hx ⟨i, hi⟩ hxi

/-- Conditional derivation of one complete original target, with the frozen
premises in their required order. The full-extension premise is deliberately
retained even though this stage only needs the smooth-difference premise. -/
theorem kernel_representation_conditional :
    Specs.P102.U2.CZLp.full_extension →
    Specs.P102.U2.CZLp.smooth_difference →
    Specs.P102.U2.MaximalTruncation.kernel_representation := by
  intro _hFull hSmooth
  obtain ⟨C, hC⟩ := hSmooth
  refine ⟨C, ?_⟩
  intro d hd K B T hK hT
  constructor
  · refine ⟨?_, ?_, hC d hd K B hK.contDiff hK.gradient⟩
    · exact hK.contDiff.continuousOn.locallyIntegrableOn (measurableSet_singleton 0).compl
    · exact compact_L2_off_support T hK.contDiff.continuousOn hT
  · intro b h2 S hS hs x hx
    exact off_support_integrable hK.contDiff.continuousOn
      (integrable_of_compact_support_L2 h2 S hS hs) S hS hs x hx


/-- The homogeneous kernel has the necessary pointwise size bound; this is
proved from the original hypotheses rather than imposed as extra input data. -/
lemma homogeneous_size {K : Point d → ℂ} {B : ℝ≥0} (hK : KernelRegularity K B) :
    ∃ M : ℝ≥0, ∀ z : Point d, z ≠ 0 → ‖K z‖ ≤ (M : ℝ) / ‖z‖ ^ d := by
  have hc : ContinuousOn K (sphere (0 : Point d) 1) :=
    hK.contDiff.continuousOn.mono (by
      intro z hz
      change z ≠ 0
      intro he
      simp [he] at hz)
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Point d) 1).exists_bound_of_continuousOn hc
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro z hz
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let u : Point d := ‖z‖⁻¹ • z
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hz]
  have hus : u ∈ sphere (0 : Point d) 1 := by simpa using hu
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu
  have hzu : ‖z‖ • u = z := by simp [u, smul_smul, hnorm.ne']
  have heq := hK.homogeneous ‖z‖ hnorm u hu0
  rw [hzu] at heq
  rw [heq, norm_smul]
  have hbound : ‖K u‖ ≤ max C 0 := (hC u hus).trans (le_max_left _ _)
  calc
    ‖((‖z‖ ^ d)⁻¹ : ℝ)‖ * ‖K u‖ ≤ (‖z‖ ^ d)⁻¹ * max C 0 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by
      change (‖z‖ ^ d)⁻¹ * max C 0 = max C 0 / ‖z‖ ^ d
      rw [div_eq_mul_inv, mul_comm]

/-- Once all positive tails are absolutely integrable, radius continuity uses
only dominated convergence and the nullity of positive-radius spheres. -/
lemma truncated_continuousAt_radius (hd : 0 < d) (K f : Point d → ℂ)
    (x : Point d)
    (hi : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun y => K (x - y) * f y) {y | ε < ‖x - y‖} volume)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) : ContinuousAt (fun ε => truncated K f ε x) ε₀ := by
  let : NeZero d := ⟨hd.ne'⟩
  let F := fun y => K (x - y) * f y
  have hm (ε : ℝ) : MeasurableSet {y : Point d | ε < ‖x - y‖} := by measurability
  have hhalf : 0 < ε₀ / 2 := half_pos hε₀
  have hev : ∀ᶠ ε : ℝ in 𝓝 ε₀, ε₀ / 2 < ε :=
    eventually_gt_nhds (half_lt_self hε₀)
  change Tendsto _ _ _
  simp_rw [truncated, ← integral_indicator (hm _)]
  apply tendsto_integral_filter_of_dominated_convergence
    ({y : Point d | ε₀ / 2 < ‖x - y‖}.indicator (fun y => ‖F y‖))
  · filter_upwards [hev] with ε hε
    exact ((hi ε (hhalf.trans hε)).integrable_indicator (hm ε)).aestronglyMeasurable
  · filter_upwards [hev] with ε hε
    exact ae_of_all _ fun y => by
      rw [norm_indicator_eq_indicator_norm]
      exact indicator_le_indicator_of_subset
        (fun y hy => hε.trans hy) (fun y => norm_nonneg (F y)) y
  · have hn : IntegrableOn (fun y => ‖F y‖) {y | ε₀ / 2 < ‖x - y‖} volume :=
      (hi (ε₀ / 2) hhalf).norm
    exact hn.integrable_indicator (hm _)
  · have hnull : (volume : Measure (Point d)) (sphere x ε₀) = 0 :=
      Measure.addHaar_sphere_of_ne_zero volume x hε₀.ne'
    filter_upwards [compl_mem_ae_iff.mpr hnull] with y hy
    have hn : ‖x - y‖ ≠ ε₀ := by
      simpa [mem_sphere, dist_eq_norm_sub, norm_sub_rev] using hy
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have he : ∀ᶠ ε : ℝ in 𝓝 ε₀, ‖x - y‖ < ε := eventually_gt_nhds hlt
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with ε hε
      simp [not_lt.mpr hlt.le, not_lt.mpr hε.le]
    · have he : ∀ᶠ ε : ℝ in 𝓝 ε₀, ε < ‖x - y‖ := eventually_lt_nhds hgt
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with ε hε
      simp [hgt, hε]

lemma smooth_radius_continuous (hd : 0 < d) {K : Point d → ℂ}
    (hK : ContinuousOn K ({0}ᶜ : Set (Point d)))
    (φ : MaximalTruncationData.Tests d) (x : Point d) :
    ContinuousOn (fun ε => truncated K φ ε x) (Ioi 0) := by
  intro ε hε
  exact (truncated_continuousAt_radius hd K φ x
    (fun _ h => smooth_truncated_integrable hK φ x h) hε).continuousWithinAt

/-- Radius continuity justifies the countable supremum while preserving all
positive real radii in the original definition. -/
lemma maximalTruncation_eq_rat (K f : Point d → ℂ) (x : Point d)
    (hc : ContinuousOn (fun ε => truncated K f ε x) (Ioi 0)) :
    maximalTruncation K f x = ⨆ (q : ℚ) (_ : 0 < q), ‖truncated K f (q : ℝ) x‖ₑ := by
  apply le_antisymm
  · apply iSup_le
    intro ε
    apply iSup_le
    intro hε
    obtain ⟨u, _hu, hu, hul⟩ := Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
      (show Monotone (fun q : ℚ => (q : ℝ)) from Rat.cast_strictMono.monotone) hε
    have ht : Tendsto (fun n => ‖truncated K f (u n : ℝ) x‖ₑ) atTop
        (𝓝 ‖truncated K f ε x‖ₑ) := by
      apply Tendsto.enorm
      apply (hc ε hε).tendsto.comp
      exact tendsto_nhdsWithin_iff.mpr ⟨hul, Eventually.of_forall (fun n => (hu n).1)⟩
    apply le_of_tendsto ht
    exact Eventually.of_forall fun n =>
      le_iSup₂_of_le (u n) (by exact_mod_cast (hu n).1) le_rfl
  · apply iSup_le
    intro q
    apply iSup_le
    intro hq
    exact le_iSup₂_of_le (q : ℝ) (by exact_mod_cast hq) le_rfl


/-- Polar coordinates give the integrable radial majorant at infinity. -/
lemma radial_tail_integrable (hd : 0 < d) {a ε : ℝ}
    (ha : (d : ℝ) < a) (hε : 0 < ε) :
    IntegrableOn (fun z : Point d => ‖z‖ ^ (-a)) {z | ε < ‖z‖} volume := by
  let : NeZero d := ⟨hd.ne'⟩
  have hi : IntegrableOn (fun r : ℝ => r ^ ((d : ℝ) - 1 - a)) (Ioi ε) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hε
  have hind := hi.integrable_indicator measurableSet_Ioi
  have hpred : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  have hj : Integrable (fun z : Point d =>
      (Ioi ε).indicator (fun r : ℝ => r ^ (-a)) ‖z‖) volume := by
    apply (integrable_fun_norm_addHaar volume).mpr
    apply hind.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    by_cases he : ε < r
    · simp only [smul_eq_mul]
      rw [indicator_of_mem (show r ∈ Ioi ε from he),
        indicator_of_mem (show r ∈ Ioi ε from he)]
      have hdim : Module.finrank ℝ (Point d) = d := finrank_euclideanSpace_fin
      simp only [hdim, ← Real.rpow_natCast, hpred]
      rw [← Real.rpow_add hr]
      congr 1
    · simp [he]
  rw [← integrable_indicator_iff (by measurability :
    MeasurableSet {z : Point d | ε < ‖z‖})]
  convert hj using 1
  ext z
  simp [indicator]

/-- Every fixed positive cutoff of K belongs to every finite Lq with q>1.
This is the actual Hölder input for absolute convergence on arbitrary Lp. -/
lemma kernel_tail_memLp (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0}
    (hK : KernelRegularity K B) {q ε : ℝ} (hq : 1 < q) (hε : 0 < ε) :
    MemLp ({z : Point d | ε < ‖z‖}.indicator K) (ENNReal.ofReal q) volume := by
  let S := {z : Point d | ε < ‖z‖}
  have hS : MeasurableSet S := by measurability
  have hS0 : S ⊆ ({0}ᶜ : Set (Point d)) := by
    intro z hz
    change z ≠ 0
    intro he
    have := hε.trans hz
    simp [he] at this
  have hm : AEStronglyMeasurable (S.indicator K) volume :=
    (aestronglyMeasurable_indicator_iff hS).mpr
      ((hK.contDiff.continuousOn.mono hS0).aestronglyMeasurable hS)
  apply (integrable_norm_rpow_iff hm (by simp [show 0 < q by linarith]) (by simp)).mp
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ q)]
  obtain ⟨M, hM⟩ := homogeneous_size hK
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hdq : (d : ℝ) < (d : ℝ) * q := by
    nlinarith [show (0 : ℝ) < d by exact_mod_cast hd]
  have hr : IntegrableOn (fun z : Point d => ‖z‖ ^ (-((d : ℝ) * q))) S volume :=
    radial_tail_integrable hd hdq hε
  have hrI := hr.integrable_indicator hS
  apply (hrI.const_mul ((M : ℝ) ^ q)).mono'
    (hm.norm.aemeasurable.pow_const q).aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  by_cases hz : z ∈ S
  · have hz0 : z ≠ 0 := hS0 hz
    simp only [indicator_of_mem hz, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc
      ‖K z‖ ^ q ≤ ((M : ℝ) / ‖z‖ ^ d) ^ q :=
        Real.rpow_le_rpow (norm_nonneg _) (hM z hz0) hq0.le
      _ = (M : ℝ) ^ q * ‖z‖ ^ (-((d : ℝ) * q)) := by
        rw [Real.div_rpow M.coe_nonneg (by positivity), div_eq_mul_inv,
          Real.rpow_neg (norm_nonneg _)]
        rw [← Real.rpow_natCast ‖z‖ d, Real.rpow_mul (norm_nonneg _)]
  · simp [hz, ne_of_gt hq0]

/-- Hölder now proves absolute convergence at every center and every positive
radius for every Lp representative, with no maximal estimate assumed. -/
lemma lp_truncated_integrable (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0}
    (hK : KernelRegularity K B) (p : Exponent) {f : Point d → ℂ}
    (hf : MemLp f p.val volume) {ε : ℝ} (hε : 0 < ε) (x : Point d) :
    IntegrableOn (fun y => K (x - y) * f y) {y | ε < ‖x - y‖} volume := by
  let q := ENNReal.conjExponent p.val
  have hq : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p.val q).mp p.lt_top
  have hqt : q < ∞ := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p.val).mpr p.one_lt
  have hqr : 1 < q.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqt.ne).mpr hq
  have hk := kernel_tail_memLp hd hK hqr hε
  rw [ENNReal.ofReal_toReal hqt.ne] at hk
  have hj := (hk.comp_measurePreserving (volume.measurePreserving_sub_left x)).integrable_mul hf
  rw [← integrable_indicator_iff (by measurability :
    MeasurableSet {y : Point d | ε < ‖x - y‖})]
  apply hj.congr
  apply Eventually.of_forall
  intro y
  by_cases hy : ε < ‖x - y‖ <;> simp [hy, Function.comp_def]

lemma lp_radius_continuous (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0}
    (hK : KernelRegularity K B) (p : Exponent) {f : Point d → ℂ}
    (hf : MemLp f p.val volume) (x : Point d) :
    ContinuousOn (fun ε => truncated K f ε x) (Ioi 0) := by
  intro ε hε
  exact (truncated_continuousAt_radius hd K f x
    (fun _ h => lp_truncated_integrable hd hK p hf h x) hε).continuousWithinAt


/-- Pairing an Lp input against translates of a finite-Lq kernel is continuous.
This proves Borel measurability of each actual truncation, including for input
representatives which are only a.e. strongly measurable. -/
lemma continuous_kernel_convolution {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] {k f : Point d → ℂ}
    (hk : MemLp k q volume) (hf : MemLp f p volume) (hqt : q ≠ ∞) :
    Continuous (fun x : Point d => ∫ y, k (x - y) * f y) := by
  let g : Point d → C(Point d, Point d) :=
    fun x => ⟨fun y => x - y, continuous_const.sub continuous_id⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g (by
    change Continuous (fun z : Point d × Point d => z.1 - z.2)
    exact continuous_fst.sub continuous_snd)
  let v := fun x => Lp.compMeasurePreserving (g x)
    (volume.measurePreserving_sub_left x) (hk.toLp k)
  have hv : Continuous v := continuous_const.compMeasurePreservingLp hg
    (fun x => volume.measurePreserving_sub_left x) hqt
  let P : Lp ℂ q (volume : Measure (Point d)) →L[ℂ] ℂ :=
    (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume p q (hf.toLp f)
  have he (x : Point d) : P (v x) = ∫ y, k (x - y) * f y := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,
      Lp.coeFn_compMeasurePreserving (hk.toLp k) (volume.measurePreserving_sub_left x),
      (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae_eq_comp hk.coeFn_toLp]
      with y hfy hvy hky
    change (v x) y = (hk.toLp k) (x - y) at hvy
    change (hk.toLp k) (x - y) = k (x - y) at hky
    change (hf.toLp f) y * (v x) y = k (x - y) * f y
    rw [hfy, hvy, hky, mul_comm]
  simpa only [Function.comp_def, he] using P.continuous.comp hv

lemma lp_truncated_continuous (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0}
    (hK : KernelRegularity K B) (p : Exponent) {f : Point d → ℂ}
    (hf : MemLp f p.val volume) {ε : ℝ} (hε : 0 < ε) :
    Continuous (truncated K f ε) := by
  let q := ENNReal.conjExponent p.val
  have hq : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p.val q).mp p.lt_top
  have hqt : q < ∞ := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p.val).mpr p.one_lt
  let : Fact (1 ≤ q) := ⟨hq.le⟩
  have hqr : 1 < q.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqt.ne).mpr hq
  have hk := kernel_tail_memLp hd hK hqr hε
  rw [ENNReal.ofReal_toReal hqt.ne] at hk
  have hc := continuous_kernel_convolution hk hf hqt.ne
  have he (x : Point d) : (∫ y, {z : Point d | ε < ‖z‖}.indicator K (x - y) * f y) =
      truncated K f ε x := by
    rw [truncated, ← integral_indicator (by measurability :
      MeasurableSet {y : Point d | ε < ‖x - y‖})]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      by_cases hy : ε < ‖x - y‖ <;> simp [hy]
  simpa only [Function.comp_def, he] using hc

lemma lp_maximalTruncation_measurable (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0}
    (hK : KernelRegularity K B) (p : Exponent) {f : Point d → ℂ}
    (hf : MemLp f p.val volume) : Measurable (maximalTruncation K f) := by
  have he : maximalTruncation K f = fun x =>
      ⨆ (q : ℚ) (_ : 0 < q), ‖truncated K f (q : ℝ) x‖ₑ :=
    funext fun x => maximalTruncation_eq_rat K f x (lp_radius_continuous hd hK p hf x)
  rw [he]
  apply Measurable.iSup
  intro q
  apply Measurable.iSup
  intro hq
  exact (lp_truncated_continuous hd hK p hf (by exact_mod_cast hq)).enorm.measurable


/-- The complete realization target is proved directly; the two frozen
conditional premises are kept explicitly, in the required order. -/
theorem truncation_realization_conditional :
    Specs.P102.U2.CZLp.full_extension →
    Specs.P102.U2.CZLp.smooth_difference →
    Specs.P102.U2.MaximalTruncation.truncation_realization := by
  intro _hFull _hSmooth d hd K B hK p f hf
  refine ⟨?_, lp_maximalTruncation_measurable hd hK p hf,
    lp_radius_continuous hd hK p hf, ?_, ?_⟩
  · intro ε hε x
    exact lp_truncated_integrable hd hK p hf hε x
  · intro x
    exact maximalTruncation_eq_rat K f x (lp_radius_continuous hd hK p hf x)
  · intro g hfg
    exact ⟨truncated_congr_ae K hfg, maximalTruncation_congr_ae K hfg⟩

/-- The compact-L² representation under the original kernel and L² data. -/
theorem kernel_representation : Specs.P102.U2.MaximalTruncation.kernel_representation :=
  kernel_representation_conditional CZLp.full_extension CZLp.smooth_difference

/-- Absolute existence and measurability for every finite Lp above one. -/
theorem truncation_realization : Specs.P102.U2.MaximalTruncation.truncation_realization :=
  truncation_realization_conditional CZLp.full_extension CZLp.smooth_difference

/-- Polar coordinates as a product integral. This identity does not assume
integrability; its use below is for compact annular cutoffs. -/
lemma integral_polar_product (hd : 0 < d) (f : Point d → ℂ) :
    (∫ z, f z) =
      ∫ p : sphere (0 : Point d) 1 × Ioi (0 : ℝ), f (p.2.1 • p.1.1)
        ∂(volume : Measure (Point d)).toSphere.prod (Measure.volumeIoiPow (d - 1)) := by
  let : NeZero d := ⟨hd.ne'⟩
  calc
    (∫ z, f z) = ∫ z : ({0}ᶜ : Set (Point d)), f z.1 ∂volume.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = _ := by
      have h := (volume : Measure (Point d)).measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _)
        (fun p => f (((homeomorphUnitSphereProd (Point d)).symm p).1))
      simpa only [Function.comp_def, Homeomorph.symm_apply_apply,
        homeomorphUnitSphereProd_symm_apply_coe, finrank_euclideanSpace_fin] using h

/-- Homogeneity and the spherical mean zero give actual cancellation on every
bounded annulus, with arbitrary positive real inner radius. -/
lemma annular_cancellation {K : Point d → ℂ} {B : ℝ≥0}
    (hd : 0 < d) (hK : KernelRegularity K B) (ε R : ℝ) :
    (∫ z in {z : Point d | ε < ‖z‖ ∧ ‖z‖ < R}, K z) = 0 := by
  rw [← integral_indicator (by measurability :
    MeasurableSet {z : Point d | ε < ‖z‖ ∧ ‖z‖ < R}), integral_polar_product hd]
  have he (p : sphere (0 : Point d) 1 × Ioi (0 : ℝ)) :
      {z : Point d | ε < ‖z‖ ∧ ‖z‖ < R}.indicator K (p.2.1 • p.1.1) =
        K p.1.1 * (if ε < p.2.1 ∧ p.2.1 < R then ((p.2.1 ^ d)⁻¹ : ℝ) else 0) := by
    have hn : ‖p.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
    have hz : p.1.1 ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
    have hr : 0 < p.2.1 := p.2.2
    by_cases h : ε < p.2.1 ∧ p.2.1 < R
    · have hmem : p.2.1 • p.1.1 ∈ {z : Point d | ε < ‖z‖ ∧ ‖z‖ < R} := by
        simpa [norm_smul, abs_of_pos hr, hn] using h
      rw [indicator_of_mem hmem, ite_eq_left h, hK.homogeneous _ hr _ hz,
        Complex.real_smul, mul_comm]
    · simp [indicator, norm_smul, abs_of_pos hr, hn, h]
  simp_rw [he, apply_ite Complex.ofReal, Complex.ofReal_zero]
  exact (integral_prod_mul (μ := (volume : Measure (Point d)).toSphere)
    (ν := Measure.volumeIoiPow (d - 1)) (fun θ : sphere (0 : Point d) 1 => K θ.1)
    (fun r : Ioi (0 : ℝ) => ((if ε < r.1 ∧ r.1 < R then ((r.1 ^ d)⁻¹ : ℝ) else 0) : ℂ))).trans
      (by rw [hK.sphereMeanZero, zero_mul])

/-- Local subtraction of the smooth input removes the nonintegrable singularity. -/
lemma smooth_compensated_integrable (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0}
    (hK : KernelRegularity K B) (φ : MaximalTruncationData.Tests d) (x : Point d) :
    Integrable (fun z : Point d => K z *
      (φ (x - z) - (ball (0 : Point d) 1).indicator (fun _ => φ x) z)) volume := by
  let : NeZero d := ⟨hd.ne'⟩
  obtain ⟨M, hM⟩ := homogeneous_size hK
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    φ.hasCompactSupport φ.contDiff (by simp)
  have hmK : Measurable K := measurable_of_continuousOn_compl_singleton 0 hK.contDiff.continuousOn
  have hm : AEStronglyMeasurable (fun z : Point d => K z * (φ (x - z) - φ x)) volume :=
    (hmK.mul ((φ.continuous.comp (continuous_const.sub continuous_id)).measurable.sub
      measurable_const)).aestronglyMeasurable
  have hi : IntegrableOn (fun z : Point d => K z * (φ (x - z) - φ x)) (ball 0 1) volume := by
    apply integrableOn_ball_of_norm_le_rpow (by simpa using (show 1 ≤ d by omega) : 1 ≤ Module.finrank ℝ (Point d))
      (α := (d : ℝ) - 1) (C := M * L) (by simp)
      _ hm
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : Point d))] with z hz
    have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hl : ‖φ (x - z) - φ x‖ ≤ L * ‖z‖ := by
      simpa [dist_eq_norm, sub_sub_cancel_left] using hL.dist_le_mul (x - z) x
    calc
      ‖K z * (φ (x - z) - φ x)‖ = ‖K z‖ * ‖φ (x - z) - φ x‖ := norm_mul _ _
      _ ≤ ((M : ℝ) / ‖z‖ ^ d) * ((L : ℝ) * ‖z‖) :=
        mul_le_mul (hM z hz) hl (norm_nonneg _) (by positivity)
      _ = (M : ℝ) * L * ‖z‖ ^ (-((d : ℝ) - 1)) := by
        rw [← Real.rpow_natCast, div_eq_mul_inv, ← Real.rpow_neg hp.le,
          show -((d : ℝ) - 1) = -(d : ℝ) + 1 by ring, Real.rpow_add hp, Real.rpow_one]
        ring
  have ht := smooth_truncated_integrable hK.contDiff.continuousOn φ x (by norm_num : (0 : ℝ) < 1 / 2)
  have ht' : IntegrableOn (fun z : Point d => K z * φ (x - z)) {z | 1 / 2 < ‖z‖} volume := by
    rw [← integrable_indicator_iff (by measurability)] at ht ⊢
    have hh := (volume.measurePreserving_sub_left x).integrable_comp_emb
      (Homeomorph.subLeft x).measurableEmbedding
      (g := {z : Point d | 1 / 2 < ‖z‖}.indicator (fun z => K z * φ (x - z)))
    apply hh.mp
    convert ht using 1
    ext y
    simp [indicator, sub_sub_cancel]
  have hc : IntegrableOn (fun z : Point d => K z * φ (x - z)) (ball (0 : Point d) 1)ᶜ volume :=
    ht'.mono_set (by intro z hz; simp only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] at hz; dsimp; linarith)
  have htotal := (hi.integrable_indicator measurableSet_ball).add
    (hc.integrable_indicator measurableSet_ball.compl)
  apply htotal.congr
  exact ae_of_all _ fun z => by
    by_cases hz : z ∈ ball (0 : Point d) 1 <;> simp [hz]

/-- The annular integral is absolutely defined whenever its inner radius is positive. -/
lemma annular_integrable {K : Point d → ℂ}
    (hK : ContinuousOn K ({0}ᶜ : Set (Point d))) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    IntegrableOn K {z : Point d | ε < ‖z‖ ∧ ‖z‖ < R} volume := by
  let S := closedBall (0 : Point d) R ∩ {z : Point d | ε ≤ ‖z‖}
  have hS : IsCompact S := (isCompact_closedBall (0 : Point d) R).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hc : ContinuousOn K S := hK.mono (by
    intro z hz
    change z ≠ 0
    exact norm_pos_iff.mp (hε.trans_le hz.2))
  exact (hc.integrableOn_compact hS).mono_set (by
    intro z hz
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hz.2.le, hz.1.le⟩)

/-- Reflection and translation put the truncation into radial kernel coordinates. -/
lemma truncated_eq_reflected (K f : Point d → ℂ) (ε : ℝ) (x : Point d) :
    truncated K f ε x = ∫ z in {z : Point d | ε < ‖z‖}, K z * f (x - z) := by
  rw [truncated, ← integral_indicator (by measurability :
    MeasurableSet {y : Point d | ε < ‖x - y‖}),
    ← integral_indicator (by measurability : MeasurableSet {z : Point d | ε < ‖z‖})]
  have h := (volume.measurePreserving_sub_left x).integral_comp
    (Homeomorph.subLeft x).measurableEmbedding
    ({z : Point d | ε < ‖z‖}.indicator (fun z => K z * f (x - z)))
  rw [← h]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by simp [indicator, sub_sub_cancel]

/-- Every positive truncation equals the corresponding truncation of the
absolutely integrable compensated kernel. -/
lemma truncated_compensated (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0}
    (hK : KernelRegularity K B) (φ : MaximalTruncationData.Tests d) (x : Point d)
    {ε : ℝ} (hε : 0 < ε) :
    truncated K φ ε x = ∫ z in {z : Point d | ε < ‖z‖},
      K z * (φ (x - z) - (ball (0 : Point d) 1).indicator (fun _ => φ x) z) := by
  let A := {z : Point d | ε < ‖z‖}
  let D := {z : Point d | ε < ‖z‖ ∧ ‖z‖ < 1}
  let F := fun z : Point d => K z *
    (φ (x - z) - (ball (0 : Point d) 1).indicator (fun _ => φ x) z)
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hD : MeasurableSet D := by dsimp [D]; measurability
  have hF := smooth_compensated_integrable hd hK φ x
  have hDK : IntegrableOn (fun z => K z * φ x) D volume :=
    (annular_integrable hK.contDiff.continuousOn hε 1).mul_const (φ x)
  have hG : IntegrableOn (D.indicator (fun z => K z * φ x)) A volume :=
    (hDK.integrable_indicator hD).integrableOn
  rw [truncated_eq_reflected]
  calc
    _ = ∫ z in A, F z + D.indicator (fun z => K z * φ x) z := by
      apply setIntegral_congr_fun hA
      intro z hz
      by_cases hb : z ∈ ball (0 : Point d) 1
      · have hzD : z ∈ D := ⟨hz, by simpa using hb⟩
        simp [F, hb, hzD, mul_sub]
      · have hzD : z ∉ D := by
          intro hzD
          exact hb (by simpa using hzD.2)
        simp [F, hb, hzD]
    _ = (∫ z in A, F z) + ∫ z in A, D.indicator (fun z => K z * φ x) z :=
      integral_add hF.integrableOn hG
    _ = ∫ z in A, F z := by
      have hh : (∫ z in A, D.indicator (fun z => K z * φ x) z) = 0 := by
        rw [setIntegral_indicator hD, inter_eq_right.mpr (show D ⊆ A from fun _ h => h.1),
          integral_mul_const, annular_cancellation hd hK ε 1, zero_mul]
      rw [hh, add_zero]

/-- Smooth principal values exist at every center, including inside the support. -/
theorem smooth_principal_value : Specs.P102.U2.MaximalTruncation.smooth_principal_value := by
  intro d hd K B hK φ x
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨fun ε hε => smooth_truncated_integrable hK.contDiff.continuousOn φ x hε, ?_⟩
  let F := fun z : Point d => K z *
    (φ (x - z) - (ball (0 : Point d) 1).indicator (fun _ => φ x) z)
  have hi : Integrable F volume := smooth_compensated_integrable hd hK φ x
  have ht : Tendsto (fun ε : ℝ => ∫ z in {z : Point d | ε < ‖z‖}, F z)
      (𝓝[>] 0) (𝓝 (∫ z, F z)) := by
    have hmE (ε : ℝ) : MeasurableSet {z : Point d | ε < ‖z‖} := by measurability
    simp_rw [← integral_indicator (hmE _)]
    apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖F z‖)
    · exact Eventually.of_forall fun ε =>
        (hi.indicator (by measurability)).aestronglyMeasurable
    · exact Eventually.of_forall fun ε => ae_of_all _ fun z => norm_indicator_le_norm_self _ _
    · exact hi.norm
    · filter_upwards [volume.ae_ne (0 : Point d)] with z hz
      have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
      apply tendsto_const_nhds.congr'
      filter_upwards [(eventually_lt_nhds hp).filter_mono nhdsWithin_le_nhds] with ε hε
      simp [hε]
  have he : (fun ε => truncated K φ ε x) =ᶠ[𝓝[>] 0]
      (fun ε => ∫ z in {z : Point d | ε < ‖z‖}, F z) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact truncated_compensated hd hK φ x hε
  have ht' := ht.congr' he.symm
  have hv : principalValue K φ x = ∫ z, F z := ht'.limUnder_eq
  rw [hv]
  exact ht'

/-- At a fixed positive radius and center, the truncation is a continuous
linear pairing on Lp. In particular no exceptional set of centers is needed. -/
lemma truncated_tendsto_Lp (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0}
    (hK : KernelRegularity K B) (p : Exponent)
    (u : ℕ → Point d → ℂ) (hu : ∀ n, MemLp (u n) p.val volume)
    (f : Point d → ℂ) (hf : MemLp f p.val volume)
    (ht : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hf.toLp f)))
    {ε : ℝ} (hε : 0 < ε) (x : Point d) :
    Tendsto (fun n => truncated K (u n) ε x) atTop (𝓝 (truncated K f ε x)) := by
  let q := ENNReal.conjExponent p.val
  have hq : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p.val q).mp p.lt_top
  have hqt : q < ∞ := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p.val).mpr p.one_lt
  let : Fact (1 ≤ q) := ⟨hq.le⟩
  have hqr : 1 < q.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqt.ne).mpr hq
  have hk := kernel_tail_memLp hd hK hqr hε
  rw [ENNReal.ofReal_toReal hqt.ne] at hk
  have hw := hk.comp_measurePreserving (volume.measurePreserving_sub_left x)
  let P : CZLpData.Space d p.val →L[ℂ] ℂ :=
    (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume q p.val (hw.toLp _)
  have he (g : Point d → ℂ) (hg : MemLp g p.val volume) :
      P (hg.toLp g) = truncated K g ε x := by
    rw [ContinuousLinearMap.lpPairing_eq_integral, truncated,
      ← integral_indicator (by measurability : MeasurableSet {y : Point d | ε < ‖x - y‖})]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp, hg.coeFn_toLp] with y hy hgy
    rw [hy, hgy]
    by_cases hyε : ε < ‖x - y‖ <;> simp [hyε]
  simpa only [Function.comp_def, he] using P.continuous.tendsto _ |>.comp ht

/-- Pointwise lower semicontinuity of the full supremum under Lp approximation. -/
lemma maximalTruncation_le_liminf (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0}
    (hK : KernelRegularity K B) (p : Exponent)
    (u : ℕ → Point d → ℂ) (hu : ∀ n, MemLp (u n) p.val volume)
    (f : Point d → ℂ) (hf : MemLp f p.val volume)
    (ht : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hf.toLp f))) (x : Point d) :
    maximalTruncation K f x ≤ liminf (fun n => maximalTruncation K (u n) x) atTop := by
  apply iSup_le
  intro ε
  apply iSup_le
  intro hε
  have hl := (truncated_tendsto_Lp hd hK p u hu f hf ht hε x).enorm
  rw [← hl.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun n => le_iSup₂_of_le ε hε le_rfl)

/-- Fatou and smooth Lp density transfer a uniform test-function maximal bound
to every representative in Lp, preserving its constant. -/
lemma maximal_moment_bound_of_tests (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0}
    (hK : KernelRegularity K B) (p : Exponent) (C : ℝ≥0)
    (hC : ∀ φ : MaximalTruncationData.Tests d,
      (∫⁻ x, maximalTruncation K φ x ^ p.val.toReal) ^ (1 / p.val.toReal) ≤
        (C : ℝ≥0∞) * eLpNorm φ p.val volume)
    (f : Point d → ℂ) (hf : MemLp f p.val volume) :
    (∫⁻ x, maximalTruncation K f x ^ p.val.toReal) ^ (1 / p.val.toReal) ≤
      (C : ℝ≥0∞) * eLpNorm f p.val volume := by
  have hp0 : p.val ≠ 0 := ne_of_gt (zero_lt_one.trans p.one_lt)
  have hr : 0 < p.val.toReal := ENNReal.toReal_pos hp0 p.lt_top.ne
  obtain ⟨v, hv, hvl⟩ := mem_closure_iff_seq_limit.mp
    (Lp.dense_hasCompactSupport_contDiff (F := ℂ) (μ := (volume : Measure (Point d)))
      (p := p.val) p.lt_top.ne (hf.toLp f))
  choose g hg hgc hgs using hv
  let φ : ℕ → MaximalTruncationData.Tests d := fun n =>
    { toFun := g n
      contDiff' := hgs n
      hasCompactSupport' := hgc n
      tsupport_subset' := subset_univ _ }
  have hφ (n : ℕ) : MemLp (φ n) p.val volume :=
    (φ n).continuous.memLp_of_hasCompactSupport (φ n).hasCompactSupport
  have hvφ (n : ℕ) : (hφ n).toLp (φ n) = v n := by
    apply Lp.ext
    exact (hφ n).coeFn_toLp.trans (hg n).symm
  have hφlim : Tendsto (fun n => (hφ n).toLp (φ n)) atTop (𝓝 (hf.toLp f)) := by
    simpa only [hvφ] using hvl
  have hn : Tendsto (fun n => eLpNorm (φ n) p.val volume) atTop
      (𝓝 (eLpNorm f p.val volume)) := by
    simpa only [Lp.enorm_toLp] using hφlim.enorm
  have hb (n : ℕ) : (∫⁻ x, maximalTruncation K (φ n) x ^ p.val.toReal) ≤
      ((C : ℝ≥0∞) * eLpNorm (φ n) p.val volume) ^ p.val.toReal := by
    exact (ENNReal.rpow_inv_le_iff hr).mp (by simpa only [one_div] using hC (φ n))
  have hpoint (x : Point d) : maximalTruncation K f x ^ p.val.toReal ≤
      liminf (fun n => maximalTruncation K (φ n) x ^ p.val.toReal) atTop := by
    have he : (liminf (fun n => maximalTruncation K (φ n) x) atTop) ^ p.val.toReal =
        liminf (fun n => maximalTruncation K (φ n) x ^ p.val.toReal) atTop := by
      exact (ENNReal.orderIsoRpow p.val.toReal hr).liminf_apply
        (by isBoundedDefault) (by isBoundedDefault) (by isBoundedDefault) (by isBoundedDefault)
    rw [← he]
    exact ENNReal.rpow_le_rpow (maximalTruncation_le_liminf hd hK p (fun n => (φ n : Point d → ℂ)) hφ f hf hφlim x) hr.le
  have hlim := (ENNReal.continuous_rpow_const (y := p.val.toReal)).tendsto
    ((C : ℝ≥0∞) * eLpNorm f p.val volume) |>.comp
      (ENNReal.Tendsto.const_mul hn (Or.inr ENNReal.coe_ne_top))
  simp only [one_div]
  apply (ENNReal.rpow_inv_le_iff hr).mpr
  calc
    (∫⁻ x, maximalTruncation K f x ^ p.val.toReal) ≤
        ∫⁻ x, liminf (fun n => maximalTruncation K (φ n) x ^ p.val.toReal) atTop :=
      lintegral_mono hpoint
    _ ≤ liminf (fun n => ∫⁻ x, maximalTruncation K (φ n) x ^ p.val.toReal) atTop :=
      lintegral_liminf_le fun n => (lp_maximalTruncation_measurable hd hK p (hφ n)).pow_const _
    _ ≤ liminf (fun n => ((C : ℝ≥0∞) * eLpNorm (φ n) p.val volume) ^ p.val.toReal) atTop :=
      liminf_le_liminf (Eventually.of_forall hb)
    _ = _ := hlim.liminf_eq

/-- An extended maximal moment estimate entails a.e. finiteness and the usual
Lp bound for the real representative. -/
lemma maximal_membership_of_moment (hd : 0 < d) {K : Point d → ℂ} {B : ℝ≥0}
    (hK : KernelRegularity K B) (p : Exponent) (C : ℝ≥0)
    (f : Point d → ℂ) (hf : MemLp f p.val volume)
    (hb : (∫⁻ x, maximalTruncation K f x ^ p.val.toReal) ^ (1 / p.val.toReal) ≤
      (C : ℝ≥0∞) * eLpNorm f p.val volume) :
    (∀ᵐ x ∂volume, maximalTruncation K f x < ∞) ∧
    MemLp (fun x => (maximalTruncation K f x).toReal) p.val volume ∧
    eLpNorm (fun x => (maximalTruncation K f x).toReal) p.val volume ≤
      (C : ℝ≥0∞) * eLpNorm f p.val volume := by
  have hp0 : p.val ≠ 0 := ne_of_gt (zero_lt_one.trans p.one_lt)
  have hr : 0 < p.val.toReal := ENNReal.toReal_pos hp0 p.lt_top.ne
  have hbound : (∫⁻ x, maximalTruncation K f x ^ p.val.toReal) ^ (1 / p.val.toReal) < ∞ :=
    hb.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.eLpNorm_lt_top)
  have hint : (∫⁻ x, maximalTruncation K f x ^ p.val.toReal) < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.mpr hr)).mp hbound
  have hm := lp_maximalTruncation_measurable hd hK p hf
  have hfinite : ∀ᵐ x ∂volume, maximalTruncation K f x < ∞ := by
    filter_upwards [ae_lt_top (hm.pow_const p.val.toReal) hint.ne] with x hx
    exact (ENNReal.rpow_lt_top_iff_of_pos hr).mp hx
  have hg : AEStronglyMeasurable (fun x => (maximalTruncation K f x).toReal) volume :=
    hm.ennreal_toReal.aestronglyMeasurable
  have heq : eLpNorm (fun x => (maximalTruncation K f x).toReal) p.val volume =
      (∫⁻ x, maximalTruncation K f x ^ p.val.toReal) ^ (1 / p.val.toReal) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 p.lt_top.ne hg]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hfinite] with x hx
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hx.ne]
  exact ⟨hfinite, by show eLpNorm _ _ _ < ∞; rw [heq]; exact hbound,
    by rw [heq]; exact hb⟩

lemma tail_ball_mass {d : ℕ} (f : Point d → ℂ) (x : Point d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in ball x r, ‖f y‖ₑ) ≤ centeredMaximal f x * volume (ball x r) := by
  have h := le_iSup₂ (f := fun (r : ℝ) (_ : 0 < r) =>
    (∫⁻ y in ball x r, ‖f y‖ₑ) / volume (ball x r)) r hr
  exact (ENNReal.div_le_iff (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne).mp h

lemma tail_shell_factor {d : ℕ} {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (ε * 2 ^ (n + 1)) ^ d / (ε * 2 ^ n) ^ (d + 1) =
      (2 : ℝ) ^ d / ε * (1 / 2 : ℝ) ^ n := by
  have hp : 0 < ε * (2 : ℝ) ^ n := by positivity
  rw [pow_succ (2 : ℝ) n]
  rw [show ε * ((2 : ℝ)^n * 2) = 2 * (ε * 2^n) by ring, mul_pow,
    pow_succ (ε * (2 : ℝ)^n) d]
  rw [div_mul_eq_div_mul_one_div, one_div_pow]
  field_simp

lemma maximal_weighted_tail {d : ℕ} (f : Point d → ℂ) (x : Point d)
    {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ u in {u : Point d | ε < ‖x-u‖},
      ‖f u‖ₑ / ENNReal.ofReal (‖x-u‖ ^ (d+1))) ≤
      ENNReal.ofReal ((2 : ℝ)^(d+1) * volume.real (ball (0 : Point d) 1) / ε) *
        centeredMaximal f x := by
  let r : ℕ → ℝ := fun n => ε * 2^n
  let S : ℕ → Set (Point d) := fun n => {u | r n ≤ ‖x-u‖ ∧ ‖x-u‖ < r (n+1)}
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hcov : {u : Point d | ε < ‖x-u‖} ⊆ ⋃ n, S n := by
    intro u hu
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near (show 1 ≤ ‖x-u‖ / ε by exact (le_div_iff₀ hε).mpr (by simpa using hu.le)) (by norm_num : (1 : ℝ) < 2)
    apply mem_iUnion.mpr
    refine ⟨n, ?_, ?_⟩
    · simpa [r, mul_comm] using (le_div_iff₀ hε).mp hn
    · simpa [r, mul_comm] using (div_lt_iff₀ hε).mp hn'
  have hlocal (n : ℕ) :
      (∫⁻ u in S n, ‖f u‖ₑ / ENNReal.ofReal (‖x-u‖ ^ (d+1))) ≤
        ENNReal.ofReal ((2 : ℝ)^d / ε * (1/2 : ℝ)^n) *
          volume (ball (0 : Point d) 1) * centeredMaximal f x := by
    calc
      _ ≤ ∫⁻ u in S n, ‖f u‖ₑ / ENNReal.ofReal ((r n) ^ (d+1)) := by
        apply setLIntegral_mono' (by dsimp [S]; measurability)
        intro u hu
        apply ENNReal.div_le_div_left
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hr n).le hu.1 _)
      _ = (∫⁻ u in S n, ‖f u‖ₑ) / ENNReal.ofReal ((r n) ^ (d+1)) := by
        simp only [div_eq_mul_inv]
        exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (hr n) _)))
      _ ≤ (∫⁻ u in ball x (r (n+1)), ‖f u‖ₑ) / ENNReal.ofReal ((r n) ^ (d+1)) := by
        apply ENNReal.div_le_div_right
        apply lintegral_mono_set
        intro u hu
        simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hu.2
      _ ≤ (centeredMaximal f x * volume (ball x (r (n+1)))) /
          ENNReal.ofReal ((r n) ^ (d+1)) :=
        ENNReal.div_le_div_right (tail_ball_mass f x (hr (n+1))) _
      _ = _ := by
        rw [Measure.addHaar_ball_of_pos volume x (hr (n+1)), finrank_euclideanSpace_fin]
        calc
          _ = (ENNReal.ofReal ((r (n+1))^d) / ENNReal.ofReal ((r n)^(d+1))) *
              volume (ball (0 : Point d) 1) * centeredMaximal f x := by
            simp only [div_eq_mul_inv]; ac_rfl
          _ = _ := by
            rw [← ENNReal.ofReal_div_of_pos (pow_pos (hr n) _), tail_shell_factor hε n]

  calc
    _ ≤ ∫⁻ u in ⋃ n, S n, ‖f u‖ₑ / ENNReal.ofReal (‖x-u‖ ^ (d+1)) := lintegral_mono_set hcov
    _ ≤ ∑' n, ∫⁻ u in S n, ‖f u‖ₑ / ENNReal.ofReal (‖x-u‖ ^ (d+1)) := lintegral_iUnion_le _ _
    _ ≤ ∑' n, ENNReal.ofReal ((2 : ℝ)^d / ε * (1/2 : ℝ)^n) *
          volume (ball (0 : Point d) 1) * centeredMaximal f x := ENNReal.tsum_le_tsum hlocal
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ)^d / ε), ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/2)]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left,
        ENNReal.tsum_geometric]
      norm_num [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_ofNat, ENNReal.sub_half] at *
      have he : ENNReal.ofReal ((2 : ℝ)^d / ε) * 2 =
          ENNReal.ofReal ((2 : ℝ)^d / ε * 2) := by
        simpa only [ENNReal.ofReal_ofNat] using
          (ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ)^d / ε) (q := 2)).symm
      rw [he, ← ofReal_measureReal (measure_ball_lt_top.ne),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [pow_succ]
      ring

lemma test_moment_bound_aux (d : ℕ) (p : Exponent) (A L : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (K g : Point d → ℂ) (φ : MaximalTruncationData.Tests d),
    MemLp g p.val volume →
    eLpNorm g p.val volume ≤ (L : ℝ≥0∞) * eLpNorm φ p.val volume →
    (∀ᵐ x ∂volume, maximalTruncation K φ x ≤ (A : ℝ≥0∞) *
      ((centeredMaximal (fun y => ‖g y‖ ^ (1 / 2 : ℝ)) x) ^ (2 : ℝ) +
        centeredMaximal (φ : Point d → ℂ) x)) →
    (∫⁻ x, maximalTruncation K φ x ^ p.val.toReal) ^ (1 / p.val.toReal) ≤
      (C : ℝ≥0∞) * eLpNorm φ p.val volume := by
  have hp0 : p.val ≠ 0 := ne_of_gt (zero_lt_one.trans p.one_lt)
  have hpr : 1 < p.val.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top p.lt_top.ne).mpr p.one_lt
  have hpr0 : 0 < p.val.toReal := zero_lt_one.trans hpr
  have hpr2 : 1 < 2 * p.val.toReal := by linarith
  have hpval : ENNReal.ofReal p.val.toReal = p.val := ENNReal.ofReal_toReal p.lt_top.ne
  obtain ⟨C₁, hC₁⟩ := ExpandedFA.SingularIntegrals.centeredMaximal_strong_finite d p.val.toReal hpr
  obtain ⟨C₂, hC₂⟩ := ExpandedFA.SingularIntegrals.centeredMaximal_strong_finite d (2 * p.val.toReal) hpr2
  refine ⟨A * (C₂ ^ 2 * L + C₁), ?_⟩
  intro K g φ hg hgn hCot
  have hexp : ENNReal.ofReal (2 * p.val.toReal) * ENNReal.ofReal (1 / 2 : ℝ) = p.val := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    calc
      ENNReal.ofReal (2 * p.val.toReal * (1 / 2 : ℝ)) = ENNReal.ofReal p.val.toReal := by
        congr 1
        ring
      _ = p.val := hpval
  have hnorm : eLpNorm (fun y => ‖g y‖ ^ (1 / 2 : ℝ)) (ENNReal.ofReal (2 * p.val.toReal)) volume =
      eLpNorm g p.val volume ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_norm_rpow g hg.aestronglyMeasurable (by norm_num : (0 : ℝ) < 1 / 2), hexp]
  have hs : MemLp (fun y => ‖g y‖ ^ (1 / 2 : ℝ)) (ENNReal.ofReal (2 * p.val.toReal)) volume := by
    rw [memLp_iff, hnorm]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hg.ne
  have hb₂ := hC₂ (fun y => ‖g y‖ ^ (1 / 2 : ℝ)) hs
  rw [hnorm] at hb₂
  have hb₁ := hC₁ (φ : Point d → ℂ)
    (by rw [hpval]; exact φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)
  rw [hpval] at hb₁
  let F : Point d → ℝ≥0∞ := fun x => centeredMaximal (fun y => ‖g y‖ ^ (1 / 2 : ℝ)) x ^ (2 : ℝ)
  let G : Point d → ℝ≥0∞ := centeredMaximal (φ : Point d → ℂ)
  have hmF : Measurable F := (ExpandedFA.SingularIntegrals.centeredMaximal_measurable d _).pow_const _
  have hmG : Measurable G := ExpandedFA.SingularIntegrals.centeredMaximal_measurable d _
  have hF : (∫⁻ x, F x ^ p.val.toReal) ^ (1 / p.val.toReal) ≤
      (C₂ : ℝ≥0∞) ^ (2 : ℝ) * eLpNorm g p.val volume := by
    have hh := ENNReal.rpow_le_rpow hb₂ (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [F, ← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
      show 1 / (2 * p.val.toReal) * 2 = 1 / p.val.toReal by field_simp] using hh
  calc
    (∫⁻ x, maximalTruncation K φ x ^ p.val.toReal) ^ (1 / p.val.toReal) ≤
        (∫⁻ x, ((A : ℝ≥0∞) * (F x + G x)) ^ p.val.toReal) ^ (1 / p.val.toReal) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      exact lintegral_mono_ae (hCot.mono fun x hx => ENNReal.rpow_le_rpow hx hpr0.le)
    _ = (A : ℝ≥0∞) * (∫⁻ x, (F x + G x) ^ p.val.toReal) ^ (1 / p.val.toReal) := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hpr0.le]
      rw [lintegral_const_mul _ (show Measurable (fun x => (F x + G x) ^ p.val.toReal) from (hmF.add hmG).pow_const _),
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        mul_one_div_cancel hpr0.ne', ENNReal.rpow_one]
    _ ≤ (A : ℝ≥0∞) * ((∫⁻ x, F x ^ p.val.toReal) ^ (1 / p.val.toReal) +
        (∫⁻ x, G x ^ p.val.toReal) ^ (1 / p.val.toReal)) := by
      exact mul_le_mul_of_nonneg_left (ENNReal.lintegral_Lp_add_le hmF.aemeasurable hmG.aemeasurable hpr.le) (by positivity)
    _ ≤ (A : ℝ≥0∞) * ((C₂ : ℝ≥0∞) ^ (2 : ℝ) * ((L : ℝ≥0∞) * eLpNorm φ p.val volume) +
        (C₁ : ℝ≥0∞) * eLpNorm φ p.val volume) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (hF.trans (mul_le_mul_of_nonneg_left hgn (by positivity))) hb₁) (by positivity)
    _ = _ := by
      simp only [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_pow, ENNReal.rpow_two]
      ring


lemma strong_test_bound {T : Operator d} {p : Exponent}
    (R : StrongOperator d p) (hR : Agrees T p R) (L : ℝ≥0) (hL : ‖R‖ ≤ L)
    (φ : MaximalTruncationData.Tests d) :
    MemLp (T (testL2 φ) : Point d → ℂ) p.val volume ∧
    eLpNorm (T (testL2 φ) : Point d → ℂ) p.val volume ≤
      (L : ℝ≥0∞) * eLpNorm φ p.val volume := by
  have hφ : MemLp (φ : Point d → ℂ) p.val volume :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hφ2 : MemLp (φ : Point d → ℂ) 2 volume :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have he := hR (φ : Point d → ℂ) hφ hφ2
  change (R (hφ.toLp φ) : Point d → ℂ) =ᵐ[volume] (T (testL2 φ) : Point d → ℂ) at he
  refine ⟨(Lp.memLp (R (hφ.toLp φ))).ae_eq he, ?_⟩
  rw [← eLpNorm_congr_ae he, ← Lp.enorm_def]
  have hLe : ‖R‖ₑ ≤ (L : ℝ≥0∞) := by
    exact_mod_cast hL
  calc
    ‖R (hφ.toLp φ)‖ₑ ≤ ‖R‖ₑ * ‖hφ.toLp φ‖ₑ := R.le_opENorm _
    _ ≤ (L : ℝ≥0∞) * eLpNorm φ p.val volume := by
      rw [Lp.enorm_toLp]
      gcongr

/-- The test bound from Cotlar, followed by Lp density and Fatou. -/
theorem maximal_bound_conditional
    (hCot : Specs.P102.U2.MaximalTruncation.cotlar)
    (hKer : Specs.P102.U2.MaximalTruncation.kernel_representation) :
    Specs.P102.U2.MaximalTruncation.maximal_bound := by
  obtain ⟨A, hA⟩ := hCot
  obtain ⟨D, hD⟩ := hKer
  obtain ⟨C₁, L, hL⟩ := CZLp.full_extension
  have hAux (d : ℕ) (K : Point d → ℂ) (B N : ℝ≥0) (p : Exponent) :=
    test_moment_bound_aux d p (A d K B N (1 / 2)) (L d p (D d * B) N)
  choose C hC using hAux
  refine ⟨C, ?_⟩
  intro d hd K B T hK hT p f hf
  obtain ⟨_, S, R, _, _, _, _, _, _, hRn, hRA, _, _⟩ :=
    hL d hd T K (D d * B) (hD d hd K B T hK hT).1
  have ht (φ : MaximalTruncationData.Tests d) :
      (∫⁻ x, maximalTruncation K φ x ^ p.val.toReal) ^ (1 / p.val.toReal) ≤
        (C d K B ‖T‖₊ p : ℝ≥0∞) * eLpNorm φ p.val volume := by
    have hs := strong_test_bound (R p) (hRA p) (L d p (D d * B) ‖T‖₊) (hRn p) φ
    apply hC d K B ‖T‖₊ p K (T (testL2 φ)) φ hs.1 hs.2
    simpa only [show (1 / (1 / 2 : ℝ)) = 2 by norm_num] using
      hA d hd K B T hK hT (1 / 2) (by norm_num) (by norm_num) φ
  have hb := maximal_moment_bound_of_tests hd hK p (C d K B ‖T‖₊ p) ht f hf
  exact ⟨hb, maximal_membership_of_moment hd hK p (C d K B ‖T‖₊ p) f hf hb⟩


lemma test_near_memLp (φ : MaximalTruncationData.Tests d) (x : Point d) (ε : ℝ)
    (p : ℝ≥0∞) : MemLp ((ball x ε).indicator (φ : Point d → ℂ)) p volume := by
  exact (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).indicator
    measurableSet_ball.nullMeasurableSet

lemma test_far_memLp (φ : MaximalTruncationData.Tests d) (x : Point d) (ε : ℝ)
    (p : ℝ≥0∞) : MemLp ((φ : Point d → ℂ) - (ball x ε).indicator φ) p volume := by
  exact (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).sub
    (test_near_memLp φ x ε p)

lemma test_far_support_compact (φ : MaximalTruncationData.Tests d) (x : Point d) (ε : ℝ) :
    IsCompact (tsupport φ ∩ (ball x ε)ᶜ) :=
  φ.hasCompactSupport.inter_right isOpen_ball.isClosed_compl

lemma test_far_eq_zero (φ : MaximalTruncationData.Tests d) (x : Point d) (ε : ℝ)
    (y : Point d) (hy : y ∉ tsupport φ ∩ (ball x ε)ᶜ) :
    φ y - (ball x ε).indicator (φ : Point d → ℂ) y = 0 := by
  by_cases hb : y ∈ ball x ε
  · simp [hb]
  · have hs : y ∉ tsupport φ := by
      intro hs
      exact hy ⟨hs, hb⟩
    simp [hb, image_eq_zero_of_notMem_tsupport hs]

lemma test_far_away_half_ball (φ : MaximalTruncationData.Tests d) (x : Point d)
    {ε : ℝ} (hε : 0 < ε) {y : Point d} (hy : y ∈ ball x (ε / 2)) :
    y ∉ tsupport φ ∩ (ball x ε)ᶜ := by
  intro hs
  exact hs.2 (ball_subset_ball (by linarith : ε / 2 ≤ ε) hy)

lemma test_near_lintegral_le (φ : MaximalTruncationData.Tests d) (x : Point d)
    {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ u, ‖(ball x ε).indicator (φ : Point d → ℂ) u‖ₑ) ≤
      centeredMaximal (φ : Point d → ℂ) x * volume (ball x ε) := by
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [lintegral_indicator measurableSet_ball]
  apply (ENNReal.div_le_iff (measure_ball_pos volume x hε).ne' measure_ball_lt_top.ne).mp
  exact le_iSup₂_of_le ε hε le_rfl

lemma volume_ball_double (x : Point d) {ε : ℝ} (_hε : 0 < ε) :
    volume (ball x ε) = (2 : ℝ≥0∞) ^ d * volume (ball x (ε / 2)) := by
  have hm : (volume : Measure (Point d)) (ball x ε) =
      ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ (Point d)) * volume (ball (0 : Point d) (ε / 2)) := by
    convert Measure.addHaar_ball_mul_of_pos (volume : Measure (Point d)) x (by norm_num : (0 : ℝ) < 2) (ε / 2) using 1; congr 2; ring
  rw [Measure.addHaar_ball_center (volume : Measure (Point d)) x (ε / 2)]
  simpa only [finrank_euclideanSpace_fin, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using hm
lemma test_operator_near_far (T : Operator d) (φ : MaximalTruncationData.Tests d)
    (x : Point d) (ε : ℝ) :
    T (testL2 φ) =
      T ((test_near_memLp φ x ε 2).toLp ((ball x ε).indicator (φ : Point d → ℂ))) +
      T ((test_far_memLp φ x ε 2).toLp ((φ : Point d → ℂ) - (ball x ε).indicator φ)) := by
  have hf : (test_far_memLp φ x ε 2).toLp ((φ : Point d → ℂ) - (ball x ε).indicator φ) =
      testL2 φ - (test_near_memLp φ x ε 2).toLp ((ball x ε).indicator (φ : Point d → ℂ)) := rfl
  rw [hf, map_sub, add_sub_cancel]

lemma test_operator_near_far_ae (T : Operator d) (φ : MaximalTruncationData.Tests d)
    (x : Point d) (ε : ℝ) :
    ∀ᵐ y ∂volume, T (testL2 φ) y =
      T ((test_near_memLp φ x ε 2).toLp ((ball x ε).indicator (φ : Point d → ℂ))) y +
      T ((test_far_memLp φ x ε 2).toLp ((φ : Point d → ℂ) - (ball x ε).indicator φ)) y := by
  nth_rw 1 [test_operator_near_far T φ x ε]
  exact Lp.coeFn_add _ _

lemma test_far_integrand_ae (K : Point d → ℂ) (φ : MaximalTruncationData.Tests d)
    (x v : Point d) {ε : ℝ} (hε : 0 < ε) :
    (fun u => K (v - u) * (φ u - (ball x ε).indicator (φ : Point d → ℂ) u)) =ᵐ[volume]
      {u : Point d | ε < ‖x - u‖}.indicator (fun u => K (v - u) * φ u) := by
  have hnull : (volume : Measure (Point d)) (sphere x ε) = 0 :=
    Measure.addHaar_sphere_of_ne_zero volume x hε.ne'
  filter_upwards [compl_mem_ae_iff.mpr hnull] with u hu
  have hn : ‖x - u‖ ≠ ε := by
    simpa [mem_sphere, dist_eq_norm_sub, norm_sub_rev] using hu
  by_cases hb : u ∈ ball x ε
  · have he : ¬ ε < ‖x - u‖ := by
      have hh : ‖x - u‖ < ε := by simpa [mem_ball, dist_eq_norm_sub, norm_sub_rev] using hb
      exact not_lt.mpr hh.le
    simp [hb, he]
  · have he : ε < ‖x - u‖ := by
      have hh : ε ≤ ‖x - u‖ := by simpa [mem_ball, dist_eq_norm_sub, norm_sub_rev] using hb
      exact hh.lt_of_ne hn.symm
    simp [hb, he]

lemma test_far_integral_eq_set (K : Point d → ℂ) (φ : MaximalTruncationData.Tests d)
    (x v : Point d) {ε : ℝ} (hε : 0 < ε) :
    (∫ u, K (v - u) * (φ u - (ball x ε).indicator (φ : Point d → ℂ) u)) =
      ∫ u in {u : Point d | ε < ‖x - u‖}, K (v - u) * φ u := by
  rw [← integral_indicator (by measurability : MeasurableSet {u : Point d | ε < ‖x - u‖})]
  exact integral_congr_ae (test_far_integrand_ae K φ x v hε)

lemma test_far_error_integral {K : Point d → ℂ}
    (hK : ContinuousOn K ({0}ᶜ : Set (Point d)))
    (φ : MaximalTruncationData.Tests d) (x : Point d) {ε : ℝ} (hε : 0 < ε)
    {y : Point d} (hy : y ∈ ball x (ε / 2)) :
    truncated K φ ε x - (∫ u, K (y - u) * (φ u - (ball x ε).indicator (φ : Point d → ℂ) u)) =
      ∫ u in {u : Point d | ε < ‖x - u‖}, (K (x - u) - K (y - u)) * φ u := by
  let f : Point d → ℂ := (φ : Point d → ℂ) - (ball x ε).indicator φ
  let S := tsupport φ ∩ (ball x ε)ᶜ
  have hs : ∀ᵐ u ∂volume, u ∉ S → f u = 0 :=
    Eventually.of_forall fun u hu => test_far_eq_zero φ x ε u hu
  have h1 : Integrable f volume := memLp_one_iff_integrable.mp (test_far_memLp φ x ε 1)
  have hxS : x ∉ S := by simp [S, hε]
  have hyS := test_far_away_half_ball φ x hε hy
  have hxi := off_support_integrable hK h1 S (test_far_support_compact φ x ε) hs x hxS
  have hyi := off_support_integrable hK h1 S (test_far_support_compact φ x ε) hs y hyS
  rw [show truncated K φ ε x = ∫ u, K (x-u)*f u from
    (test_far_integral_eq_set K φ x x hε).symm]
  change (∫ u, K (x-u)*f u) - (∫ u, K (y-u)*f u) = _
  rw [← integral_sub hxi hyi]
  rw [← integral_indicator (by measurability : MeasurableSet {u : Point d | ε < ‖x-u‖})]
  apply integral_congr_ae
  filter_upwards [test_far_integrand_ae K φ x x hε, test_far_integrand_ae K φ x y hε] with u hxu hyu
  change K (x-u)*f u - K (y-u)*f u = _
  dsimp [f]
  rw [hxu, hyu]
  by_cases hu : ε < ‖x-u‖ <;> simp [hu, sub_mul]


lemma test_far_kernel_error {K : Point d → ℂ} {B : ℝ≥0} (hK : KernelRegularity K B)
    (x : Point d) {ε : ℝ} (hε : 0 < ε) {y : Point d} (hy : y ∈ ball x (ε/2))
    {u : Point d} (hu : ε < ‖x-u‖) :
    ‖K (x-u) - K (y-u)‖ ≤ ((d : ℝ)*B*2^(d+1))*ε / ‖x-u‖^(d+1) := by
  have hxy : ‖x-y‖ < ε/2 := by simpa [mem_ball, dist_eq_norm_sub, norm_sub_rev] using hy
  have hxu : x-u ≠ 0 := norm_pos_iff.mp (hε.trans hu)
  have hh : ‖x-y‖ ≤ ‖x-u‖/2 := by linarith
  have hbd := CZLp.kernel_difference_of_gradient K B hK.contDiff hK.gradient (x-u) (x-y) hxu hh
  have hid : x-u-(x-y) = y-u := by abel
  rw [hid, norm_sub_rev] at hbd
  exact hbd.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith : ‖x-y‖ ≤ ε) (by positivity)) (by positivity))

lemma test_far_error_bound {K : Point d → ℂ} {B : ℝ≥0} (hK : KernelRegularity K B)
    (φ : MaximalTruncationData.Tests d) (x : Point d) {ε : ℝ} (hε : 0 < ε)
    (htail : (∫⁻ u in {u : Point d | ε < ‖x-u‖},
      ‖φ u‖ₑ / ENNReal.ofReal (‖x-u‖^(d+1))) ≤
      ENNReal.ofReal ((2 : ℝ)^(d+1)*volume.real (ball (0 : Point d) 1)/ε) *
        centeredMaximal (φ : Point d → ℂ) x)
    {y : Point d} (hy : y ∈ ball x (ε/2)) :
    ‖truncated K φ ε x - (∫ u, K (y-u)*(φ u-(ball x ε).indicator (φ : Point d → ℂ) u))‖ₑ ≤
      ENNReal.ofReal (((d : ℝ)*B*2^(d+1))*((2 : ℝ)^(d+1)*volume.real (ball (0 : Point d) 1))) *
        centeredMaximal (φ : Point d → ℂ) x := by
  let A : ℝ := (d : ℝ)*B*2^(d+1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  rw [test_far_error_integral hK.contDiff.continuousOn φ x hε hy]
  calc
    _ ≤ ∫⁻ u in {u : Point d | ε < ‖x-u‖}, ‖(K (x-u)-K (y-u))*φ u‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u in {u : Point d | ε < ‖x-u‖},
        ENNReal.ofReal (A*ε) * (‖φ u‖ₑ / ENNReal.ofReal (‖x-u‖^(d+1))) := by
      apply setLIntegral_mono' (by measurability)
      intro u hu
      have hp : 0 < ‖x-u‖^(d+1) := pow_pos (hε.trans hu) _
      calc
        _ = ENNReal.ofReal ‖K (x-u)-K (y-u)‖ * ‖φ u‖ₑ := by rw [enorm_mul, ofReal_norm]
        _ ≤ ENNReal.ofReal (A*ε / ‖x-u‖^(d+1)) * ‖φ u‖ₑ :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (test_far_kernel_error hK x hε hy hu)) le_rfl
        _ = _ := by rw [ENNReal.ofReal_div_of_pos hp]; simp only [div_eq_mul_inv]; ac_rfl
    _ = ENNReal.ofReal (A*ε) * (∫⁻ u in {u : Point d | ε < ‖x-u‖},
        ‖φ u‖ₑ / ENNReal.ofReal (‖x-u‖^(d+1))) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (A*ε) *
        (ENNReal.ofReal ((2 : ℝ)^(d+1)*volume.real (ball (0 : Point d) 1)/ε) * centeredMaximal (φ : Point d → ℂ) x) :=
      mul_le_mul' le_rfl htail
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hA hε.le)]
      congr 2
      dsimp [A]
      field_simp

lemma test_far_oscillation {K : Point d → ℂ} {B : ℝ≥0} {T : Operator d}
    (hK : KernelRegularity K B) (hT : SmoothL2Action T K)
    (φ : MaximalTruncationData.Tests d) (x : Point d) {ε : ℝ} (hε : 0 < ε)
    (htail : (∫⁻ u in {u : Point d | ε < ‖x-u‖},
      ‖φ u‖ₑ / ENNReal.ofReal (‖x-u‖^(d+1))) ≤
      ENNReal.ofReal ((2 : ℝ)^(d+1)*volume.real (ball (0 : Point d) 1)/ε) *
        centeredMaximal (φ : Point d → ℂ) x) :
    ∀ᵐ y ∂volume, y ∈ ball x (ε/2) →
      ‖truncated K φ ε x - T ((test_far_memLp φ x ε 2).toLp
        ((φ : Point d → ℂ)-(ball x ε).indicator φ)) y‖ₑ ≤
      ENNReal.ofReal (((d : ℝ)*B*2^(d+1))*((2 : ℝ)^(d+1)*volume.real (ball (0 : Point d) 1))) *
        centeredMaximal (φ : Point d → ℂ) x := by
  have hoff := compact_L2_off_support T hK.contDiff.continuousOn hT
    ((φ : Point d → ℂ)-(ball x ε).indicator φ) (test_far_memLp φ x ε 2)
    (tsupport φ ∩ (ball x ε)ᶜ) (test_far_support_compact φ x ε)
    (Eventually.of_forall fun u hu => test_far_eq_zero φ x ε u hu)
  filter_upwards [hoff] with y hy hyball
  rw [hy (test_far_away_half_ball φ x hε hyball)]
  exact test_far_error_bound hK φ x hε htail hyball


lemma exists_good_point {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (E s t : Set α) (P : α → Prop) (hP : ∀ᵐ y ∂μ, P y)
    (hm0 : μ E ≠ 0) (hmfin : μ E ≠ ∞)
    (hs : μ s ≤ μ E / 4) (ht : μ t ≤ μ E / 4) :
    ∃ y ∈ E, y ∉ s ∧ y ∉ t ∧ P y := by
  by_contra! hn
  have he : μ E ≤ μ (s ∪ t) := by
    apply measure_mono_ae
    filter_upwards [hP] with y hy
    intro hye
    simp only [mem_union]
    by_cases hys : y ∈ s
    · exact Or.inl hys
    · exact Or.inr (not_not.mp (fun hyt => hn y hye hys hyt hy))
  have hle : μ E ≤ μ E / 4 + μ E / 4 :=
    he.trans ((measure_union_le s t).trans (add_le_add hs ht))
  have hmf : μ E / 4 + μ E / 4 < μ E := by
    have hfin : μ E / 4 ≠ ∞ := ENNReal.div_ne_top hmfin (by norm_num)
    apply (ENNReal.toReal_lt_toReal (ENNReal.add_ne_top.mpr ⟨hfin, hfin⟩) hmfin).mp
    rw [ENNReal.toReal_add hfin hfin, ENNReal.toReal_div]
    have hmpos := ENNReal.toReal_pos hm0 hmfin
    norm_num
    linarith
  exact (not_lt_of_ge hle) hmf

lemma measure_bad_moment_le (g : Point d → ℂ) (hg : AEStronglyMeasurable g volume)
    (δ : ℝ) (hδ : 0 < δ) (x : Point d) {r : ℝ} (hr : 0 < r)
    (hN : centeredMaximal (fun y => ‖g y‖ ^ δ) x ≠ ∞)
    {a : ℝ} (ha : 0 < a)
    (h4 : 4 * (centeredMaximal (fun y => ‖g y‖ ^ δ) x).toReal ≤ a ^ δ) :
    (volume.restrict (ball x r)) {y | a < ‖g y‖} ≤ volume (ball x r) / 4 := by
  let N := centeredMaximal (fun y => ‖g y‖ ^ δ) x
  let A := ENNReal.ofReal (a ^ δ)
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos ha _)).ne'
  have hAfin : A ≠ ∞ := ENNReal.ofReal_ne_top
  have hL : (∫⁻ y in ball x r, ENNReal.ofReal (‖g y‖ ^ δ)) ≤ N * volume (ball x r) := by
    have hb : (∫⁻ y in ball x r, ‖‖g y‖ ^ δ‖ₑ) / volume (ball x r) ≤ N :=
      le_iSup₂_of_le r hr le_rfl
    have hn (y : Point d) : ‖‖g y‖ ^ δ‖ₑ = ENNReal.ofReal (‖g y‖ ^ δ) := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    simp_rw [hn] at hb
    exact (ENNReal.div_le_iff (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne).mp hb
  have hNA : N ≤ A / 4 := by
    have hN' : N ≠ ∞ := hN
    rw [← ENNReal.ofReal_toReal hN']
    calc
      ENNReal.ofReal N.toReal ≤ ENNReal.ofReal (a ^ δ / 4) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = A / 4 := by simp [A, ENNReal.ofReal_div_of_pos]
  calc
    (volume.restrict (ball x r)) {y | a < ‖g y‖} ≤
        (volume.restrict (ball x r)) {y | A ≤ ENNReal.ofReal (‖g y‖ ^ δ)} := by
      apply measure_mono
      intro y hy
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ha.le hy.le hδ.le)
    _ ≤ (∫⁻ y in ball x r, ENNReal.ofReal (‖g y‖ ^ δ)) / A := by
      apply meas_ge_le_lintegral_div _ hA0 hAfin
      exact (hg.norm.aemeasurable.pow_const δ).ennreal_ofReal.restrict
    _ ≤ volume (ball x r) / 4 := by
      apply (ENNReal.div_le_iff hA0 hAfin).mpr
      calc
        _ ≤ N * volume (ball x r) := hL
        _ ≤ (A / 4) * volume (ball x r) := mul_le_mul' hNA le_rfl
        _ = volume (ball x r) / 4 * A := by simp only [div_eq_mul_inv]; ac_rfl

lemma measure_bad_near_le (T : Operator d) {C : ℝ} (hC : 0 ≤ C)
    (hcore : CoreBound T C) (φ : Tests d) (x : Point d) {ε : ℝ} (hε : 0 < ε)
    (hM : centeredMaximal (φ : Point d → ℂ) x ≠ ∞)
    {b : ℝ} (hb : 0 < b)
    (h4 : 4 * C * (2 : ℝ) ^ d * (centeredMaximal (φ : Point d → ℂ) x).toReal ≤ b) :
    (volume.restrict (ball x (ε / 2)))
      {y | b < ‖T ((test_near_memLp φ x ε 2).toLp ((ball x ε).indicator (φ : Point d → ℂ))) y‖}
      ≤ volume (ball x (ε / 2)) / 4 := by
  let M := centeredMaximal (φ : Point d → ℂ) x
  have hcoef : ENNReal.ofReal C * M * (2 : ℝ≥0∞) ^ d ≤ ENNReal.ofReal b / 4 := by
    have hreal : C * M.toReal * (2 : ℝ) ^ d ≤ b / 4 := by dsimp [M]; nlinarith
    have hMR : ENNReal.ofReal M.toReal = M := ENNReal.ofReal_toReal hM
    have hpow : ENNReal.ofReal ((2 : ℝ) ^ d) = (2 : ℝ≥0∞) ^ d := by simp
    calc
      _ = ENNReal.ofReal (C * M.toReal * (2 : ℝ) ^ d) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hC ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul hC, hMR, hpow]
      _ ≤ ENNReal.ofReal (b / 4) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal b / 4 := by simp [ENNReal.ofReal_div_of_pos]
  calc
    _ ≤ volume {y | b < ‖T ((test_near_memLp φ x ε 2).toLp
      ((ball x ε).indicator (φ : Point d → ℂ))) y‖} := Measure.restrict_le_self _
    _ ≤ ENNReal.ofReal (C / b) * eLpNorm ((ball x ε).indicator (φ : Point d → ℂ)) 1 volume :=
      hcore _ (test_near_memLp φ x ε 1) (test_near_memLp φ x ε 2) b hb
    _ ≤ ENNReal.ofReal (C / b) * (M * ((2 : ℝ≥0∞) ^ d * volume (ball x (ε / 2)))) := by
      gcongr
      rw [eLpNorm_one_eq_lintegral_enorm (test_near_memLp φ x ε 1).aestronglyMeasurable]
      exact (test_near_lintegral_le φ x hε).trans_eq
        (by rw [volume_ball_double x hε])
    _ = (ENNReal.ofReal C * M * (2 : ℝ≥0∞) ^ d * volume (ball x (ε / 2))) /
        ENNReal.ofReal b := by
      rw [ENNReal.ofReal_div_of_pos hb]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ volume (ball x (ε / 2)) / 4 := by
      apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hb).ne' ENNReal.ofReal_ne_top).mpr
      calc
        _ ≤ (ENNReal.ofReal b / 4) * volume (ball x (ε / 2)) := mul_le_mul' hcoef le_rfl
        _ = volume (ball x (ε / 2)) / 4 * ENNReal.ofReal b := by
          simp only [div_eq_mul_inv]; ac_rfl

lemma cotlar_truncated_real_of_oscillation (T : Operator d) (K : Point d → ℂ)
    {C D : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D) (hcore : CoreBound T C)
    (φ : Tests d) (δ : ℝ) (hδ : 0 < δ) (x : Point d)
    (hM : centeredMaximal (φ : Point d → ℂ) x ≠ ∞)
    (hN : centeredMaximal (fun y => ‖T (testL2 φ) y‖ ^ δ) x ≠ ∞)
    {ε : ℝ} (hε : 0 < ε)
    (hosc : ∀ᵐ y ∂volume, y ∈ ball x (ε / 2) →
      ‖truncated K φ ε x - T ((test_far_memLp φ x ε 2).toLp
        ((φ : Point d → ℂ) - (ball x ε).indicator φ)) y‖ ≤
        D * (centeredMaximal (φ : Point d → ℂ) x).toReal) :
    ‖truncated K φ ε x‖ ≤
      (4 : ℝ) ^ (1 / δ) * (centeredMaximal (fun y => ‖T (testL2 φ) y‖ ^ δ) x).toReal ^ (1 / δ) +
        (4 * C * (2 : ℝ) ^ d + D) * (centeredMaximal (φ : Point d → ℂ) x).toReal := by
  let M := (centeredMaximal (φ : Point d → ℂ) x).toReal
  let N := (centeredMaximal (fun y => ‖T (testL2 φ) y‖ ^ δ) x).toReal
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have hroot : 0 < 1 / δ := by positivity
  apply le_of_forall_pos_le_add
  intro η hη
  let a := (4 * N) ^ (1 / δ) + η / 2
  let b := 4 * C * (2 : ℝ) ^ d * M + η / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have h4a : 4 * N ≤ a ^ δ := by
    calc
      4 * N = ((4 * N) ^ (1 / δ)) ^ δ := by
        rw [one_div, Real.rpow_inv_rpow (by positivity) hδ.ne']
      _ ≤ a ^ δ := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _)
        (by dsimp [a]; linarith) hδ.le
  have h4b : 4 * C * (2 : ℝ) ^ d * M ≤ b := by dsimp [b]; linarith
  have hbad1 := measure_bad_moment_le (T (testL2 φ)) (Lp.aestronglyMeasurable _) δ hδ x
    (show 0 < ε / 2 by positivity) hN ha h4a
  have hbad2 := measure_bad_near_le T hC hcore φ x hε hM hb h4b
  let P : Point d → Prop := fun y => y ∈ ball x (ε / 2) ∧
    T (testL2 φ) y =
      T ((test_near_memLp φ x ε 2).toLp ((ball x ε).indicator (φ : Point d → ℂ))) y +
      T ((test_far_memLp φ x ε 2).toLp ((φ : Point d → ℂ) - (ball x ε).indicator φ)) y ∧
    ‖truncated K φ ε x - T ((test_far_memLp φ x ε 2).toLp
      ((φ : Point d → ℂ) - (ball x ε).indicator φ)) y‖ ≤ D * M
  have hP : ∀ᵐ y ∂volume.restrict (ball x (ε / 2)), P y := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (test_operator_near_far_ae T φ x ε), ae_restrict_of_ae hosc] with y hy hs ho
    exact ⟨hy, hs, ho hy⟩
  obtain ⟨y, _, hy1, hy2, hy⟩ := exists_good_point (volume.restrict (ball x (ε / 2)))
    Set.univ {y | a < ‖T (testL2 φ) y‖}
    {y | b < ‖T ((test_near_memLp φ x ε 2).toLp ((ball x ε).indicator (φ : Point d → ℂ))) y‖}
    P hP (by simpa using (measure_ball_pos volume x (show 0 < ε / 2 by positivity)).ne')
    (by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top.ne : volume (ball x (ε / 2)) ≠ ∞)) (by simpa using hbad1) (by simpa using hbad2)
  have hny : ‖T ((test_near_memLp φ x ε 2).toLp ((ball x ε).indicator (φ : Point d → ℂ))) y‖ ≤ b :=
    le_of_not_gt hy2
  have hty : ‖T (testL2 φ) y‖ ≤ a := le_of_not_gt hy1
  have hfy : ‖T ((test_far_memLp φ x ε 2).toLp ((φ : Point d → ℂ) - (ball x ε).indicator φ)) y‖ ≤ a + b := by
    calc
      _ = ‖T (testL2 φ) y - T ((test_near_memLp φ x ε 2).toLp
        ((ball x ε).indicator (φ : Point d → ℂ))) y‖ := by rw [hy.2.1]; congr 1; ring
      _ ≤ ‖T (testL2 φ) y‖ + ‖T ((test_near_memLp φ x ε 2).toLp
        ((ball x ε).indicator (φ : Point d → ℂ))) y‖ := norm_sub_le _ _
      _ ≤ a + b := add_le_add hty hny
  have htr : ‖truncated K φ ε x‖ ≤ D * M + (a + b) := by
    calc
      _ = ‖(truncated K φ ε x - T ((test_far_memLp φ x ε 2).toLp
        ((φ : Point d → ℂ) - (ball x ε).indicator φ)) y) +
        T ((test_far_memLp φ x ε 2).toLp ((φ : Point d → ℂ) - (ball x ε).indicator φ)) y‖ := by
          congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hy.2.2 hfy)
  have heq : (4 * N) ^ (1 / δ) = (4 : ℝ) ^ (1 / δ) * N ^ (1 / δ) :=
    Real.mul_rpow (by norm_num) hN0
  dsimp only [a, b] at htr
  rw [heq] at htr
  change _ ≤ _ + _ + η
  dsimp only [M, N] at htr
  nlinarith

/-- Finite ENNReal values let a real good-point estimate retain its extended
maximal-function conclusion without discarding a possible infinite truncation. -/
lemma cotlar_enorm_algebra (l a b s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s)
    (M N : ℝ≥0∞) (hM : M ≠ ∞) (hN : N ≠ ∞)
    (hreal : l ≤ a * N.toReal ^ s + b * M.toReal) :
    ENNReal.ofReal l ≤ ENNReal.ofReal (a + b) * (N ^ s + M) := by
  calc
    ENNReal.ofReal l ≤ ENNReal.ofReal (a * N.toReal ^ s + b * M.toReal) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal a * N ^ s + ENNReal.ofReal b * M := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul ha,
        ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs.le,
        ENNReal.ofReal_toReal hN, ENNReal.ofReal_mul hb, ENNReal.ofReal_toReal hM]
    _ ≤ (ENNReal.ofReal a + ENNReal.ofReal b) * N ^ s +
        (ENNReal.ofReal a + ENNReal.ofReal b) * M := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (le_add_right le_rfl) (by positivity))
        (mul_le_mul_of_nonneg_right (le_add_left le_rfl) (by positivity))
    _ = ENNReal.ofReal (a + b) * (N ^ s + M) := by
      rw [ENNReal.ofReal_add ha hb, mul_add]

lemma cotlar_of_oscillation (T : Operator d) (K : Point d → ℂ)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hcore : CoreBound T C)
    (φ : Tests d) (δ : ℝ) (hδ : 0 < δ)
    (hosc : ∀ (ε : ℝ), 0 < ε → ∀ x : Point d,
      ∀ᵐ y ∂volume, y ∈ ball x (ε / 2) →
        ‖truncated K φ ε x - T ((test_far_memLp φ x ε 2).toLp
          ((φ : Point d → ℂ) - (ball x ε).indicator φ)) y‖ₑ ≤
          ENNReal.ofReal D * centeredMaximal (φ : Point d → ℂ) x) :
    ∀ x : Point d, maximalTruncation K φ x ≤
      ENNReal.ofReal ((4 : ℝ) ^ (1 / δ) + 4 * C * (2 : ℝ) ^ d + D) *
        ((centeredMaximal (fun y => ‖T (testL2 φ) y‖ ^ δ) x) ^ (1 / δ) +
          centeredMaximal (φ : Point d → ℂ) x) := by
  intro x
  have hroot : 0 < 1 / δ := by positivity
  have hcoef : 0 < (4 : ℝ) ^ (1 / δ) + 4 * C * (2 : ℝ) ^ d + D := by positivity
  by_cases hM : centeredMaximal (φ : Point d → ℂ) x = ∞
  · rw [hM, add_top, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hcoef).ne']
    exact le_top
  by_cases hN : centeredMaximal (fun y => ‖T (testL2 φ) y‖ ^ δ) x = ∞
  · rw [hN, ENNReal.top_rpow_of_pos hroot, top_add,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr hcoef).ne']
    exact le_top
  apply iSup_le
  intro ε
  apply iSup_le
  intro hε
  have hoscR : ∀ᵐ y ∂volume, y ∈ ball x (ε / 2) →
      ‖truncated K φ ε x - T ((test_far_memLp φ x ε 2).toLp
        ((φ : Point d → ℂ) - (ball x ε).indicator φ)) y‖ ≤
        D * (centeredMaximal (φ : Point d → ℂ) x).toReal := by
    filter_upwards [hosc ε hε x] with y hy hyball
    have hf : ENNReal.ofReal D * centeredMaximal (φ : Point d → ℂ) x ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM
    have hr := ENNReal.toReal_mono hf (hy hyball)
    simpa only [toReal_enorm, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hD] using hr
  have hreal := cotlar_truncated_real_of_oscillation T K hC hD hcore φ δ hδ x hM hN hε hoscR
  have halg := cotlar_enorm_algebra ‖truncated K φ ε x‖ ((4 : ℝ) ^ (1 / δ))
    (4 * C * (2 : ℝ) ^ d + D) (1 / δ) (by positivity) (by positivity) hroot
    (centeredMaximal (φ : Point d → ℂ) x)
    (centeredMaximal (fun y => ‖T (testL2 φ) y‖ ^ δ) x) hM hN hreal
  simpa only [add_assoc, ofReal_norm] using halg


/-- The far-field error constant is controlled by dimension and the gradient bound. -/
def oscillationConstant (d : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  ⟨(((d : ℝ) * B * 2 ^ (d + 1)) *
      ((2 : ℝ) ^ (d + 1) * volume.real (ball (0 : Point d) 1))), by positivity⟩

/-- Cotlar's estimate follows from the genuine compact-L² representation,
the weak endpoint, and the summable far-field kernel error. -/
theorem cotlar : Specs.P102.U2.MaximalTruncation.cotlar := by
  obtain ⟨E, hE⟩ := kernel_representation
  obtain ⟨C₁, Cₚ, hFull⟩ := CZLp.full_extension
  refine ⟨fun d _K B N δ =>
    Real.toNNReal ((4 : ℝ) ^ (1 / δ) + 4 * (C₁ d (E d * B) N : ℝ) * 2 ^ d +
      (oscillationConstant d B : ℝ)), ?_⟩
  intro d hd K B T hK hT δ hδ _hδ1 φ
  have hcore := (hFull d hd T K (E d * B) (hE d hd K B T hK hT).1).1
  have hpoint := cotlar_of_oscillation T K (C := (C₁ d (E d * B) ‖T‖₊ : ℝ))
    (D := (oscillationConstant d B : ℝ)) (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) hcore
    φ δ hδ (fun ε hε x =>
      test_far_oscillation hK hT φ x hε (maximal_weighted_tail φ x hε))
  exact ae_of_all _ (fun x => by
    simpa only [ENNReal.ofReal, add_assoc] using hpoint x)

/-- The strong estimate, a.e. finiteness, and real Lp realization on every Lp input. -/
theorem maximal_bound : Specs.P102.U2.MaximalTruncation.maximal_bound :=
  maximal_bound_conditional cotlar kernel_representation

end P102.U2.MaximalTruncation
