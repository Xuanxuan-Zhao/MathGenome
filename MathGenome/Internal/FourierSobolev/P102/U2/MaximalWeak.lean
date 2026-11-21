import MathGenome.Internal.FourierSobolev.Specs.P102.U2.MaximalWeak
import MathGenome.Internal.RealAnalysis.D11.Ch13.MaximalWeak11

noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace P102.U2.MaximalWeak
open D11.Ch03
open D11.Ch03.LebesgueMeasures
open D11.Ch13.AveragesMaximalDefinition
open D11.Ch13.MaximalWeak11
abbrev μ (d : ℕ) [NeZero d] := lebesgue d
private theorem volume_sphere_null {d : ℕ} (x : Point d) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Point d)) (sphere x r) = 0 :=
  Measure.addHaar_sphere_of_ne_zero volume x hr.ne'

private theorem volume_ball_double {d : ℕ} (x z : Point d) (r : ℝ) :
    (volume : Measure (Point d)) (ball x (2*r)) =
      (2 : ℝ≥0∞)^d * volume (ball z r) := by
  rw [Measure.addHaar_ball_mul_of_pos volume x (by norm_num : (0:ℝ)<2) r,
    Measure.addHaar_ball_center volume z r]
  simp [finrank_euclideanSpace, ENNReal.ofReal_pow]

local instance (d : ℕ) [NeZero d] : MeasurableSpace (Point d) := lebesgueSpace d
variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

def ballAverage (f : Point d → 𝕜) (r : ℝ) (x : Point d) : ℝ :=
  (μ d (ball x r)).toReal⁻¹ * ∫ y in ball x r, ‖f y‖ ∂(μ d)

def centered (f : Point d → 𝕜) (x : Point d) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), ENNReal.ofReal (ballAverage f r x)

def uncentered (f : Point d → 𝕜) (x : Point d) : ℝ≥0∞ :=
  ⨆ (z : Point d) (r : ℝ) (_ : 0 < r) (_ : x ∈ ball z r),
    ENNReal.ofReal (ballAverage f r z)

theorem centered_eq_library (f : Point d → 𝕜) (hf : locallyIntegrable f) :
    centered f = maximal f hf := rfl

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
theorem ballAverage_congr (f g : Point d → 𝕜) (h : f =ᵐ[μ d] g) (r : ℝ) (x : Point d) :
    ballAverage f r x = ballAverage g r x := by
  unfold ballAverage
  congr 1
  exact integral_congr_ae (ae_restrict_of_ae (h.mono (fun _ h => congrArg norm h)))

theorem ae_invariant : Specs.P102.U2.MaximalWeak.ae_invariant := by
  intro d _ 𝕜 _ _ _ f g _ _ h
  have he : ballAverage f = ballAverage g := by
    funext r x
    exact ballAverage_congr f g h r x
  constructor
  · change centered f = centered g
    exact congrArg (fun (A : ℝ → Point d → ℝ) => fun x => ⨆ (r : ℝ) (_ : 0 < r), ENNReal.ofReal (A r x)) he
  · change uncentered f = uncentered g
    exact congrArg (fun (A : ℝ → Point d → ℝ) => fun x => ⨆ (z : Point d) (r : ℝ) (_ : 0 < r)
      (_ : x ∈ ball z r), ENNReal.ofReal (A r z)) he

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
theorem centered_le_uncentered (f : Point d → 𝕜) (x : Point d) :
    centered f x ≤ uncentered f x := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  exact le_iSup_of_le x (le_iSup_of_le r (le_iSup_of_le hr
    (le_iSup_of_le (mem_ball_self hr) le_rfl)))

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
theorem uncentered_level_open (f : Point d → 𝕜) (a : ℝ≥0∞) :
    IsOpen {x | a < uncentered f x} := by
  have he : {x | a < uncentered f x} =
      ⋃ (z : Point d) (r : ℝ) (_ : 0 < r)
        (_ : a < ENNReal.ofReal (ballAverage f r z)), ball z r := by
    ext x
    simp only [mem_ofPred_eq, uncentered, lt_iSup_iff, mem_iUnion]
    aesop
  rw [he]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
    isOpen_iUnion fun _ => isOpen_ball

-- Local integrability suffices for dominated convergence in a moving ball:
-- centers near x have all their balls inside the fixed ball of radius r+1.
theorem continuous_ball_integral_local (f : Point d → 𝕜) (hf : locallyIntegrable f)
    (r : ℝ) (hr : 0 < r) :
    Continuous (fun z => ∫ y in ball z r, ‖f y‖ ∂(μ d)) := by
  simp_rw [← integral_indicator (ball_measurable _ _)]
  apply continuous_iff_continuousAt.mpr
  intro x
  have hi : IntegrableOn (fun y => ‖f y‖) (ball x (r+1)) (μ d) :=
    ((((locallyIntegrable_iff f).mp hf).2 _ (isCompact_closedBall x (r+1))).mono_set
      ball_subset_closedBall).norm
  apply continuousAt_of_dominated (bound := (ball x (r+1)).indicator (fun y => ‖f y‖))
  · apply Eventually.of_forall
    intro z
    have hz : IntegrableOn (fun y => ‖f y‖) (ball z r) (μ d) :=
      ((((locallyIntegrable_iff f).mp hf).2 _ (isCompact_closedBall z r)).mono_set
        ball_subset_closedBall).norm
    exact (hz.integrable_indicator (ball_measurable z r)).1
  · filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1)] with z hz
    apply ae_of_all
    intro y
    by_cases hy : y ∈ ball z r
    · have hyx : y ∈ ball x (r+1) := by
        exact (dist_triangle y z x).trans_lt (add_lt_add hy hz)
      simp [hy, hyx]
    · simp only [indicator_of_notMem hy, norm_zero]
      exact indicator_nonneg (fun _ _ => norm_nonneg _) _
  · exact hi.integrable_indicator (ball_measurable _ _)
  · have hs : μ d (sphere x r) = 0 := by
      rw [EuclideanRegularity.lebesgue_eq_volume]
      exact volume_sphere_null x hr
    have hae : ∀ᵐ y ∂(μ d), y ∉ sphere x r := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hs
    filter_upwards [hae] with y hy
    have hne : dist y x ≠ r := hy
    have hc : ContinuousAt (fun z : Point d => dist y z) x :=
      continuous_const.dist continuous_id |>.continuousAt
    by_cases h : dist y x < r
    · have he : ∀ᶠ z in 𝓝 x, y ∈ ball z r := hc.eventually (gt_mem_nhds h)
      exact continuousAt_const.congr_of_eventuallyEq (he.mono (fun z hz =>
        indicator_of_mem hz _))
    · have he : ∀ᶠ z in 𝓝 x, y ∉ ball z r := by
        have hgt : r < dist y x := lt_of_le_of_ne (le_of_not_gt h) hne.symm
        exact (hc.eventually (lt_mem_nhds hgt)).mono (fun z hz => not_lt.mpr hz.le)
      exact continuousAt_const.congr_of_eventuallyEq (he.mono (fun z hz =>
        indicator_of_notMem hz _))

theorem continuous_ballAverage (f : Point d → 𝕜) (hf : locallyIntegrable f)
    (r : ℝ) (hr : 0 < r) : Continuous (ballAverage f r) := by
  unfold ballAverage
  simp_rw [lebesgue_ball_center]
  exact continuous_const.mul (continuous_ball_integral_local f hf r hr)

theorem centered_level_open (f : Point d → 𝕜) (hf : locallyIntegrable f)
    (a : ℝ≥0∞) : IsOpen {x | a < centered f x} := by
  have he : {x | a < centered f x} =
      ⋃ (r : ℝ) (_ : 0 < r), {x | a < ENNReal.ofReal (ballAverage f r x)} := by
    ext x
    simp only [mem_ofPred_eq, centered, lt_iSup_iff, mem_iUnion]
  rw [he]
  exact isOpen_iUnion fun r => isOpen_iUnion fun hr => isOpen_lt continuous_const
    (ENNReal.continuous_ofReal.comp (continuous_ballAverage f hf r hr))

theorem measurable_maximal : Specs.P102.U2.MaximalWeak.measurable_maximal := by
  intro d _ 𝕜 _ _ _ f hf
  change Measurable (centered f) ∧ Measurable (uncentered f)
  exact ⟨measurable_of_Ioi fun a => (centered_level_open f hf a).measurableSet,
    measurable_of_Ioi fun a => (uncentered_level_open f a).measurableSet⟩

theorem lebesgue_ball_double (x z : Point d) (r : ℝ) :
    μ d (ball x (2*r)) = (2 : ℝ≥0∞)^d * μ d (ball z r) := by
  simp_rw [μ, EuclideanRegularity.lebesgue_eq_volume]
  exact volume_ball_double x z r

theorem ballAverage_le_double (f : Point d → 𝕜) (hf : locallyIntegrable f)
    (x z : Point d) (r : ℝ) (hr : 0 < r) (hx : x ∈ ball z r) :
    ballAverage f r z ≤ (2 : ℝ)^d * ballAverage f (2*r) x := by
  have hsub : ball z r ⊆ ball x (2*r) := by
    intro y hy
    have hx' : dist z x < r := by simpa [dist_comm] using hx
    have hy' : dist y z < r := hy
    exact (dist_triangle y z x).trans_lt (by linarith)
  have hi : IntegrableOn (fun y => ‖f y‖) (ball x (2*r)) (μ d) :=
    ((((locallyIntegrable_iff f).mp hf).2 _ (isCompact_closedBall x (2*r))).mono_set
      ball_subset_closedBall).norm
  have hI := setIntegral_mono_set hi (ae_of_all _ (fun y => norm_nonneg (f y)))
    (Filter.Eventually.of_forall hsub)
  have hvol : (μ d (ball x (2*r))).toReal =
      (2:ℝ)^d * (μ d (ball z r)).toReal := by
    rw [lebesgue_ball_double x z r, ENNReal.toReal_mul, ENNReal.toReal_pow]
    norm_num
  have hn := (ball_measure z r hr).2.2.ne'
  unfold ballAverage
  calc
    _ ≤ (μ d (ball z r)).toReal⁻¹ * (∫ y in ball x (2*r), ‖f y‖ ∂(μ d)) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by rw [hvol]; field_simp

theorem uncentered_le_centered (f : Point d → 𝕜) (hf : locallyIntegrable f)
    (x : Point d) : uncentered f x ≤ (2:ℝ≥0∞)^d * centered f x := by
  apply iSup_le
  intro z
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  apply iSup_le
  intro hx
  calc
    _ ≤ ENNReal.ofReal ((2:ℝ)^d * ballAverage f (2*r) x) :=
      ENNReal.ofReal_le_ofReal (ballAverage_le_double f hf x z r hr hx)
    _ = (2:ℝ≥0∞)^d * ENNReal.ofReal (ballAverage f (2*r) x) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
      norm_num
    _ ≤ _ := by
      have hsup : ENNReal.ofReal (ballAverage f (2*r) x) ≤ centered f x :=
        le_iSup₂_of_le (2*r) (by positivity) le_rfl
      exact mul_le_mul_of_nonneg_left hsup (by positivity)

theorem comparison : Specs.P102.U2.MaximalWeak.comparison := by
  intro d _ 𝕜 _ _ _ f hf x
  exact ⟨centered_le_uncentered f x, uncentered_le_centered f hf x⟩

theorem centered_weak_bound (f : Point d → 𝕜) (hf : locallyIntegrable f)
    (hi : Integrable f (μ d)) (a : ℝ) (ha : 0 < a) :
    μ d {x | ENNReal.ofReal a < centered f x} ≤
      (3:ℝ≥0∞)^d * ENNReal.ofReal (∫ y, ‖f y‖ ∂(μ d)) / ENNReal.ofReal a := by
  simpa only [centered_eq_library f hf, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    using maximal_weak11 f hf hi a ha

theorem uncentered_weak_bound (f : Point d → 𝕜) (hf : locallyIntegrable f)
    (hi : Integrable f (μ d)) (a : ℝ) (ha : 0 < a) :
    μ d {x | ENNReal.ofReal a < uncentered f x} ≤
      (6:ℝ≥0∞)^d * ENNReal.ofReal (∫ y, ‖f y‖ ∂(μ d)) / ENNReal.ofReal a := by
  have hp : (0:ℝ) < 2^d := by positivity
  have hpow : ENNReal.ofReal ((2:ℝ)^d) = (2:ℝ≥0∞)^d := by
    rw [ENNReal.ofReal_pow (by norm_num)]; norm_num
  have hs : {x | ENNReal.ofReal a < uncentered f x} ⊆
      {x | ENNReal.ofReal (a / (2:ℝ)^d) < centered f x} := by
    intro x hx
    change ENNReal.ofReal a < uncentered f x at hx
    change ENNReal.ofReal (a / (2:ℝ)^d) < centered f x
    rw [ENNReal.ofReal_div_of_pos hp, hpow,
      ENNReal.div_lt_iff (Or.inl (by positivity))
        (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), mul_comm]
    exact hx.trans_le (uncentered_le_centered f hf x)
  calc
    _ ≤ μ d {x | ENNReal.ofReal (a / (2:ℝ)^d) < centered f x} := measure_mono hs
    _ ≤ (3:ℝ≥0∞)^d * ENNReal.ofReal (∫ y, ‖f y‖ ∂(μ d)) /
        ENNReal.ofReal (a / (2:ℝ)^d) :=
      centered_weak_bound f hf hi _ (div_pos ha hp)
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos hp, hpow,
        div_eq_mul_inv, ENNReal.inv_div (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
          (Or.inl (by positivity)), div_eq_mul_inv, div_eq_mul_inv]
      have h6 : (6:ℝ≥0∞)^d = (3:ℝ≥0∞)^d * (2:ℝ≥0∞)^d := by
        rw [← mul_pow]; norm_num
      rw [h6]
      ring

theorem weak_bounds : Specs.P102.U2.MaximalWeak.weak_bounds := by
  intro d _ 𝕜 _ _ _ f hi a ha
  change Integrable f (μ d) at hi
  let : (μ d).IsComplete := lebesgue_complete d
  have hm : Measurable f := aemeasurable_iff_measurable.mp hi.aestronglyMeasurable.aemeasurable
  have hf : locallyIntegrable f := locallyIntegrable_of_integrable f hm hi
  exact ⟨centered_weak_bound f hf hi a ha, uncentered_weak_bound f hf hi a ha⟩

end P102.U2.MaximalWeak
