import MathGenome.Internal.RealAnalysis.D11.Ch13.AveragesMaximalDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch13.FiniteBallCovering
import MathGenome.Internal.RealAnalysis.D11.Ch03.EuclideanRegularity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.MaximalWeak11
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Weak (1,1) for the shared centered Euclidean maximal function
(paper.tex:4370–4399). Fixed-radius absolute integrals are continuous by
dominated convergence: the moving ball indicators are locally constant
at every point outside the limiting sphere, which is Lebesgue-null.
This gives open strict level sets without restricting the radii.
The finite ball selection bounds each compact subset of a level set;
completed Lebesgue inner regularity gives the full estimate with `3^n`.
Finally the estimates at positive integer thresholds make the infinite
level set null. All evaluated scalar integrals have integrable integrands. -/

noncomputable section
set_option maxHeartbeats 400000
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology BigOperators
namespace D11.Ch13.MaximalWeak11
open D11.Ch03
open D11.Ch03.LebesgueMeasures
open D11.Ch13.AveragesMaximalDefinition

-- These two facts are proved with the native Borel structure, before installing
-- the completed structure used by every integral below.
private theorem volume_sphere_null {n : ℕ} (x : Point n) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Point n)) (sphere x r) = 0 :=
  Measure.addHaar_sphere_of_ne_zero volume x hr.ne'

private theorem volume_ball_center {n : ℕ} (x : Point n) (r : ℝ) :
    (volume : Measure (Point n)) (ball x r) = volume (ball (0 : Point n) r) :=
  Measure.addHaar_ball_center volume x r

local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) := lebesgueSpace n
variable {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

theorem locallyIntegrable_of_integrable (f : Point n → 𝕜) (hm : Measurable f)
    (hi : Integrable f (lebesgue n)) : locallyIntegrable f := by
  exact (locallyIntegrable_iff f).mpr ⟨hm, fun _ _ => hi.integrableOn⟩

theorem continuous_ball_integral (f : Point n → 𝕜) (hi : Integrable f (lebesgue n))
    (r : ℝ) (hr : 0 < r) :
    Continuous (fun x => ∫ y in ball x r, ‖f y‖ ∂(lebesgue n)) := by
  simp_rw [← integral_indicator (ball_measurable _ _)]
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated (bound := fun y => ‖f y‖)
  · exact Eventually.of_forall (fun z => (hi.norm.indicator (ball_measurable z r)).1)
  · exact Eventually.of_forall (fun z => ae_of_all _ (fun y => by
      by_cases h : y ∈ ball z r
      · simp [h]
      · simp [h]))
  · exact hi.norm
  · have hs : lebesgue n (sphere x r) = 0 := by
      rw [EuclideanRegularity.lebesgue_eq_volume]
      exact volume_sphere_null x hr
    have hae : ∀ᵐ y ∂(lebesgue n), y ∉ sphere x r := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hs
    filter_upwards [hae] with y hy
    have hne : dist y x ≠ r := hy
    have hc : ContinuousAt (fun z : Point n => dist y z) x :=
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

theorem lebesgue_ball_center (x : Point n) (r : ℝ) :
    lebesgue n (ball x r) = lebesgue n (ball (0 : Point n) r) := by
  rw [EuclideanRegularity.lebesgue_eq_volume,
    EuclideanRegularity.lebesgue_eq_volume]
  exact volume_ball_center x r

theorem continuous_absoluteAverage (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (hi : Integrable f (lebesgue n)) (r : ℝ) (hr : 0 < r) :
    Continuous (absoluteAverage f hf r) := by
  change Continuous (fun x => (lebesgue n (ball x r)).toReal⁻¹ *
    ∫ y in ball x r, ‖f y‖ ∂(lebesgue n))
  simp_rw [lebesgue_ball_center]
  exact continuous_const.mul (continuous_ball_integral f hi r hr)

theorem strict_superlevel_open (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (hi : Integrable f (lebesgue n)) (α : ℝ≥0∞) :
    IsOpen {x | α < maximal f hf x} := by
  have heq : {x | α < maximal f hf x} =
      ⋃ (r : ℝ) (_ : 0 < r), {x | α < ENNReal.ofReal (absoluteAverage f hf r x)} := by
    ext x
    simp only [mem_ofPred_eq, maximal, lt_iSup_iff, mem_iUnion]
  rw [heq]
  exact isOpen_iUnion (fun r => isOpen_iUnion (fun hr =>
    isOpen_lt continuous_const
      (ENNReal.continuous_ofReal.comp (continuous_absoluteAverage f hf hi r hr))))

theorem maximal_measurable (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (hi : Integrable f (lebesgue n)) : Measurable (maximal f hf) := by
  exact measurable_of_Ioi (fun α => (strict_superlevel_open f hf hi α).measurableSet)

/-- A witnessing ball has mass bounded by its absolute integral divided by
the threshold. The lower integral makes the subsequent disjoint sum exact. -/
theorem ball_mass_le (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (hi : Integrable f (lebesgue n)) (α : ℝ) (hα : 0 < α)
    (x : Point n) (r : ℝ) (hr : 0 < r)
    (hav : ENNReal.ofReal α < ENNReal.ofReal (absoluteAverage f hf r x)) :
    lebesgue n (ball x r) ≤ (ENNReal.ofReal α)⁻¹ *
      ∫⁻ y in ball x r, ENNReal.ofReal ‖f y‖ ∂(lebesgue n) := by
  obtain ⟨_, hfin, hpos⟩ := ball_measure x r hr
  have ha : α < absoluteAverage f hf r x :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα.le).mp hav
  change α < (lebesgue n (ball x r)).toReal⁻¹ *
    ∫ y in ball x r, ‖f y‖ ∂(lebesgue n) at ha
  have hscaled := (lt_inv_mul_iff₀ hpos).mp ha
  have he : ENNReal.ofReal α * lebesgue n (ball x r) ≤
      ENNReal.ofReal (∫ y in ball x r, ‖f y‖ ∂(lebesgue n)) := by
    rw [← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_mul hα.le]
    exact ENNReal.ofReal_le_ofReal (by simpa only [mul_comm] using hscaled.le)
  rw [ofReal_integral_eq_lintegral_ofReal hi.norm.integrableOn
    (ae_of_all _ (fun y => norm_nonneg (f y)))] at he
  have hd := (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.mpr hα).ne') (Or.inl ENNReal.ofReal_ne_top)).mpr
      (show lebesgue n (ball x r) * ENNReal.ofReal α ≤ _ by
        simpa only [mul_comm] using he)
  simpa only [div_eq_mul_inv, mul_comm] using hd

/-- The finite covering argument on an arbitrary compact subset of the
strict level set; no bounded support assumption is imposed on `f`. -/
theorem compact_level_bound (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (hi : Integrable f (lebesgue n)) (α : ℝ) (hα : 0 < α)
    (K : Set (Point n)) (hK : IsCompact K)
    (hKE : K ⊆ {x | ENNReal.ofReal α < maximal f hf x}) :
    lebesgue n K ≤ (3 : ℝ≥0∞) ^ n * (ENNReal.ofReal α)⁻¹ *
      ENNReal.ofReal (∫ y, ‖f y‖ ∂(lebesgue n)) := by
  classical
  have hw : ∀ x : K, ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal α < ENNReal.ofReal (absoluteAverage f hf r x) := by
    intro x
    have hx := hKE x.property
    simpa only [mem_ofPred_eq, maximal, lt_iSup_iff, exists_prop] using hx
  choose r hr hav using hw
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : Point n) (r x))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩)
  obtain ⟨t, _, hdisj, _, hbound⟩ :=
    FiniteBallCovering.finite_ball_covering n s (fun x : K => (x : Point n)) r
      (fun x _ => hr x)
  have hmeas : ∀ x : K, MeasurableSet (ball (x : Point n) (r x)) :=
    fun x => ball_measurable (x : Point n) (r x)
  have hlin : (∫⁻ y in ⋃ x ∈ t, ball (x : Point n) (r x),
      ENNReal.ofReal ‖f y‖ ∂(lebesgue n)) =
      ∑ x ∈ t, ∫⁻ y in ball (x : Point n) (r x), ENNReal.ofReal ‖f y‖ ∂(lebesgue n) :=
    lintegral_biUnion_finset (μ := lebesgue n) hdisj (fun x _ => hmeas x)
      (fun y => ENNReal.ofReal ‖f y‖)
  have hsum : (∑ x ∈ t, lebesgue n (ball (x : Point n) (r x))) ≤
      (ENNReal.ofReal α)⁻¹ * (∫⁻ y, ENNReal.ofReal ‖f y‖ ∂(lebesgue n)) := by
    calc
      _ ≤ ∑ x ∈ t, (ENNReal.ofReal α)⁻¹ *
          ∫⁻ y in ball (x : Point n) (r x), ENNReal.ofReal ‖f y‖ ∂(lebesgue n) :=
        Finset.sum_le_sum (fun x _ => ball_mass_le f hf hi α hα x (r x) (hr x) (hav x))
      _ = (ENNReal.ofReal α)⁻¹ *
          ∫⁻ y in ⋃ x ∈ t, ball (x : Point n) (r x), ENNReal.ofReal ‖f y‖ ∂(lebesgue n) := by
        rw [hlin, Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) (by positivity)
  calc
    lebesgue n K ≤ lebesgue n (⋃ x ∈ s, ball (x : Point n) (r x)) := measure_mono hs
    _ ≤ (3 : ℝ≥0∞) ^ n * ∑ x ∈ t, lebesgue n (ball (x : Point n) (r x)) := hbound
    _ ≤ (3 : ℝ≥0∞) ^ n * ((ENNReal.ofReal α)⁻¹ *
        ∫⁻ y, ENNReal.ofReal ‖f y‖ ∂(lebesgue n)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      rw [ofReal_integral_eq_lintegral_ofReal hi.norm (ae_of_all _ (fun y => norm_nonneg (f y))),
        mul_assoc]

theorem maximal_weak11 (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (hi : Integrable f (lebesgue n)) (α : ℝ) (hα : 0 < α) :
    lebesgue n {x | ENNReal.ofReal α < maximal f hf x} ≤
      (3 : ℝ≥0∞) ^ n * (ENNReal.ofReal α)⁻¹ *
        ENNReal.ofReal (∫ y, ‖f y‖ ∂(lebesgue n)) := by
  rw [(strict_superlevel_open f hf hi _).measure_eq_iSup_isCompact]
  exact iSup_le (fun K => iSup_le (fun hKE => iSup_le (fun hK =>
    compact_level_bound f hf hi α hα K hK hKE)))

theorem maximal_finite_ae (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (hi : Integrable f (lebesgue n)) :
    ∀ᵐ x ∂(lebesgue n), maximal f hf x < ∞ := by
  let C : ℝ≥0∞ := (3 : ℝ≥0∞) ^ n * ENNReal.ofReal (∫ y, ‖f y‖ ∂(lebesgue n))
  have hC : C ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ENNReal.ofReal_ne_top
  have ht : Tendsto (fun k : ℕ => C * (k : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul (a := C) ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hC)
  have hb : ∀ᶠ k : ℕ in atTop,
      lebesgue n {x | maximal f hf x = ∞} ≤ C * (k : ℝ≥0∞)⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    calc
      _ ≤ lebesgue n {x | ENNReal.ofReal (k : ℝ) < maximal f hf x} :=
        measure_mono (fun x hx => by
          change maximal f hf x = ∞ at hx
          simp only [mem_ofPred_eq, hx, ENNReal.ofReal_lt_top])
      _ ≤ _ := by
        simpa only [ENNReal.ofReal_natCast, C, mul_assoc, mul_comm, mul_left_comm] using
          maximal_weak11 f hf hi (k : ℝ) (by exact_mod_cast hk)
  have hs : lebesgue n {x | maximal f hf x = ∞} = 0 :=
    le_antisymm (ge_of_tendsto ht hb) zero_le
  apply ae_iff.mpr
  simpa only [not_lt, top_le_iff] using hs

end D11.Ch13.MaximalWeak11
