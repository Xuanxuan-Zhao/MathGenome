import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.BlaschkeProducts
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyLogModulus
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexConjugate Classical

namespace ExpandedFA.PartIV.BlaschkeProducts
open HardyDiskSpec

lemma mem_disk_iff (z : ℂ) : z ∈ disk ↔ ‖z‖ < 1 := by
  simp [disk]

theorem inner_nonzero : Spec.InnerNonzero := by
  intro f hf he
  have hh := hf.2
  rw [he] at hh
  simp at hh
  have h1 := congrArg (fun μ : Measure HardyDiskSpec.Circle => μ Set.univ) hh
  simp at h1

theorem inner_bound : Spec.InnerBound := by
  intro f hf z hz
  exact HardyLogModulus.evaluation_norm_le_of_boundary_norm_le
    (hf.2.mono fun _ ht => ht.le) hz

theorem zero_orders_finite : Spec.ZeroOrdersFinite := by
  intro f hf z hz
  obtain ⟨w, hw, hfw⟩ := HardyLogModulus.exists_nonzero_evaluation hf
  exact (HardyDisk.analytic_evaluation f).analyticOrderAt_ne_top_of_isPreconnected
    (convex_ball (0 : ℂ) 1).isPreconnected hw hz
    (by rw [(HardyDisk.analytic_evaluation f w hw).analyticOrderAt_eq_zero.mpr hfw]; simp)

theorem zeros_correct : Spec.ZerosCorrect := by
  intro f hf z hz
  constructor
  · rintro ⟨⟨⟨w, n⟩, hw, hn⟩, he⟩
    change w = z at he
    subst w
    dsimp at hn
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (by omega)
  · intro he
    have hn : analyticOrderNatAt (eval f) z ≠ 0 := by
      intro h
      have hc := Nat.cast_analyticOrderNatAt (zero_orders_finite f hf z hz)
      rw [h] at hc
      have : analyticOrderAt (eval f) z = 0 := hc.symm
      exact ((HardyDisk.analytic_evaluation f z hz).analyticOrderAt_eq_zero.mp this) he
    exact ⟨⟨(z, 0), hz, Nat.pos_of_ne_zero hn⟩, rfl⟩

theorem origin_interpretation : Spec.OriginInterpretation := by
  funext z
  simp [factor]

theorem finite_interpretation : Spec.FiniteInterpretation := by
  intro ι _ a
  funext z
  exact tprod_fintype (fun j => factor (a j) z)

theorem empty_interpretation : Spec.EmptyInterpretation := by
  intro ι _ a
  funext z
  simp [familyProduct]

lemma denominator_ne_zero {a z : ℂ} (ha : a ∈ disk) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hn : ‖conj a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg a) hz) ((mem_disk_iff a).mp ha)
  rw [← h, norm_one] at hn
  exact (lt_irrefl _ hn)

lemma norm_phase {a : ℂ} (ha : a ≠ 0) : ‖(‖a‖ : ℂ) / a‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
  exact div_self (norm_ne_zero_iff.mpr ha)

lemma analyticAt_factor_closed {a z : ℂ} (ha : a ∈ disk) (hz : ‖z‖ ≤ 1) :
    AnalyticAt ℂ (factor a) z := by
  by_cases h : a = 0
  · subst a
    rw [origin_interpretation]
    exact analyticAt_id
  · have he : factor a = fun w => ((‖a‖ : ℂ) / a) * ((a - w) / (1 - conj a * w)) := by
      funext w
      simp [factor, h]
    rw [he]
    exact analyticAt_const.mul ((analyticAt_const.sub analyticAt_id).div
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
      (denominator_ne_zero ha hz))


theorem factor_analytic : Spec.FactorAnalytic := by
  intro a ha z hz
  exact analyticAt_factor_closed ha ((mem_disk_iff z).mp hz).le

theorem factor_zeros : Spec.FactorZeros := by
  intro a ha z hz
  by_cases h : a = 0
  · simp [factor, h]
  · have hn : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h)
    simp only [factor, ite_eq_right h, mul_eq_zero, div_eq_zero_iff]
    rw [or_iff_right hn, or_iff_left (denominator_ne_zero ha ((mem_disk_iff z).mp hz).le)]
    simpa only [h, false_or] using (sub_eq_zero : a - z = 0 ↔ a = z).trans eq_comm

lemma norm_denominator_sq_sub (a z : ℂ) :
    ‖1 - conj a * z‖ ^ 2 - ‖a - z‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, map_mul,
    Complex.normSq_conj, map_one, one_mul]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma norm_factor_of_ne_zero {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    ‖factor a z‖ = ‖a - z‖ / ‖1 - conj a * z‖ := by
  simp only [factor, ite_eq_right ha, norm_mul, norm_phase ha, one_mul, norm_div]

lemma factor_bound_closed {a z : ℂ} (ha : a ∈ disk) (hz : ‖z‖ ≤ 1) :
    ‖factor a z‖ ≤ 1 := by
  by_cases h : a = 0
  · simpa [factor, h] using hz
  rw [norm_factor_of_ne_zero h, div_le_one (norm_pos_iff.mpr (denominator_ne_zero ha hz))]
  have hsq := norm_denominator_sq_sub a z
  have ha' := (mem_disk_iff a).mp ha
  have haa : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hzz : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  nlinarith [mul_nonneg haa hzz, norm_nonneg (a - z), norm_nonneg (1 - conj a * z)]

theorem factor_bound : Spec.FactorBound := by
  intro a ha z hz
  exact factor_bound_closed ha ((mem_disk_iff z).mp hz).le

theorem factor_boundary : Spec.FactorBoundary := by
  intro a ha z hz
  by_cases h : a = 0
  · simpa [factor, h] using hz
  rw [norm_factor_of_ne_zero h]
  have hs := norm_denominator_sq_sub a z
  rw [hz] at hs
  have hn : ‖a - z‖ = ‖1 - conj a * z‖ := by
    nlinarith [norm_nonneg (a - z), norm_nonneg (1 - conj a * z)]
  rw [hn]
  exact div_self (norm_ne_zero_iff.mpr (denominator_ne_zero ha hz.le))

lemma phase_mul_norm {a : ℂ} (ha : a ≠ 0) :
    ((‖a‖ : ℂ) / a) * (‖a‖ : ℂ) = conj a := by
  calc
    _ = (‖a‖ : ℂ) ^ 2 / a := by ring
    _ = (a * conj a) / a := by rw [Complex.mul_conj', ← Complex.ofReal_pow]
    _ = conj a := by field_simp

lemma one_sub_factor {a z : ℂ} (ha : a ≠ 0) (hd : 1 - conj a * z ≠ 0) :
    1 - factor a z = ((1 - ‖a‖ : ℝ) : ℂ) *
      (1 + ((‖a‖ : ℂ) / a) * z) / (1 - conj a * z) := by
  have hp : ((‖a‖ : ℂ) / a) * a = (‖a‖ : ℂ) := div_mul_cancel₀ _ ha
  have hn := phase_mul_norm ha
  rw [factor, ite_eq_right ha]
  push_cast
  apply (eq_div_iff hd).mpr
  rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hd]
  linear_combination -hp + z * hn

theorem factor_estimate : Spec.FactorEstimate := by
  intro a ha r hr0 hr1 z hz
  have hrp : 0 < 1 - r := sub_pos.mpr hr1
  have hz1 : ‖z‖ ≤ 1 := hz.trans hr1.le
  have hC : 1 + r ≤ (1 + r) / (1 - r) := by
    apply (le_div_iff₀ hrp).mpr
    nlinarith
  by_cases h : a = 0
  · calc
      ‖factor a z - 1‖ = ‖z - 1‖ := by simp [factor, h]
      _ ≤ ‖z‖ + 1 := by simpa using norm_sub_le z (1 : ℂ)
      _ ≤ 1 + r := by linarith
      _ ≤ ((1 + r) / (1 - r)) * (1 - ‖a‖) := by simpa [h] using hC
  · have hd : 1 - conj a * z ≠ 0 := denominator_ne_zero ha hz1
    have hden : 1 - r ≤ ‖1 - conj a * z‖ := by
      calc
        1 - r ≤ 1 - ‖conj a * z‖ := by
          gcongr
          rw [norm_mul, Complex.norm_conj]
          exact (mul_le_of_le_one_left (norm_nonneg z) ((mem_disk_iff a).mp ha).le).trans hz
        _ ≤ ‖1 - conj a * z‖ := by simpa using norm_sub_norm_le (1 : ℂ) (conj a * z)
    have hnum : ‖1 + ((‖a‖ : ℂ) / a) * z‖ ≤ 1 + r := by
      calc
        _ ≤ 1 + ‖((‖a‖ : ℂ) / a) * z‖ := by simpa only [norm_one] using norm_add_le (1 : ℂ) (((‖a‖ : ℂ) / a) * z)
        _ = 1 + ‖z‖ := by rw [norm_mul, norm_phase h, one_mul]
        _ ≤ 1 + r := by linarith
    have ha' : 0 ≤ 1 - ‖a‖ := sub_nonneg.mpr ((mem_disk_iff a).mp ha).le
    rw [norm_sub_rev, one_sub_factor h hd, norm_div, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg ha']
    calc
      _ ≤ (1 - ‖a‖) * (1 + r) / (1 - r) := by
        exact div_le_div₀ (mul_nonneg ha' (by linarith))
          (mul_le_mul_of_nonneg_left hnum ha') hrp hden
      _ = _ := by ring


/-- Convergence on every compact subdisk is unconditional in the zero index. -/
lemma family_uniform_closedBall {ι : Type*} (a : ι → ℂ)
    (ha : ∀ j, a j ∈ disk) (hs : Summable (fun j => 1 - ‖a j‖))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasProdUniformlyOn (fun j => factor (a j)) (familyProduct a)
      (Metric.closedBall (0 : ℂ) r) := by
  have hsum := hs.mul_left ((1 + r) / (1 - r))
  have hh := hsum.hasProdUniformlyOn_one_add (f := fun j z => factor (a j) z - 1)
    (isCompact_closedBall (0 : ℂ) r)
    (Eventually.of_forall (fun j z hz => factor_estimate (a j) (ha j) r hr0 hr1 z
      (by simpa using hz)))
    (fun j => ((factor_analytic (a j) (ha j)).continuousOn.mono (by
      intro z hz
      exact (mem_disk_iff z).mpr ((by simpa using hz : ‖z‖ ≤ r).trans_lt hr1))).sub
        continuousOn_const)
  convert! hh using 1 <;> simp only [add_sub_cancel]
  unfold familyProduct
  rfl

theorem family_convergence : Spec.FamilyConvergence := by
  intro ι a ha hs
  apply hasProdLocallyUniformlyOn_of_forall_compact (s := disk) Metric.isOpen_ball
  intro K hK hKC
  obtain ⟨r, hr, hKr⟩ := exists_pos_lt_subset_ball (by norm_num : (0 : ℝ) < 1)
    hKC.isClosed hK
  exact (family_uniform_closedBall a ha hs hr.1.le hr.2).mono
    (fun z hz => Metric.ball_subset_closedBall (hKr hz))

theorem family_holomorphic : Spec.FamilyHolomorphic := by
  intro ι a ha hs
  apply (family_convergence ι a ha hs).differentiableOn _ Metric.isOpen_ball
  filter_upwards with s
  exact DifferentiableOn.fun_finsetProd (fun j _ => (factor_analytic (a j) (ha j)).differentiableOn)

lemma family_hasProd {ι : Type*} (a : ι → ℂ)
    (ha : ∀ j, a j ∈ disk) (hs : Summable (fun j => 1 - ‖a j‖))
    {z : ℂ} (hz : z ∈ disk) : HasProd (fun j => factor (a j) z) (familyProduct a z) := by
  exact (family_uniform_closedBall a ha hs (norm_nonneg z) ((mem_disk_iff z).mp hz)).hasProd
    (by simp)

lemma family_norm_le_one {ι : Type*} (a : ι → ℂ)
    (ha : ∀ j, a j ∈ disk) (hs : Summable (fun j => 1 - ‖a j‖))
    {z : ℂ} (hz : z ∈ disk) : ‖familyProduct a z‖ ≤ 1 := by
  apply le_of_tendsto (family_hasProd a ha hs hz).norm
  filter_upwards with s
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => factor_bound (a j) (ha j) z hz)

lemma summable_norm_factor_sub_one {ι : Type*} (a : ι → ℂ)
    (ha : ∀ j, a j ∈ disk) (hs : Summable (fun j => 1 - ‖a j‖))
    {z : ℂ} (hz : z ∈ disk) : Summable (fun j => ‖factor (a j) z - 1‖) := by
  exact (hs.mul_left ((1 + ‖z‖) / (1 - ‖z‖))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun j => factor_estimate (a j) (ha j) ‖z‖
      (norm_nonneg z) ((mem_disk_iff z).mp hz) z le_rfl)

theorem family_zeros : Spec.FamilyZeros := by
  intro ι a ha hs z hz
  constructor
  · intro he
    by_contra h
    have hn : ∀ j, factor (a j) z ≠ 0 := by
      intro j
      rw [ne_eq, factor_zeros (a j) (ha j) z hz]
      exact fun hj => h ⟨j, hj⟩
    have hprod := tprod_one_add_ne_zero_of_summable
      (f := fun j => factor (a j) z - 1) (by simpa only [add_sub_cancel] using hn)
      (summable_norm_factor_sub_one a ha hs hz)
    apply hprod
    simpa only [familyProduct, add_sub_cancel] using he
  · rintro ⟨j, hj⟩
    exact tprod_of_exists_eq_zero ⟨j, (factor_zeros (a j) (ha j) z hz).mpr hj⟩


/-- A bound for the analytic values constructs a vector in the canonical lp
Hardy model; the analytic function is not used as a replacement model. -/
lemma hardy_of_bound_one {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F disk)
    (hb : ∀ z ∈ disk, ‖F z‖ ≤ 1) :
    ∃ f : H2, Set.EqOn (eval f) F disk ∧ ‖f‖ ≤ 1 := by
  apply HardyDisk.hardy_of_circleBound hF (by norm_num : (0 : ℝ) ≤ 1)
  intro r hr0 hr1
  let g := HardyDisk.circleValuesLp F hF.continuousOn r hr0 hr1
  have hg := HardyDisk.circleValuesLp_coe F hF.continuousOn r hr0 hr1
  refine ⟨g, hg, ?_⟩
  have hn : ‖g‖ ≤ 1 * ‖(fourierLp (T := 2 * Real.pi) 2 0 : BoundaryL2)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hg, coeFn_fourierLp (T := 2 * Real.pi) 2 0] with t ht hm
    rw [ht, hm, HardyDisk.norm_fourier_point, mul_one]
    exact hb _ (HardyDisk.radial_point_mem_disk hr0 hr1 t)
  simpa only [(orthonormal_fourier (T := 2 * Real.pi)).norm_eq_one, mul_one] using hn

theorem family_hardy : Spec.FamilyHardy := by
  intro ι a ha hs
  exact hardy_of_bound_one (family_holomorphic ι a ha hs)
    (fun _ hz => family_norm_le_one a ha hs hz)

lemma countable_of_summable_deficits {ι : Type*} (a : ι → ℂ)
    (ha : ∀ j, a j ∈ disk) (hs : Summable (fun j => 1 - ‖a j‖)) : Countable ι := by
  have he : Function.support (fun j => 1 - ‖a j‖) = Set.univ := by
    ext j
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (sub_pos.mpr ((mem_disk_iff (a j)).mp (ha j)))
  have hc := hs.countable_support
  rw [he] at hc
  exact Set.countable_univ_iff.mp hc

lemma canonical_convergence_of_summability (hs : Spec.ZeroSummability) :
    Spec.CanonicalConvergence := by
  intro f hf
  exact family_convergence (ZeroOccurrence f) (@zeroPoint f) (fun j => j.property.1) (hs f hf)

lemma canonical_inner_of_family_inner (hs : Spec.ZeroSummability) (hi : Spec.FamilyInner) :
    Spec.CanonicalInner := by
  intro f hf
  exact hi (ZeroOccurrence f) (@zeroPoint f) (fun j => j.property.1) (hs f hf)

lemma zero_countability_of_summability (hs : Spec.ZeroSummability) : Spec.ZeroCountability := by
  intro f hf
  exact countable_of_summable_deficits (@zeroPoint f) (fun j => j.property.1) (hs f hf)

/-- The coefficient boundary agrees with continuous boundary data whenever the
analytic values extend continuously to the closed disk. -/
lemma boundary_eq_of_continuousOn_closedBall {f : H2} {F : ℂ → ℂ}
    (hF : ContinuousOn F (Metric.closedBall 0 1)) (he : Set.EqOn (eval f) F disk) :
    ∀ᵐ t ∂HardyLogModulus.circleMeasure,
      boundary f t = F (HardyLogModulus.circlePoint t) := by
  let r : ℕ → ℝ := fun n => (n : ℝ) / ((n : ℝ) + 1)
  have hr0 (n : ℕ) : 0 ≤ r n := by positivity
  have hr1 (n : ℕ) : r n < 1 := by
    apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    linarith
  have hr : Tendsto r atTop (𝓝 1) := tendsto_natCast_div_add_atTop (1 : ℝ)
  obtain ⟨k, hk, hkae⟩ := HardyLogModulus.exists_subseq_radial_ae f hr0 hr1 hr
  filter_upwards [hkae] with t ht
  have hp : Tendsto (fun n => (r (k n) : ℂ) * HardyLogModulus.circlePoint t)
      atTop (𝓝 (HardyLogModulus.circlePoint t)) := by
    simpa using ((Complex.continuous_ofReal.tendsto 1).comp (hr.comp hk.tendsto_atTop)).mul_const
      (HardyLogModulus.circlePoint t)
  have hm : ∀ n, (r (k n) : ℂ) * HardyLogModulus.circlePoint t ∈ Metric.closedBall 0 1 := by
    intro n
    exact Metric.ball_subset_closedBall (HardyDisk.radial_point_mem_disk (hr0 _) (hr1 _) t)
  have hlim := (hF _ (by simp [HardyLogModulus.norm_circlePoint] :
    HardyLogModulus.circlePoint t ∈ Metric.closedBall 0 1)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hp, Eventually.of_forall hm⟩)
  exact tendsto_nhds_unique ht (hlim.congr' (Eventually.of_forall (fun n =>
    (he (HardyDisk.radial_point_mem_disk (hr0 _) (hr1 _) t)).symm)))

theorem finite_inner : Spec.FiniteInner := by
  intro ι a ha s
  have han : AnalyticOnNhd ℂ (finiteProduct a s) (Metric.closedBall 0 1) := by
    intro z hz
    exact s.analyticAt_fun_prod (fun j _ => analyticAt_factor_closed (ha j) (by simpa using hz))
  have hdiff : DifferentiableOn ℂ (finiteProduct a s) disk :=
    han.differentiableOn.mono Metric.ball_subset_closedBall
  have hb : ∀ z ∈ disk, ‖finiteProduct a s z‖ ≤ 1 := by
    intro z hz
    exact (Finset.norm_prod_le _ _).trans
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => factor_bound (a j) (ha j) z hz))
  obtain ⟨b, he, hbn⟩ := hardy_of_bound_one hdiff hb
  refine ⟨b, ⟨⟨1, fun z hz => (he hz) ▸ hb z hz⟩, ?_⟩, he⟩
  filter_upwards [boundary_eq_of_continuousOn_closedBall han.continuousOn he] with t ht
  rw [ht]
  simp only [finiteProduct, norm_prod]
  exact Finset.prod_eq_one (fun j _ => factor_boundary (a j) (ha j) _ (HardyLogModulus.norm_circlePoint t))

/-- Disk bounds pass to the canonical coefficient boundary by radial convergence. -/
lemma boundary_norm_le_one {f : H2} (hb : ∀ z ∈ disk, ‖eval f z‖ ≤ 1) :
    ∀ᵐ t ∂HardyLogModulus.circleMeasure, ‖boundary f t‖ ≤ 1 := by
  let r : ℕ → ℝ := fun n => (n : ℝ) / ((n : ℝ) + 1)
  have hr0 (n : ℕ) : 0 ≤ r n := by positivity
  have hr1 (n : ℕ) : r n < 1 := by
    apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    linarith
  obtain ⟨k, _, hk⟩ := HardyLogModulus.exists_subseq_radial_ae f hr0 hr1
    (tendsto_natCast_div_add_atTop (1 : ℝ))
  filter_upwards [hk] with t ht
  exact le_of_tendsto ht.norm (Eventually.of_forall fun n =>
    hb _ (HardyDisk.radial_point_mem_disk (hr0 _) (hr1 _) t))

/-- A boundary contraction of full Hardy norm has modulus one almost everywhere. -/
lemma inner_of_bound_and_norm {f : H2} (hb : ∀ z ∈ disk, ‖eval f z‖ ≤ 1)
    (hn : ‖f‖ = 1) : IsInner f := by
  refine ⟨⟨1, hb⟩, ?_⟩
  have hbound := boundary_norm_le_one hb
  have hi : Integrable (fun t => ‖boundary f t‖ ^ 2) HardyLogModulus.circleMeasure := by
    simpa using ((Lp.memLp (boundary f)).norm_rpow (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)).integrable (by norm_num)
  have hle : (fun t => ‖boundary f t‖ ^ 2) ≤ᵐ[HardyLogModulus.circleMeasure] fun _ => 1 := by
    filter_upwards [hbound] with t ht
    nlinarith [norm_nonneg (boundary f t)]
  have he : ∀ᵐ t ∂HardyLogModulus.circleMeasure, ‖boundary f t‖ ^ 2 = 1 := by
    apply (integral_eq_iff_of_ae_le hi (integrable_const (1 : ℝ)) hle).mp
    rw [← HardyLogModulus.boundaryL2_norm_sq, boundary.norm_map, hn]
    simp
  filter_upwards [he] with t ht
  nlinarith [norm_nonneg (boundary f t)]

/-- Finite and complementary products split the same unconditional product. -/
lemma family_split {ι : Type*} (a : ι → ℂ) (ha : ∀ j, a j ∈ disk)
    (hs : Summable (fun j => 1 - ‖a j‖)) (s : Finset ι) {z : ℂ} (hz : z ∈ disk) :
    familyProduct a z = finiteProduct a s z *
      familyProduct (fun j : {j // j ∉ s} => a j) z := by
  classical
  have ht := family_hasProd (fun j : {j // j ∉ s} => a j) (fun j => ha j)
    (hs.subtype _) hz
  have hf : Multipliable (fun j : (s : Set ι) => factor (a j) z) := (hasProd_fintype _).multipliable
  have he := Multipliable.tprod_mul_tprod_compl
    (f := fun j => factor (a j) z) (s := (s : Set ι)) hf ht.multipliable
  convert! he.symm using 1
  congr 1
  exact (s.tprod_subtype' (fun j => factor (a j) z)).symm

/-- Complementary products tend to one; this statement also permits zero factors
in the initial product and therefore handles zeros at the origin. -/
lemma family_tail_tendsto_one {ι : Type*} (a : ι → ℂ) (ha : ∀ j, a j ∈ disk)
    (hs : Summable (fun j => 1 - ‖a j‖)) {z : ℂ} (hz : z ∈ disk) :
    Tendsto (fun s : Finset ι => familyProduct (fun j : {j // j ∉ s} => a j) z)
      atTop (𝓝 1) := by
  classical
  let v : Finset ι → ι → ℂ := fun s j => if j ∈ s then 0 else factor (a j) z - 1
  have hv (j : ι) : Tendsto (fun s => v s j) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({j} : Finset ι)] with s hs
    have hj : j ∈ s := hs (Finset.mem_singleton_self j)
    simp [v, hj]
  have hdom : ∀ᶠ s in (atTop : Filter (Finset ι)), ∀ j, ‖v s j‖ ≤ ‖factor (a j) z - 1‖ := by
    filter_upwards with s j
    dsimp [v]
    split_ifs <;> simp
  have hlim := tendsto_tprod_one_add_of_dominated_convergence
    (summable_norm_factor_sub_one a ha hs hz) hv hdom
  have he (s : Finset ι) : (∏' j, (1 + v s j)) =
      familyProduct (fun j : {j // j ∉ s} => a j) z := by
    change (∏' j, (1 + v s j)) = ∏' j : ({j | j ∉ s} : Set ι), factor (a j) z
    rw [tprod_subtype {j | j ∉ s} (fun j => factor (a j) z)]
    apply tprod_congr
    intro j
    by_cases hj : j ∈ s <;> simp [v, hj, Set.mulIndicator]
  simpa only [he, add_zero, tprod_one] using hlim

theorem family_inner : Spec.FamilyInner := by
  intro ι a ha hs
  obtain ⟨b, hb, hbn⟩ := family_hardy ι a ha hs
  have hbb : ∀ z ∈ disk, ‖eval b z‖ ≤ 1 := fun z hz =>
    (hb hz) ▸ family_norm_le_one a ha hs hz
  have htbound (s : Finset ι) :
      ‖familyProduct (fun j : {j // j ∉ s} => a j) 0‖ ≤ ‖b‖ := by
    obtain ⟨p, hp, hpe⟩ := finite_inner ι a ha s
    obtain ⟨q, hq, _⟩ := family_hardy {j // j ∉ s} (fun j => a j)
      (fun j => ha j) (hs.subtype _)
    have hmul : ∀ᵐ t ∂HardyLogModulus.circleMeasure,
        boundary b t = boundary p t * boundary q t := by
      apply HardyLogModulus.boundary_mul_of_eval_mul
      intro z hz
      rw [hb hz, hpe hz, hq hz]
      exact family_split a ha hs s hz
    have hn : ‖q‖ ^ 2 = ‖b‖ ^ 2 := by
      rw [← boundary.norm_map q, ← boundary.norm_map b,
        HardyLogModulus.boundaryL2_norm_sq, HardyLogModulus.boundaryL2_norm_sq]
      apply integral_congr_ae
      filter_upwards [hmul, hp.2] with t ht hpt
      rw [ht, norm_mul, hpt, one_mul]
    have hqb : ‖q‖ ≤ ‖b‖ := by nlinarith [norm_nonneg q, norm_nonneg b]
    have h0 : (0 : ℂ) ∈ disk := by simp [disk]
    rw [← hq h0]
    calc
      ‖eval q 0‖ ≤ ‖q‖ := by simpa using HardyDisk.evaluation_bound q 0 h0
      _ ≤ ‖b‖ := hqb
  have hbn' : 1 ≤ ‖b‖ := by
    have ht := (family_tail_tendsto_one a ha hs (by simp [disk] : (0 : ℂ) ∈ disk)).norm
    simpa using le_of_tendsto ht (Eventually.of_forall htbound)
  exact ⟨b, inner_of_bound_and_norm hbb (le_antisymm hbn hbn'), hb⟩

lemma factor_order {a : ℂ} (ha : a ∈ disk) : analyticOrderAt (factor a) a = 1 := by
  by_cases h : a = 0
  · subst a
    rw [origin_interpretation]
    change analyticOrderAt (id : ℂ → ℂ) 0 = 1
    exact analyticOrderAt_id
  let g : ℂ → ℂ := fun w => -((‖a‖ : ℂ) / a) / (1 - conj a * w)
  have hg : AnalyticAt ℂ g a := analyticAt_const.div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    (denominator_ne_zero ha ((mem_disk_iff a).mp ha).le)
  have hga : g a ≠ 0 := by
    apply div_ne_zero
    · exact neg_ne_zero.mpr (div_ne_zero (by exact_mod_cast norm_ne_zero_iff.mpr h) h)
    · exact denominator_ne_zero ha ((mem_disk_iff a).mp ha).le
  have he : factor a = (fun w => w - a) * g := by
    funext w
    simp only [factor, ite_eq_right h, Pi.mul_apply, g]
    ring
  rw [he, analyticOrderAt_mul (f := fun w => w - a) (analyticAt_id.sub analyticAt_const) hg,
    analyticOrderAt_id_sub_const_self, hg.analyticOrderAt_eq_zero.mpr hga, add_zero]

lemma family_analytic {ι : Type} (a : ι → ℂ) (ha : ∀ j, a j ∈ disk)
    (hs : Summable (fun j => 1 - ‖a j‖)) : AnalyticOnNhd ℂ (familyProduct a) disk :=
  (family_holomorphic ι a ha hs).analyticOnNhd Metric.isOpen_ball

lemma finite_fiber {ι : Type} (a : ι → ℂ) (ha : ∀ j, a j ∈ disk)
    (hs : Summable (fun j => 1 - ‖a j‖)) {z : ℂ} (hz : z ∈ disk) :
    Set.Finite {j | a j = z} := by
  have hh : Summable (fun _ : ({j | a j = z} : Set ι) => 1 - ‖z‖) := by
    exact (hs.subtype {j | a j = z}).congr (fun j => by
      change 1 - ‖a j.val‖ = 1 - ‖z‖
      rw [j.property])
  letI : Finite ({j | a j = z} : Set ι) := Finite.of_summable_const (sub_pos.mpr ((mem_disk_iff z).mp hz)) hh
  exact Set.finite_coe_iff.mp (inferInstance : Finite ({j | a j = z} : Set ι))

/-- The local order is exactly the number of occurrences at the point. -/
lemma family_order {ι : Type} (a : ι → ℂ) (ha : ∀ j, a j ∈ disk)
    (hs : Summable (fun j => 1 - ‖a j‖)) {z : ℂ} (hz : z ∈ disk) :
    analyticOrderAt (familyProduct a) z = Nat.card {j // a j = z} := by
  classical
  let hfin := finite_fiber a ha hs hz
  let s := hfin.toFinset
  have hmem (j : ι) : j ∈ s ↔ a j = z := by simp [s]
  let tail := familyProduct (fun j : {j // j ∉ s} => a j)
  have htail : AnalyticAt ℂ tail z :=
    family_analytic (fun j : {j // j ∉ s} => a j) (fun j => ha j) (hs.subtype _) z hz
  have htne : tail z ≠ 0 := by
    rw [ne_eq, family_zeros {j // j ∉ s} _ (fun j => ha j) (hs.subtype _) z hz]
    rintro ⟨j, hj⟩
    exact j.property ((hmem j).mpr hj.symm)
  have he : familyProduct a =ᶠ[𝓝 z] (factor z) ^ s.card * tail := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    rw [family_split a ha hs s hw]
    change finiteProduct a s w * tail w = factor z w ^ s.card * tail w
    congr 1
    exact Finset.prod_eq_pow_card (fun j hj => by rw [(hmem j).mp hj])
  rw [analyticOrderAt_congr he,
    analyticOrderAt_mul ((factor_analytic z hz z hz).pow _) htail,
    analyticOrderAt_pow (factor_analytic z hz z hz), factor_order hz,
    htail.analyticOrderAt_eq_zero.mpr htne, add_zero]
  simpa only [nsmul_eq_mul, mul_one] using congrArg (fun n : ℕ => (n : ℕ∞))
    (show s.card = Nat.card {j // a j = z} from by
      convert! (Nat.card_eq_card_finite_toFinset hfin).symm using 1)

/-- The fiber of the actual occurrence index is the finite analytic order. -/
def zeroFiberEquiv (f : H2) (z : ℂ) (hz : z ∈ disk) :
    {j : ZeroOccurrence f // zeroPoint j = z} ≃ Fin (analyticOrderNatAt (eval f) z) where
  toFun j := ⟨j.val.val.2, by
    have hn := j.val.property.2
    have he : j.val.val.1 = z := j.property
    rwa [he] at hn⟩
  invFun n := ⟨⟨(z, n.val), hz, n.isLt⟩, rfl⟩
  left_inv j := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext j.property.symm rfl
  right_inv n := by apply Fin.ext; rfl

lemma canonical_orders_of_summability (hs : Spec.ZeroSummability) : Spec.CanonicalOrders := by
  intro f hf z hz
  rw [canonicalProduct, family_order (@zeroPoint f) (fun j => j.property.1) (hs f hf) hz,
    Nat.card_congr (zeroFiberEquiv f z hz), Nat.card_fin]
  exact Nat.cast_analyticOrderNatAt (zero_orders_finite f (inner_nonzero f hf) z hz)

/-- Remove the quotient singularities whenever the denominator's local orders
are at most the numerator's. Both finite-order assumptions are explicit. -/
lemma analytic_quotient_extension {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F disk) (hG : AnalyticOnNhd ℂ G disk)
    (hFfin : ∀ z ∈ disk, analyticOrderAt F z ≠ ⊤)
    (hGfin : ∀ z ∈ disk, analyticOrderAt G z ≠ ⊤)
    (hord : ∀ z ∈ disk, analyticOrderAt G z ≤ analyticOrderAt F z) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q disk ∧
      (∀ z ∈ disk, F z = G z * Q z) ∧
      (∀ z ∈ disk, G z ≠ 0 → Q z = F z / G z) ∧
      (∀ z ∈ disk, analyticOrderAt G z = analyticOrderAt F z → Q z ≠ 0) := by
  let raw : ℂ → ℂ := fun z => F z / G z
  have hm : MeromorphicOn raw disk := fun z hz => (hF z hz).meromorphicAt.div (hG z hz).meromorphicAt
  let Q := toMeromorphicNFOn raw disk
  have hn (z : ℂ) (hz : z ∈ disk) : MeromorphicNFAt Q z :=
    meromorphicNFOn_toMeromorphicNFOn raw disk hz
  have ho (z : ℂ) (hz : z ∈ disk) : meromorphicOrderAt Q z =
      (analyticOrderNatAt F z : ℤ) - (analyticOrderNatAt G z : ℤ) := by
    rw [meromorphicOrderAt_toMeromorphicNFOn hm hz,
      fun_meromorphicOrderAt_div (hF z hz).meromorphicAt (hG z hz).meromorphicAt,
      (hF z hz).meromorphicOrderAt_eq, (hG z hz).meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt (hFfin z hz),
      ← Nat.cast_analyticOrderNatAt (hGfin z hz)]
    simp
  have hQa : AnalyticOnNhd ℂ Q disk := by
    intro z hz
    apply (hn z hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [ho z hz]
    have hh := hord z hz
    rw [← Nat.cast_analyticOrderNatAt (hFfin z hz),
      ← Nat.cast_analyticOrderNatAt (hGfin z hz), Nat.cast_le] at hh
    exact_mod_cast sub_nonneg.mpr (Int.ofNat_le.mpr hh)
  have hqe (z : ℂ) (hz : z ∈ disk) (hg : G z ≠ 0) : Q z = F z / G z := by
    rw [show Q z = toMeromorphicNFAt raw z z from toMeromorphicNFOn_eq_toMeromorphicNFAt hm hz]
    have hr : AnalyticAt ℂ raw z := (hF z hz).div (hG z hz) hg
    exact congrFun (toMeromorphicNFAt_eq_self.mpr hr.meromorphicNFAt) z
  refine ⟨Q, hQa, ?_, hqe, ?_⟩
  · intro z hz
    by_cases hg : G z = 0
    · have hGo : analyticOrderAt G z ≠ 0 := (hG z hz).analyticOrderAt_ne_zero.mpr hg
      have hFo : analyticOrderAt F z ≠ 0 := by
        intro hf
        exact hGo (le_antisymm (hf ▸ hord z hz) bot_le)
      rw [(hF z hz).analyticOrderAt_ne_zero.mp hFo, hg, zero_mul]
    · rw [hqe z hz hg, mul_div_cancel₀ _ hg]
  · intro z hz he
    apply (hn z hz).meromorphicOrderAt_eq_zero_iff.mp
    rw [ho z hz]
    have he' : analyticOrderNatAt F z = analyticOrderNatAt G z := by
      simp only [analyticOrderNatAt, he]
    simp [he']

/-- Once the Blaschke sum is proved, equality of exact orders constructs the
zero-free holomorphic quotient, including its values at the removed zeros. -/
lemma canonical_analytic_quotient_of_summability (hs : Spec.ZeroSummability)
    (f : H2) (hf : IsInner f) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q disk ∧ (∀ z ∈ disk, Q z ≠ 0) ∧
      (∀ z ∈ disk, eval f z = canonicalProduct f z * Q z) ∧
      (∀ z ∈ disk, canonicalProduct f z ≠ 0 → Q z = eval f z / canonicalProduct f z) := by
  have ho := canonical_orders_of_summability hs f hf
  have hfin := zero_orders_finite f (inner_nonzero f hf)
  have hGa : AnalyticOnNhd ℂ (canonicalProduct f) disk :=
    family_analytic _ (fun j => j.property.1) (hs f hf)
  obtain ⟨Q, hQ, hmul, he, hne⟩ := analytic_quotient_extension (HardyDisk.analytic_evaluation f)
    hGa hfin
    (fun z hz => by rw [ho z hz]; exact hfin z hz) (fun z hz => (ho z hz).le)
  exact ⟨Q, hQ, fun z hz => hne z hz (ho z hz), hmul, he⟩

lemma norm_factor_lower {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk)
    {δ : ℝ} (hδ : 0 ≤ δ) (hd : δ ≤ ‖z - a‖) : δ / 2 ≤ ‖factor a z‖ := by
  by_cases h : a = 0
  · simpa [factor, h] using (show δ / 2 ≤ ‖z‖ by simpa [h] using (half_le_self hδ).trans hd)
  rw [norm_factor_of_ne_zero h]
  apply (le_div_iff₀ (norm_pos_iff.mpr (denominator_ne_zero ha ((mem_disk_iff z).mp hz).le))).mpr
  have hden : ‖1 - conj a * z‖ ≤ 2 := by
    calc
      _ ≤ 1 + ‖conj a * z‖ := by simpa using norm_sub_le (1 : ℂ) (conj a * z)
      _ ≤ 2 := by
        rw [norm_mul, Complex.norm_conj]
        have ha' := ((mem_disk_iff a).mp ha).le
        have hz' := ((mem_disk_iff z).mp hz).le
        nlinarith [mul_le_mul ha' hz' (norm_nonneg z) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [norm_sub_rev] at hd
  nlinarith

/-- An analytic quotient by one disk factor is bounded whenever the original
function is bounded by one. Continuity controls the removed singularity. -/
lemma bound_of_factor_mul {F Q : ℂ → ℂ} (hQ : AnalyticOnNhd ℂ Q disk)
    (hb : ∀ z ∈ disk, ‖F z‖ ≤ 1) {a : ℂ} (ha : a ∈ disk)
    (he : ∀ z ∈ disk, F z = factor a z * Q z) :
    ∃ C : ℝ, ∀ z ∈ disk, ‖Q z‖ ≤ C := by
  have hc := (hQ a ha).continuousAt.norm.eventually_lt_const (lt_add_one ‖Q a‖)
  obtain ⟨δ, hδ, hloc⟩ := Metric.eventually_nhds_iff.mp hc
  refine ⟨max (‖Q a‖ + 1) (2 / δ), fun z hz => ?_⟩
  by_cases hd : dist z a < δ
  · exact (hloc hd).le.trans (le_max_left _ _)
  · have hl : δ / 2 ≤ ‖factor a z‖ := norm_factor_lower ha hz hδ.le (by
      simpa [dist_eq_norm] using le_of_not_gt hd)
    have hm := hb z hz
    rw [he z hz, norm_mul] at hm
    apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hδ).mpr
    nlinarith [norm_nonneg (Q z)]

lemma hardy_of_bounded_analytic {Q : ℂ → ℂ} (hQ : AnalyticOnNhd ℂ Q disk)
    (hb : ∃ C : ℝ, ∀ z ∈ disk, ‖Q z‖ ≤ C) :
    ∃ q : H2, Set.EqOn (eval q) Q disk := by
  let b : HInfinity := ⟨fun z => Q z, hQ.differentiableOn.congr (fun z hz => by
    simp [zeroExtend, hz]), by
      obtain ⟨C, hC⟩ := hb
      exact ⟨C, fun z => hC z z.property⟩⟩
  obtain ⟨q, hq⟩ := HardyDisk.bounded_analytic_coefficients b
  exact ⟨q, fun z hz => hq ⟨z, hz⟩⟩

/-- Removing any single zero from an inner function produces another inner
function, with the quotient extended at the removed zero. -/
lemma inner_divide_factor (f : H2) (hf : IsInner f) {a : ℂ} (ha : a ∈ disk)
    (hfzero : eval f a = 0) :
    ∃ q : H2, IsInner q ∧ ∀ z ∈ disk, eval f z = factor a z * eval q z := by
  have hF := HardyDisk.analytic_evaluation f
  have hG := factor_analytic a ha
  have hfin (z : ℂ) (hz : z ∈ disk) : analyticOrderAt (factor a) z ≠ ⊤ := by
    by_cases h : z = a
    · subst z
      rw [factor_order ha]
      simp
    · rw [(hG z hz).analyticOrderAt_eq_zero.mpr (by
        exact fun he => h ((factor_zeros a ha z hz).mp he))]
      simp
  have hord (z : ℂ) (hz : z ∈ disk) :
      analyticOrderAt (factor a) z ≤ analyticOrderAt (eval f) z := by
    by_cases h : z = a
    · subst z
      rw [factor_order ha]
      exact Order.one_le_iff_ne_zero.mpr ((hF a ha).analyticOrderAt_ne_zero.mpr hfzero)
    · rw [(hG z hz).analyticOrderAt_eq_zero.mpr (by
        exact fun he => h ((factor_zeros a ha z hz).mp he))]
      exact bot_le
  obtain ⟨Q, hQ, hmul, _, _⟩ := analytic_quotient_extension hF hG
    (zero_orders_finite f (inner_nonzero f hf)) hfin hord
  obtain ⟨q, hq⟩ := hardy_of_bounded_analytic hQ
    (bound_of_factor_mul hQ (inner_bound f hf) ha hmul)
  have hmul' : ∀ z ∈ disk, eval f z = factor a z * eval q z := by
    intro z hz
    rw [hq hz]
    exact hmul z hz
  obtain ⟨p, hp, hpe⟩ := finite_inner Unit (fun _ => a) (fun _ => ha) {()}
  have hpe' : Set.EqOn (eval p) (factor a) disk := by
    intro z hz
    simpa [finiteProduct] using hpe hz
  have hboundary : ∀ᵐ t ∂HardyLogModulus.circleMeasure,
      boundary f t = boundary p t * boundary q t := by
    apply HardyLogModulus.boundary_mul_of_eval_mul
    intro z hz
    rw [hpe' hz]
    exact hmul' z hz
  refine ⟨q, ⟨?_, ?_⟩, hmul'⟩
  · obtain ⟨C, hC⟩ := bound_of_factor_mul hQ (inner_bound f hf) ha hmul
    exact ⟨C, fun z hz => (hq hz) ▸ hC z hz⟩
  · filter_upwards [hboundary, hf.2, hp.2] with t ht hft hpt
    rw [ht, norm_mul, hpt, one_mul] at hft
    exact hft

lemma finite_analytic {ι : Type} (a : ι → ℂ) (ha : ∀ j, a j ∈ disk) (s : Finset ι) :
    AnalyticOnNhd ℂ (finiteProduct a s) disk := by
  intro z hz
  exact s.analyticAt_fun_prod (fun j _ => factor_analytic (a j) (ha j) z hz)

lemma finite_order_insert {ι : Type} (a : ι → ℂ) (ha : ∀ j, a j ∈ disk)
    (s : Finset ι) (j : ι) (hj : j ∉ s) {z : ℂ} (hz : z ∈ disk) :
    analyticOrderAt (finiteProduct a (insert j s)) z =
      analyticOrderAt (factor (a j)) z + analyticOrderAt (finiteProduct a s) z := by
  classical
  have he : finiteProduct a (insert j s) = factor (a j) * finiteProduct a s := by
    funext w
    exact Finset.prod_insert hj
  rw [he, analyticOrderAt_mul (factor_analytic (a j) (ha j) z hz) (finite_analytic a ha s z hz)]

lemma finite_order_eq_count {ι : Type} (a : ι → ℂ) (ha : ∀ j, a j ∈ disk)
    (s : Finset ι) {z : ℂ} (hz : z ∈ disk) :
    analyticOrderAt (finiteProduct a s) z = (s.filter (fun j => a j = z)).card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : finiteProduct a ∅ = fun _ => 1 := by ext; simp [finiteProduct]
    rw [he, AnalyticAt.analyticOrderAt_eq_zero (by fun_prop) |>.mpr (by norm_num)]
    simp
  | @insert j s hj ih =>
    rw [finite_order_insert a ha s j hj hz, ih]
    by_cases he : a j = z
    · rw [← he, factor_order (ha j)]
      simp [he, Finset.filter_insert, hj, Nat.cast_add, add_comm]
    · rw [(factor_analytic (a j) (ha j) z hz).analyticOrderAt_eq_zero.mpr (by
        exact fun h => he ((factor_zeros (a j) (ha j) z hz).mp h).symm)]
      simp [Finset.filter_insert, he]

/-- The multiplicities in every finite selection of actual occurrences are
bounded by the analytic multiplicities of the original function. -/
lemma finite_occurrence_orders (f : H2) (hf : f ≠ 0) (s : Finset (ZeroOccurrence f))
    {z : ℂ} (hz : z ∈ disk) :
    analyticOrderAt (finiteProduct (@zeroPoint f) s) z ≤ analyticOrderAt (eval f) z := by
  classical
  rw [finite_order_eq_count (@zeroPoint f) (fun j => j.property.1) s hz,
    ← Nat.cast_analyticOrderNatAt (zero_orders_finite f hf z hz), Nat.cast_le]
  have hc := Finset.card_le_card_of_injOn (s := s.filter (fun j => zeroPoint j = z))
    (t := Finset.range (analyticOrderNatAt (eval f) z)) (fun j : ZeroOccurrence f => j.val.2)
  apply le_trans (hc ?_ ?_) (by simp)
  · intro j hj
    obtain ⟨_, he⟩ := Finset.mem_filter.mp hj
    have hn := j.property.2
    change j.val.1 = z at he
    simpa only [Finset.mem_coe, Finset.mem_range, he] using hn
  · intro j hj k hk he
    obtain ⟨_, hjz⟩ := Finset.mem_filter.mp hj
    obtain ⟨_, hkz⟩ := Finset.mem_filter.mp hk
    apply Subtype.ext
    exact Prod.ext (hjz.trans hkz.symm) he

/-- Successive finite division preserves actual innerness and the disk bound. -/
lemma inner_divide_finite {ι : Type} (a : ι → ℂ) (ha : ∀ j, a j ∈ disk)
    (s : Finset ι) (f : H2) (hf : IsInner f)
    (hord : ∀ z ∈ disk, analyticOrderAt (finiteProduct a s) z ≤ analyticOrderAt (eval f) z) :
    ∃ q : H2, IsInner q ∧ ∀ z ∈ disk, eval f z = finiteProduct a s z * eval q z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => exact ⟨f, hf, by intro z hz; simp [finiteProduct]⟩
  | @insert j s hj ih =>
    have hfzero : eval f (a j) = 0 := by
      apply (HardyDisk.analytic_evaluation f (a j) (ha j)).analyticOrderAt_ne_zero.mp
      apply Order.one_le_iff_ne_zero.mp
      have hh := hord (a j) (ha j)
      rw [finite_order_insert a ha s j hj (ha j), factor_order (ha j)] at hh
      exact (le_add_right le_rfl).trans hh
    obtain ⟨g, hg, hfg⟩ := inner_divide_factor f hf (ha j) hfzero
    have hfgorder (z : ℂ) (hz : z ∈ disk) : analyticOrderAt (eval f) z =
        analyticOrderAt (factor (a j)) z + analyticOrderAt (eval g) z := by
      have he : eval f =ᶠ[𝓝 z] factor (a j) * eval g := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
        exact hfg w hw
      rw [analyticOrderAt_congr he,
        analyticOrderAt_mul (factor_analytic (a j) (ha j) z hz) (HardyDisk.analytic_evaluation g z hz)]
    have hgord (z : ℂ) (hz : z ∈ disk) :
        analyticOrderAt (finiteProduct a s) z ≤ analyticOrderAt (eval g) z := by
      have hh := hord z hz
      rw [finite_order_insert a ha s j hj hz, hfgorder z hz] at hh
      apply (ENat.add_le_add_iff_left ?_).mp hh
      by_cases he : z = a j
      · subst z
        simp [factor_order (ha j)]
      · rw [(factor_analytic (a j) (ha j) z hz).analyticOrderAt_eq_zero.mpr (by
          exact fun h => he ((factor_zeros (a j) (ha j) z hz).mp h))]
        simp
    obtain ⟨q, hq, hgq⟩ := ih g hg hgord
    refine ⟨q, hq, ?_⟩
    intro z hz
    rw [hfg z hz, hgq z hz]
    simp only [finiteProduct, Finset.prod_insert hj]
    ring

lemma inner_divide_occurrences (f : H2) (hf : IsInner f) (s : Finset (ZeroOccurrence f)) :
    ∃ q : H2, IsInner q ∧ ∀ z ∈ disk,
      eval f z = finiteProduct (@zeroPoint f) s z * eval q z :=
  inner_divide_finite _ (fun j => j.property.1) s f hf
    (fun _ hz => finite_occurrence_orders f (inner_nonzero f hf) s hz)

lemma sum_deficits_le_neg_log {ι : Type*} (a : ι → ℝ) (s : Finset ι)
    (ha : ∀ j ∈ s, 0 < a j) {c : ℝ} (hc : 0 < c)
    (hp : c ≤ ∏ j ∈ s, a j) :
    ∑ j ∈ s, (1 - a j) ≤ -Real.log c := by
  calc
    ∑ j ∈ s, (1 - a j) ≤ ∑ j ∈ s, -Real.log (a j) := by
      apply Finset.sum_le_sum
      intro j hj
      linarith [Real.log_le_sub_one_of_pos (ha j hj)]
    _ = -Real.log (∏ j ∈ s, a j) := by
      rw [Real.log_prod (fun j hj => (ha j hj).ne'), Finset.sum_neg_distrib]
    _ ≤ -Real.log c := neg_le_neg (Real.log_le_log hc hp)

lemma inner_remove_origin (f : H2) (hf : IsInner f) :
    ∃ q : H2, IsInner q ∧ eval q 0 ≠ 0 ∧
      ∀ z ∈ disk, z ≠ 0 → analyticOrderAt (eval f) z = analyticOrderAt (eval q) z := by
  have h0 : (0 : ℂ) ∈ disk := by simp [disk]
  let e := zeroFiberEquiv f 0 h0
  have hfin : Set.Finite {j : ZeroOccurrence f | zeroPoint j = 0} := by
    exact Set.finite_coe_iff.mp (Finite.of_injective e e.injective)
  let s := hfin.toFinset
  have hmem (j : ZeroOccurrence f) : j ∈ s ↔ zeroPoint j = 0 := by simp [s]
  have hcard : s.card = analyticOrderNatAt (eval f) 0 := by
    calc
      s.card = Nat.card {j : ZeroOccurrence f // zeroPoint j = 0} := by
        exact (Nat.card_eq_card_finite_toFinset hfin).symm
      _ = analyticOrderNatAt (eval f) 0 := by rw [Nat.card_congr e, Nat.card_fin]
  obtain ⟨q, hq, hmul⟩ := inner_divide_occurrences f hf s
  have horder (z : ℂ) (hz : z ∈ disk) : analyticOrderAt (eval f) z =
      analyticOrderAt (finiteProduct (@zeroPoint f) s) z + analyticOrderAt (eval q) z := by
    have he : eval f =ᶠ[𝓝 z] finiteProduct (@zeroPoint f) s * eval q := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      exact hmul w hw
    rw [analyticOrderAt_congr he,
      analyticOrderAt_mul (finite_analytic (@zeroPoint f) (fun j => j.property.1) s z hz)
        (HardyDisk.analytic_evaluation q z hz)]
  have hs0 : analyticOrderAt (finiteProduct (@zeroPoint f) s) 0 =
      analyticOrderAt (eval f) 0 := by
    rw [finite_order_eq_count (@zeroPoint f) (fun j => j.property.1) s h0,
      Finset.filter_eq_self.mpr (fun j hj => (hmem j).mp hj), hcard,
      Nat.cast_analyticOrderNatAt (zero_orders_finite f (inner_nonzero f hf) 0 h0)]
  have hq0 : eval q 0 ≠ 0 := by
    apply (HardyDisk.analytic_evaluation q 0 h0).analyticOrderAt_eq_zero.mp
    have hh := horder 0 h0
    rw [hs0] at hh
    have hc := ENat.add_right_injective_of_ne_top
      (zero_orders_finite f (inner_nonzero f hf) 0 h0)
    apply hc
    simpa only [add_zero] using hh.symm
  refine ⟨q, hq, hq0, ?_⟩
  intro z hz hne
  have hs : s.filter (fun j => zeroPoint j = z) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro j hj he
    exact hne (he.symm.trans ((hmem j).mp hj))
  simpa [finite_order_eq_count (@zeroPoint f) (fun j => j.property.1) s hz, hs] using horder z hz

lemma zero_summability : Spec.ZeroSummability := by
  intro f hf
  have h0 : (0 : ℂ) ∈ disk := by simp [disk]
  obtain ⟨q, hq, hq0, hqord⟩ := inner_remove_origin f hf
  apply summable_of_sum_le (c := (analyticOrderNatAt (eval f) 0 : ℝ) - Real.log ‖eval q 0‖)
  · intro j
    exact sub_nonneg.mpr ((mem_disk_iff _).mp j.property.1).le
  intro s
  let t := s.filter (fun j => zeroPoint j ≠ 0)
  have ht (j : ZeroOccurrence f) (hj : j ∈ t) : zeroPoint j ≠ 0 :=
    (Finset.mem_filter.mp hj).2
  have horders (z : ℂ) (hz : z ∈ disk) :
      analyticOrderAt (finiteProduct (@zeroPoint f) t) z ≤ analyticOrderAt (eval q) z := by
    by_cases he : z = 0
    · subst z
      have hempty : t.filter (fun j => zeroPoint j = 0) = ∅ := by
        exact Finset.filter_eq_empty_iff.mpr (fun j hj => ht j hj)
      rw [finite_order_eq_count (@zeroPoint f) (fun j => j.property.1) t h0, hempty]
      simp
    · rw [← hqord z hz he]
      exact finite_occurrence_orders f (inner_nonzero f hf) t hz
  obtain ⟨r, hr, hmul⟩ := inner_divide_finite (@zeroPoint f) (fun j => j.property.1) t q hq horders
  have hprod : ‖eval q 0‖ ≤ ∏ j ∈ t, ‖zeroPoint j‖ := by
    calc
      ‖eval q 0‖ = ‖finiteProduct (@zeroPoint f) t 0‖ * ‖eval r 0‖ := by
        rw [hmul 0 h0, norm_mul]
      _ ≤ ‖finiteProduct (@zeroPoint f) t 0‖ :=
        mul_le_of_le_one_right (norm_nonneg _) (inner_bound r hr 0 h0)
      _ = ∏ j ∈ t, ‖zeroPoint j‖ := by
        simp only [finiteProduct, norm_prod]
        apply Finset.prod_congr rfl
        intro j hj
        simp [norm_factor_of_ne_zero (ht j hj)]
  have htbound := sum_deficits_le_neg_log (fun j : ZeroOccurrence f => ‖zeroPoint j‖) t
    (fun j hj => norm_pos_iff.mpr (ht j hj)) (norm_pos_iff.mpr hq0) hprod
  have hcount : (s.filter (fun j => zeroPoint j = 0)).card ≤ analyticOrderNatAt (eval f) 0 := by
    have hh := finite_occurrence_orders f (inner_nonzero f hf) s h0
    rw [finite_order_eq_count (@zeroPoint f) (fun j => j.property.1) s h0,
      ← Nat.cast_analyticOrderNatAt (zero_orders_finite f (inner_nonzero f hf) 0 h0),
      Nat.cast_le] at hh
    exact hh
  have hsum0 : ∑ j ∈ s.filter (fun j => zeroPoint j = 0), (1 - ‖zeroPoint j‖) =
      ((s.filter (fun j => zeroPoint j = 0)).card : ℝ) := by
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    apply Finset.sum_congr rfl
    intro j hj
    simp [(Finset.mem_filter.mp hj).2]
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun j => zeroPoint j = 0)
    (fun j => 1 - ‖zeroPoint j‖)
  change ∑ j ∈ s.filter (fun j => zeroPoint j = 0), (1 - ‖zeroPoint j‖) +
    ∑ j ∈ t, (1 - ‖zeroPoint j‖) = ∑ j ∈ s, (1 - ‖zeroPoint j‖) at hsplit
  rw [← hsplit, hsum0]
  exact add_le_add (by exact_mod_cast hcount) htbound



lemma canonical_norm_dominates_of_summability (hs : Spec.ZeroSummability)
    (f : H2) (hf : IsInner f) {z : ℂ} (hz : z ∈ disk) :
    ‖eval f z‖ ≤ ‖canonicalProduct f z‖ := by
  apply ge_of_tendsto (family_hasProd (@zeroPoint f) (fun j => j.property.1) (hs f hf) hz).norm
  filter_upwards with s
  obtain ⟨q, hq, hmul⟩ := inner_divide_occurrences f hf s
  rw [hmul z hz, norm_mul]
  simpa only [finiteProduct, norm_prod] using
    mul_le_of_le_one_right (norm_nonneg (finiteProduct (@zeroPoint f) s z)) (inner_bound q hq z hz)

lemma quotient_bound_of_summability (hs : Spec.ZeroSummability)
    (f : H2) (hf : IsInner f) {Q : ℂ → ℂ} (hQ : AnalyticOnNhd ℂ Q disk)
    (hmul : ∀ z ∈ disk, eval f z = canonicalProduct f z * Q z) :
    ∀ z ∈ disk, ‖Q z‖ ≤ 1 := by
  have hpoint (z : ℂ) (hz : z ∈ disk) (hne : canonicalProduct f z ≠ 0) : ‖Q z‖ ≤ 1 := by
    have h := canonical_norm_dominates_of_summability hs f hf hz
    rw [hmul z hz, norm_mul] at h
    have hp := norm_pos_iff.mpr hne
    nlinarith
  intro z hz
  have hBa := family_analytic (@zeroPoint f) (fun j => j.property.1) (hs f hf)
  have hBfin : analyticOrderAt (canonicalProduct f) z ≠ ⊤ := by
    rw [canonical_orders_of_summability hs f hf z hz]
    exact zero_orders_finite f (inner_nonzero f hf) z hz
  have hne : ∀ᶠ w in 𝓝[≠] z, canonicalProduct f w ≠ 0 := by
    exact (hBa z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h => hBfin (analyticOrderAt_eq_top.mpr h))
  have hd : ∀ᶠ w in 𝓝[≠] z, w ∈ disk :=
    (show ∀ᶠ w in 𝓝 z, w ∈ disk from Metric.isOpen_ball.mem_nhds hz).filter_mono nhdsWithin_le_nhds
  have ht : Tendsto (fun w : ℂ => ‖Q w‖) (𝓝[≠] z) (𝓝 ‖Q z‖) :=
    (hQ z hz).continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  filter_upwards [hne, hd] with w hw hwd
  exact hpoint w hwd hw

lemma zero_free_quotient_of_summability (hs : Spec.ZeroSummability) : Spec.ZeroFreeQuotient := by
  intro f hf
  obtain ⟨Q, hQ, hne, hmul, he⟩ := canonical_analytic_quotient_of_summability hs f hf
  have hbound := quotient_bound_of_summability hs f hf hQ hmul
  obtain ⟨q, hq, _⟩ := hardy_of_bound_one hQ.differentiableOn hbound
  obtain ⟨b, hb, hbe⟩ := family_inner (ZeroOccurrence f) (@zeroPoint f)
    (fun j => j.property.1) (hs f hf)
  have hboundary : ∀ᵐ t ∂HardyLogModulus.circleMeasure,
      boundary f t = boundary b t * boundary q t := by
    apply HardyLogModulus.boundary_mul_of_eval_mul
    intro z hz
    rw [hbe hz, hq hz]
    exact hmul z hz
  have hqi : IsInner q := by
    refine ⟨⟨1, fun z hz => (hq hz) ▸ hbound z hz⟩, ?_⟩
    filter_upwards [hboundary, hf.2, hb.2] with t ht hft hbt
    rw [ht, norm_mul, hbt, one_mul] at hft
    exact hft
  refine ⟨q, hqi, ?_, ?_, ?_⟩
  · intro z hz
    rw [hq hz]
    exact hne z hz
  · intro z hz
    rw [hq hz]
    exact hmul z hz
  · intro z hz hbz
    rw [hq hz]
    exact he z hz hbz


/-- The actual occurrence family is countable, with no enumeration supplied. -/
theorem zero_countability : Spec.ZeroCountability :=
  zero_countability_of_summability zero_summability

/-- The canonical product converges locally uniformly, including origin zeros. -/
theorem canonical_convergence : Spec.CanonicalConvergence :=
  canonical_convergence_of_summability zero_summability

theorem canonical_inner : Spec.CanonicalInner :=
  canonical_inner_of_family_inner zero_summability family_inner

theorem canonical_orders : Spec.CanonicalOrders :=
  canonical_orders_of_summability zero_summability

/-- Division across every zero is realized by the zero-free inner extension. -/
theorem zero_free_quotient : Spec.ZeroFreeQuotient :=
  zero_free_quotient_of_summability zero_summability

end ExpandedFA.PartIV.BlaschkeProducts
