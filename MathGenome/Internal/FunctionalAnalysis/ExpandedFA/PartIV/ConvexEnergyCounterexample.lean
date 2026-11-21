import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.ConvexEnergyCounterexample
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.ConvexEnergySubendpoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ExpandedFA.PartIV.ConvexEnergyCounterexample

open Spec ConvexEnergySubendpoint.Spec

/-- The representative of a spike agrees with its defining indicator a.e. -/
theorem spike_coe_ae (p : ℝ≥0∞) (a : ℝ) :
    (spike p a : ℝ → ℝ) =ᵐ[unitIntervalMeasure]
      (spikeSet p a).indicator (fun _ => a) :=
  indicatorConstLp_coeFn

/-- The support is inside (0,1), including the boundary case a=1. -/
theorem spikeSet_subset {p : ℝ≥0∞} {a : ℝ} (ha : 1 ≤ a) :
    spikeSet p a ⊆ Ioo (0 : ℝ) 1 := by
  intro x hx
  exact ⟨hx.1, hx.2.trans_le (Real.rpow_le_one_of_one_le_of_nonpos ha
    (neg_nonpos.mpr ENNReal.toReal_nonneg))⟩

/-- The support has precisely the measure prescribed in the source. -/
theorem measure_spikeSet {p : ℝ≥0∞} {a : ℝ} (ha : 1 ≤ a) :
    unitIntervalMeasure (spikeSet p a) = ENNReal.ofReal (a ^ (-p.toReal)) := by
  rw [unitIntervalMeasure, Measure.restrict_apply measurableSet_Ioo,
    inter_eq_left.mpr (spikeSet_subset ha)]
  simp [spikeSet, Real.volume_Ioo]

theorem measureReal_spikeSet {p : ℝ≥0∞} {a : ℝ} (ha : 1 ≤ a) :
    unitIntervalMeasure.real (spikeSet p a) = a ^ (-p.toReal) := by
  rw [measureReal_def, measure_spikeSet ha, ENNReal.toReal_ofReal]
  positivity

/-- All spikes have norm exactly one for finite positive exponents. -/
theorem norm_spike {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    {a : ℝ} (ha : 1 ≤ a) : ‖spike p a‖ = 1 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hp : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hpt).ne'
  rw [spike, norm_indicatorConstLp hp0 hpt, Real.norm_eq_abs,
    abs_of_pos ha0, measureReal_spikeSet ha,
    ← Real.rpow_mul ha0.le]
  have hexp : -p.toReal * (1 / p.toReal) = -1 := by field_simp
  rw [hexp, Real.rpow_neg_one]
  exact mul_inv_cancel₀ ha0.ne'

/-- Composing with a function vanishing at zero produces another constant
indicator. This lemma needs no continuity assumption. -/
theorem comp_spike_ae (p : ℝ≥0∞) (a : ℝ) (F : ℝ → ℝ) (hF : F 0 = 0) :
    (fun x => F (spike p a x)) =ᵐ[unitIntervalMeasure]
      (spikeSet p a).indicator (fun _ => F a) := by
  filter_upwards [spike_coe_ae p a] with x hx
  rw [hx]
  by_cases hs : x ∈ spikeSet p a
  · simp [hs]
  · simp [hs, hF]

/-- Nonlinear differences always vanish off the original support. -/
theorem image_spike_ae (p : ℝ≥0∞) (a : ℝ) (g : ℝ → ℝ) :
    (fun x => g (spike p a x) - g 0) =ᵐ[unitIntervalMeasure]
      (spikeSet p a).indicator (fun _ => g a - g 0) :=
  comp_spike_ae p a (fun t => g t - g 0) (sub_self _)

/-- No image-membership hypothesis is needed: each individual image is simple. -/
theorem memLp_image_spike (p q : ℝ≥0∞) (a : ℝ) (g : ℝ → ℝ) :
    MemLp (fun x => g (spike p a x) - g 0) q unitIntervalMeasure :=
  by
  rw [memLp_congr_ae (image_spike_ae p a g)]
  exact memLp_indicator_const q measurableSet_Ioo.nullMeasurableSet _
    (Or.inr (measure_ne_top _ _))

/-- Energy is exactly the scalar primitive divided by the pth amplitude. -/
theorem integral_primitive_spike {p : ℝ≥0∞} {a : ℝ} (ha : 1 ≤ a)
    (g : ℝ → ℝ) :
    (∫ x, primitive g (spike p a x) ∂unitIntervalMeasure) =
      a ^ (-p.toReal) * primitive g a := by
  rw [integral_congr_ae (comp_spike_ae p a (primitive g) (by simp [primitive])),
    integral_indicator_const _ measurableSet_Ioo, measureReal_spikeSet ha,
    smul_eq_mul]

theorem integrable_primitive_spike (p : ℝ≥0∞) (a : ℝ) (g : ℝ → ℝ) :
    Integrable (fun x => primitive g (spike p a x)) unitIntervalMeasure := by
  rw [← memLp_one_iff_integrable, memLp_congr_ae
    (comp_spike_ae p a (primitive g) (by simp [primitive]))]
  exact memLp_indicator_const 1 measurableSet_Ioo.nullMeasurableSet _
    (Or.inr (measure_ne_top _ _))

/-- The exact finite-exponent norm of the nonlinear difference. -/
theorem image_norm_spike {p q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    {a : ℝ} (ha : 1 ≤ a) (g : ℝ → ℝ) :
    (eLpNorm (fun x => g (spike p a x) - g 0) q unitIntervalMeasure).toReal =
      |g a - g 0| * a ^ (-p.toReal * (1 / q.toReal)) := by
  rw [eLpNorm_congr_ae (image_spike_ae p a g),
    eLpNorm_indicator_const measurableSet_Ioo.nullMeasurableSet hq0 hqt,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_enorm,
    Real.norm_eq_abs, ← measureReal_def, measureReal_spikeSet ha,
    ← Real.rpow_mul (zero_le_one.trans ha)]

/-- Rewriting the exact image norm using the original conjugate exponent. -/
theorem conjugate_image_norm_spike {p : ℝ≥0∞} (hp : 1 < p) (hpt : p ≠ ∞)
    {a : ℝ} (ha : 1 ≤ a) (g : ℝ → ℝ) :
    (eLpNorm (fun x => g (spike p a x) - g 0) (conjugate p)
      unitIntervalMeasure).toReal = |g a - g 0| * a ^ (-(p.toReal - 1)) := by
  have hpR := ConvexEnergySubendpoint.toReal_gt_one hp hpt
  have hqR : (conjugate p).toReal = p.toReal / (p.toReal - 1) := by
    rw [conjugate, ENNReal.toReal_ofReal (by positivity)]
  rw [image_norm_spike
    (ne_of_gt (zero_lt_one.trans (ConvexEnergySubendpoint.conjugate_gt_one hp hpt)))
    (ConvexEnergySubendpoint.conjugate_ne_top p) ha, hqR]
  congr 2
  field_simp

/-- A scalar endpoint value of size a^(p-1) prevents the nonlinear norm
from tending to zero, even while the primitive is small. -/
theorem one_le_image_norm_spike {p : ℝ≥0∞} (hp : 1 < p) (hpt : p ≠ ∞)
    {a : ℝ} (ha : 1 ≤ a) (g : ℝ → ℝ)
    (hg : a ^ (p.toReal - 1) ≤ g a - g 0) :
    1 ≤ (eLpNorm (fun x => g (spike p a x) - g 0) (conjugate p)
      unitIntervalMeasure).toReal := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  rw [conjugate_image_norm_spike hp hpt ha]
  calc
    1 = a ^ (p.toReal - 1) * a ^ (-(p.toReal - 1)) := by
      rw [Real.rpow_neg ha0.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos ha0 _).ne']
    _ ≤ |g a - g 0| * a ^ (-(p.toReal - 1)) :=
      mul_le_mul_of_nonneg_right (hg.trans (le_abs_self _)) (by positivity)

/-- Shrinking supports have vanishing measure whenever amplitudes escape. -/
theorem measure_spikeSet_tendsto {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n) (hat : Tendsto a atTop atTop) :
    Tendsto (fun n => unitIntervalMeasure (spikeSet p (a n))) atTop (𝓝 0) := by
  simp_rw [measure_spikeSet (ha _)]
  simpa only [ENNReal.ofReal_zero, Function.comp_def] using
    (ENNReal.tendsto_ofReal ((tendsto_rpow_neg_atTop
      (ENNReal.toReal_pos hp0 hpt)).comp hat))

/-- Absolute continuity of an individual Lq norm on the shrinking supports. -/
theorem test_indicator_norm_tendsto {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hq : 1 ≤ q) (hqt : q ≠ ∞) {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hat : Tendsto a atTop atTop) {h : ℝ → ℝ} (hh : MemLp h q unitIntervalMeasure) :
    Tendsto (fun n => eLpNorm ((spikeSet p (a n)).indicator h) q unitIntervalMeasure)
      atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hh.eLpNorm_indicator_le hq hqt hε
  have hm := measure_spikeSet_tendsto hp0 hpt ha hat
  filter_upwards [hm.eventually_lt_const hδ] with n hn
  exact hbound _ measurableSet_Ioo.nullMeasurableSet hn.le

/-- Every bounded normalized spike sequence with shrinking supports is weakly
null. Dual representation supplies all continuous linear tests, not merely
bounded or smooth test functions. -/
theorem spike_weakly_converges {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp0 : p ≠ 0) (hpt : p ≠ ∞) (hqt : q ≠ ∞)
    {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n) (hat : Tendsto a atTop atTop) :
    WeaklyConverges unitIntervalMeasure p (fun n => spike p (a n)) 0 := by
  intro L
  obtain ⟨h, hh, _⟩ := ExpandedFA.FunctionSpaces.lp_duality_sigmaFinite
    unitIntervalMeasure p q hpt L
  let w : ℕ → Lp ℝ q unitIntervalMeasure := fun n =>
    ((Lp.memLp h).indicator measurableSet_Ioo.nullMeasurableSet).toLp
      ((spikeSet p (a n)).indicator (h : ℝ → ℝ))
  have hw (n : ℕ) : (w n : ℝ → ℝ) =ᵐ[unitIntervalMeasure]
      (spikeSet p (a n)).indicator (h : ℝ → ℝ) := MemLp.coeFn_toLp _
  have hwn : Tendsto (fun n => ‖w n‖) atTop (𝓝 0) := by
    have ht := test_indicator_norm_tendsto hp0 hpt (Fact.out : 1 ≤ q) hqt ha hat
      (Lp.memLp h)
    have htr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
    simpa only [w, Lp.norm_toLp, ENNReal.toReal_zero, Function.comp_def] using htr
  have heq (n : ℕ) : L (spike p (a n)) =
      ExpandedFA.FunctionSpaces.ScalarLpIntegralPairingSpec.IntegralPairingValue
        unitIntervalMeasure p q (w n)
        (spike p (a n)) := by
    rw [(hh.1 _).2, (ExpandedFA.FunctionSpaces.lp_pairing_integral
      unitIntervalMeasure p q (w n) (spike p (a n))).2]
    apply integral_congr_ae
    filter_upwards [hw n, spike_coe_ae p (a n)] with x hx hxv
    rw [hx, hxv]
    by_cases hs : x ∈ spikeSet p (a n)
    · simp [hs]
    · simp [hs]
  have hbound (n : ℕ) : ‖L (spike p (a n))‖ ≤ ‖w n‖ := by
    rw [heq]
    simpa only [norm_spike hp0 hpt (ha n), mul_one] using
      ExpandedFA.FunctionSpaces.lp_pairing_apply_bound unitIntervalMeasure p q
        (w n) (spike p (a n))
  simpa only [map_zero] using
    (tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun n => norm_nonneg _) hbound hwn))

/-- The bounded strict perturbation does not spoil upper polynomial growth. -/
theorem upperGrowth_add_arctan {p : ℝ≥0∞} {g₀ : ℝ → ℝ}
    (hg : UpperGrowth p g₀) : UpperGrowth p (fun t => g₀ t + Real.arctan t) := by
  obtain ⟨C, hC, hg⟩ := hg
  refine ⟨C + Real.pi / 2, by positivity, fun t => ?_⟩
  have hat : |Real.arctan t| ≤ Real.pi / 2 :=
    (abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan t, Real.arctan_lt_pi_div_two t⟩).le
  have hr : 0 ≤ |t| ^ (p.toReal - 1) := Real.rpow_nonneg (abs_nonneg t) _
  calc
    |g₀ t + Real.arctan t| ≤ |g₀ t| + |Real.arctan t| := abs_add_le _ _
    _ ≤ C * (1 + |t| ^ (p.toReal - 1)) + Real.pi / 2 := add_le_add (hg t) hat
    _ ≤ (C + Real.pi / 2) * (1 + |t| ^ (p.toReal - 1)) := by
      nlinarith [Real.pi_pos]

/-- The added primitive is O(a); after normalization by a^p it vanishes. -/
theorem normalized_arctan_primitive_tendsto {p : ℝ≥0∞}
    (hp : 1 < p) (hpt : p ≠ ∞) {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hat : Tendsto a atTop atTop) :
    Tendsto (fun n => a n ^ (-p.toReal) * primitive Real.arctan (a n))
      atTop (𝓝 0) := by
  have hpR := ConvexEnergySubendpoint.toReal_gt_one hp hpt
  have hbound (n : ℕ) :
      ‖a n ^ (-p.toReal) * primitive Real.arctan (a n)‖ ≤
        (Real.pi / 2) * a n ^ (-(p.toReal - 1)) := by
    have ha0 : 0 < a n := zero_lt_one.trans_le (ha n)
    have hi : ‖primitive Real.arctan (a n)‖ ≤ (Real.pi / 2) * a n := by
      have ht : ∀ t ∈ Set.uIoc (0 : ℝ) (a n), ‖Real.arctan t‖ ≤ Real.pi / 2 := by
        intro t _
        exact (abs_lt.mpr
          ⟨Real.neg_pi_div_two_lt_arctan t, Real.arctan_lt_pi_div_two t⟩).le
      simpa only [primitive, sub_zero, abs_of_pos ha0] using
        intervalIntegral.norm_integral_le_of_norm_le_const ht
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ha0 _)]
    calc
      a n ^ (-p.toReal) * ‖primitive Real.arctan (a n)‖ ≤
          a n ^ (-p.toReal) * ((Real.pi / 2) * a n) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = (Real.pi / 2) * a n ^ (-(p.toReal - 1)) := by
        calc
          _ = (Real.pi / 2) * (a n ^ (-p.toReal) * a n ^ (1 : ℝ)) := by
            rw [Real.rpow_one]
            ring
          _ = _ := by
            rw [← Real.rpow_add ha0]
            congr 2
            ring
  have ht : Tendsto (fun n => (Real.pi / 2) * a n ^ (-(p.toReal - 1))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (((tendsto_rpow_neg_atTop (sub_pos.mpr hpR)).comp hat).const_mul (Real.pi / 2))
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun n => norm_nonneg _) hbound ht)

/-- The entire functional-analytic part and the strict perturbation reduce
the assigned conclusion to the scalar ramp construction. -/
theorem counterexample_of_ramps (hramps : Spec.RampConstruction) : Spec.Counterexample := by
  intro p _ hp hpt
  obtain ⟨g₀, a, hg₀, hm₀, hgrowth₀, hz₀, ha, hat, hsample, henergy⟩ := hramps p hp hpt
  let g : ℝ → ℝ := fun t => g₀ t + Real.arctan t
  have hg : Continuous g := hg₀.add Real.continuous_arctan
  have hstrict : StrictMono g := fun x y hxy =>
    add_lt_add_of_le_of_lt (hm₀ hxy.le) (Real.arctan_strictMono hxy)
  have hz : g 0 = 0 := by simp only [g, hz₀, Real.arctan_zero, add_zero]
  have hsample' (n : ℕ) : a n ^ (p.toReal - 1) ≤ g (a n) - g 0 := by
    rw [hz, sub_zero]
    exact (hsample n).trans (le_add_of_nonneg_right
      (Real.arctan_nonneg.mpr (zero_le_one.trans (ha n))))
  have he (n : ℕ) : primitive g (a n) =
      primitive g₀ (a n) + primitive Real.arctan (a n) :=
    intervalIntegral.integral_add (hg₀.intervalIntegrable _ _)
      (Real.continuous_arctan.intervalIntegrable _ _)
  have he_limit : Tendsto
      (fun n => ∫ x, primitive g (spike p (a n) x) ∂unitIntervalMeasure) atTop (𝓝 0) := by
    simp_rw [integral_primitive_spike (ha _), he, mul_add]
    simpa only [add_zero] using
      henergy.add (normalized_arctan_primitive_tendsto hp hpt ha hat)
  have hnorm (n : ℕ) : ‖spike p (a n)‖ = 1 :=
    norm_spike (ne_of_gt (zero_lt_one.trans hp)) hpt (ha n)
  have himage (n : ℕ) : 1 ≤ (eLpNorm (fun x => g (spike p (a n) x) - g 0)
      (conjugate p) unitIntervalMeasure).toReal :=
    one_le_image_norm_spike hp hpt (ha n) g (hsample' n)
  haveI : Fact (1 ≤ conjugate p) := ⟨(ConvexEnergySubendpoint.conjugate_gt_one hp hpt).le⟩
  haveI := ConvexEnergySubendpoint.conjugate_holder hp hpt
  refine ⟨g, fun n => spike p (a n), hg, hstrict, upperGrowth_add_arctan hgrowth₀, hz,
    spike_weakly_converges (q := conjugate p) (ne_of_gt (zero_lt_one.trans hp)) hpt
      (ConvexEnergySubendpoint.conjugate_ne_top p) ha hat,
    fun n => integrable_primitive_spike p (a n) g, he_limit, hnorm,
    fun n => memLp_image_spike p (conjugate p) (a n) g, himage, ?_, ?_⟩
  · intro h
    have hone : (1 : ℝ) ≤ 0 := ge_of_tendsto h (Eventually.of_forall (fun n => (hnorm n).ge))
    linarith
  · intro h
    have hone : (1 : ℝ) ≤ 0 := ge_of_tendsto h (Eventually.of_forall himage)
    linarith

/-- A continuous rise from zero to H on [b,a], followed by a plateau. -/
def scalarRamp (a b H t : ℝ) : ℝ := H * min 1 (max 0 ((t - b) / (a - b)))

lemma scalarRamp_continuous (a b H : ℝ) : Continuous (scalarRamp a b H) := by
  unfold scalarRamp
  fun_prop

lemma scalarRamp_nonneg {a b H t : ℝ} (hH : 0 ≤ H) : 0 ≤ scalarRamp a b H t := by
  exact mul_nonneg hH (le_min zero_le_one (le_max_left _ _))

lemma scalarRamp_le {a b H t : ℝ} (hH : 0 ≤ H) : scalarRamp a b H t ≤ H := by
  exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hH).trans_eq (mul_one H)

lemma scalarRamp_zero {a b H t : ℝ} (hab : b < a) (ht : t ≤ b) :
    scalarRamp a b H t = 0 := by
  simp [scalarRamp, max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht)
    (sub_pos.mpr hab).le)]

lemma scalarRamp_top {a b H : ℝ} (hab : b < a) : scalarRamp a b H a = H := by
  simp [scalarRamp, div_self (sub_pos.mpr hab).ne']

lemma scalarRamp_monotone {a b H : ℝ} (hab : b < a) (hH : 0 ≤ H) :
    Monotone (scalarRamp a b H) := by
  intro x y hxy
  apply mul_le_mul_of_nonneg_left _ hH
  exact min_le_min_left _ (max_le_max_left _ (div_le_div_of_nonneg_right
    (sub_le_sub_right hxy _) (sub_pos.mpr hab).le))

/-- Choose a scale with growing consecutive height ratios and separated rises. -/
lemma exists_ramp_scale {r : ℝ} (hr : 0 < r) :
    ∃ a : ℕ → ℝ, (∀ n, 1 ≤ a n) ∧ Monotone a ∧ Tendsto a atTop atTop ∧
      (∀ n, 2 * a n ≤ a (n+1)) ∧
      (∀ n : ℕ, ((n : ℝ) + 2) * (a n)^r ≤ (a (n+1))^r) := by
  have hex (n : ℕ) (x : ℝ) : ∃ y : ℝ,
      x + 1 ≤ y ∧ 2*x ≤ y ∧ ((n : ℝ)+2)*x^r ≤ y^r := by
    have he := (tendsto_rpow_atTop hr).eventually_ge_atTop (((n : ℝ)+2)*x^r)
    obtain ⟨y, hy1, hy2, hy3⟩ := ((eventually_ge_atTop (x+1)).and
      ((eventually_ge_atTop (2*x)).and he)).exists
    exact ⟨y, hy1, hy2, hy3⟩
  let step : ℕ → ℝ → ℝ := fun n x => Classical.choose (hex n x)
  have hstep (n : ℕ) (x : ℝ) := Classical.choose_spec (hex n x)
  let a : ℕ → ℝ := fun n => Nat.rec 1 (fun n x => step n x) n
  have ha0 : a 0 = 1 := rfl
  have hainc (n : ℕ) : a n + 1 ≤ a (n+1) := (hstep n (a n)).1
  have haN (n : ℕ) : (n : ℝ) + 1 ≤ a n := by
    induction n with
    | zero => simp [ha0]
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one]
      linarith [hainc n]
  have ha1 (n : ℕ) : 1 ≤ a n := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith [haN n]
  refine ⟨a, ha1,
    monotone_nat_of_le_succ (fun n => by linarith [hainc n]), ?_,
    fun n => (hstep n (a n)).2.1, fun n => (hstep n (a n)).2.2⟩
  exact tendsto_atTop_mono haN (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)


/-- Beginning of the nth rise; its relative width is 1/(n+2). -/
def rampStart (a : ℕ → ℝ) (n : ℕ) : ℝ := a n - a n / ((n : ℝ)+2)

lemma rampStart_bounds {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n) (n : ℕ) :
    a n / 2 ≤ rampStart a n ∧ rampStart a n < a n := by
  have ha0 : 0 < a n := zero_lt_one.trans_le (ha n)
  have hn : (2 : ℝ) ≤ (n : ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hdiv : a n / ((n : ℝ)+2) ≤ a n / 2 :=
    div_le_div_of_nonneg_left ha0.le (by norm_num) hn
  have hpos : 0 < a n / ((n : ℝ)+2) := div_pos ha0 (by positivity)
  constructor <;> dsimp [rampStart] <;> linarith

/-- The supremum of the ramps. Boundedness follows from `ramp_term_bound`;
locally this equals a finite maximum, as proved in `rampEnvelope_continuous`. -/
def rampEnvelope (r : ℝ) (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ⨆ n, scalarRamp (a n) (rampStart a n) ((a n)^r) t

lemma ramp_term_bound {r : ℝ} (hr : 0 < r) {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (n : ℕ) (t : ℝ) :
    scalarRamp (a n) (rampStart a n) ((a n)^r) t ≤ (2*|t|)^r := by
  have hb := rampStart_bounds ha n
  by_cases ht : t ≤ rampStart a n
  · rw [scalarRamp_zero hb.2 ht]
    positivity
  · apply (scalarRamp_le (Real.rpow_nonneg (zero_le_one.trans (ha n)) r)).trans
    apply Real.rpow_le_rpow (zero_le_one.trans (ha n)) _ hr.le
    have : a n / 2 < t := hb.1.trans_lt (lt_of_not_ge ht)
    nlinarith [le_abs_self t]

lemma ramp_terms_bdd {r : ℝ} (hr : 0 < r) {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (t : ℝ) : BddAbove (range (fun n =>
      scalarRamp (a n) (rampStart a n) ((a n)^r) t)) :=
  ⟨(2*|t|)^r, by rintro _ ⟨n, rfl⟩; exact ramp_term_bound hr ha n t⟩

lemma rampEnvelope_nonneg {r : ℝ} (hr : 0 < r) {a : ℕ → ℝ}
    (ha : ∀ n, 1 ≤ a n) (t : ℝ) : 0 ≤ rampEnvelope r a t :=
  (scalarRamp_nonneg (Real.rpow_nonneg (zero_le_one.trans (ha 0)) r)).trans
    (le_ciSup (ramp_terms_bdd hr ha t) 0)

lemma rampEnvelope_monotone {r : ℝ} (hr : 0 < r) {a : ℕ → ℝ}
    (ha : ∀ n, 1 ≤ a n) : Monotone (rampEnvelope r a) := by
  intro x y hxy
  exact ciSup_mono (ramp_terms_bdd hr ha y) (fun n => scalarRamp_monotone
    (rampStart_bounds ha n).2 (Real.rpow_nonneg (zero_le_one.trans (ha n)) r) hxy)

lemma rampEnvelope_zero {r : ℝ} (hr : 0 < r) {a : ℕ → ℝ}
    (ha : ∀ n, 1 ≤ a n) {t : ℝ} (ht : t ≤ 0) : rampEnvelope r a t = 0 := by
  apply le_antisymm _ (rampEnvelope_nonneg hr ha t)
  unfold rampEnvelope
  apply ciSup_le
  intro n
  rw [scalarRamp_zero (rampStart_bounds ha n).2]
  exact ht.trans ((div_nonneg (zero_le_one.trans (ha n)) (by norm_num)).trans (rampStart_bounds ha n).1)

lemma rampEnvelope_continuous {r : ℝ} (hr : 0 < r) {a : ℕ → ℝ}
    (ha : ∀ n, 1 ≤ a n) (hat : Tendsto a atTop atTop) : Continuous (rampEnvelope r a) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp hat) (2*(x+1))
  let s := Finset.range (N+1)
  have hs : s.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  have heq {t : ℝ} (ht : t < x+1) :
      rampEnvelope r a t = s.sup' hs (fun n => scalarRamp (a n) (rampStart a n) ((a n)^r) t) := by
    unfold rampEnvelope
    apply le_antisymm
    · apply ciSup_le
      intro n
      by_cases hn : n ∈ s
      · exact Finset.le_sup' (fun n => scalarRamp (a n) (rampStart a n) ((a n)^r) t) hn
      · have hnN : N ≤ n := by
          have : ¬ n < N+1 := by simpa only [s, Finset.mem_range] using hn
          omega
        have hbt : t ≤ rampStart a n := by
          have := hN n hnN
          have := (rampStart_bounds ha n).1
          linarith
        rw [scalarRamp_zero (rampStart_bounds ha n).2 hbt]
        exact (scalarRamp_nonneg (a := a 0) (b := rampStart a 0) (t := t)
          (Real.rpow_nonneg (zero_le_one.trans (ha 0)) r)).trans
          (Finset.le_sup' (fun n => scalarRamp (a n) (rampStart a n) ((a n)^r) t) (show 0 ∈ s from Finset.mem_range.mpr (Nat.zero_lt_succ _)))
    · apply Finset.sup'_le
      intro n _
      exact le_ciSup (ramp_terms_bdd hr ha t) n
  have hc : Continuous (fun t => s.sup' hs
      (fun n => scalarRamp (a n) (rampStart a n) ((a n)^r) t)) :=
    Continuous.finset_sup'_apply hs (fun n _ => scalarRamp_continuous _ _ _)
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds (show x < x+1 by linarith)] with t ht
  exact heq ht


lemma rampStart_later {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n) (hm : Monotone a)
    (hsep : ∀ n, 2*a n ≤ a (n+1)) {n i : ℕ} (hni : n < i) :
    a n ≤ rampStart a i := by
  have hmono := hm (Nat.succ_le_of_lt hni)
  have hstart := (rampStart_bounds ha i).1
  have hs := hsep n
  linarith

lemma rampEnvelope_sample {r : ℝ} (hr : 0 < r) {a : ℕ → ℝ}
    (ha : ∀ n, 1 ≤ a n) (hm : Monotone a)
    (hsep : ∀ n, 2*a n ≤ a (n+1)) (n : ℕ) :
    rampEnvelope r a (a n) = (a n)^r := by
  apply le_antisymm
  · unfold rampEnvelope
    apply ciSup_le
    intro i
    by_cases hi : i ≤ n
    · exact (scalarRamp_le (Real.rpow_nonneg (zero_le_one.trans (ha i)) r)).trans
        (Real.rpow_le_rpow (zero_le_one.trans (ha i)) (hm hi) hr.le)
    · rw [scalarRamp_zero (rampStart_bounds ha i).2
        (rampStart_later ha hm hsep (lt_of_not_ge hi))]
      exact Real.rpow_nonneg (zero_le_one.trans (ha n)) r
  · simpa only [rampEnvelope, scalarRamp_top (rampStart_bounds ha n).2] using
      (le_ciSup (ramp_terms_bdd hr ha (a n)) n)

lemma rampEnvelope_plateau {r : ℝ} (hr : 0 < r) {a : ℕ → ℝ}
    (ha : ∀ n, 1 ≤ a n) (hm : Monotone a)
    (hsep : ∀ n, 2*a n ≤ a (n+1)) (n : ℕ) :
    rampEnvelope r a (rampStart a (n+1)) ≤ (a n)^r := by
  unfold rampEnvelope
  apply ciSup_le
  intro i
  by_cases hi : i ≤ n
  · exact (scalarRamp_le (Real.rpow_nonneg (zero_le_one.trans (ha i)) r)).trans
      (Real.rpow_le_rpow (zero_le_one.trans (ha i)) (hm hi) hr.le)
  · have hstart : rampStart a (n+1) ≤ rampStart a i := by
      rcases (Nat.eq_or_lt_of_le (show n+1 ≤ i by omega)) with he | he
      · rw [← he]
      · exact (rampStart_bounds ha (n+1)).2.le.trans (rampStart_later ha hm hsep he)
    rw [scalarRamp_zero (rampStart_bounds ha i).2 hstart]
    exact Real.rpow_nonneg (zero_le_one.trans (ha n)) r

lemma rampEnvelope_upperGrowth {p : ℝ≥0∞} (hpR : 1 < p.toReal) {a : ℕ → ℝ}
    (ha : ∀ n, 1 ≤ a n) : UpperGrowth p (rampEnvelope (p.toReal-1) a) := by
  have hr : 0 < p.toReal-1 := sub_pos.mpr hpR
  refine ⟨(2:ℝ)^(p.toReal-1), by positivity, fun t => ?_⟩
  rw [abs_of_nonneg (rampEnvelope_nonneg hr ha t)]
  calc
    rampEnvelope (p.toReal-1) a t ≤ (2*|t|)^(p.toReal-1) :=
      ciSup_le (fun n => ramp_term_bound hr ha n t)
    _ = (2:ℝ)^(p.toReal-1) * |t|^(p.toReal-1) := Real.mul_rpow (by norm_num) (abs_nonneg t)
    _ ≤ (2:ℝ)^(p.toReal-1) * (1+|t|^(p.toReal-1)) := by
      have : 0 ≤ (2:ℝ)^(p.toReal-1) := by positivity
      nlinarith

/-- Split at the beginning of the new rise: the first area is bounded by
the previous height times the endpoint, and the second by width times new height. -/
lemma rampEnvelope_primitive_bound {r : ℝ} (hr : 0 < r) {a : ℕ → ℝ}
    (ha : ∀ n, 1 ≤ a n) (hm : Monotone a) (hat : Tendsto a atTop atTop)
    (hsep : ∀ n, 2*a n ≤ a (n+1)) (n : ℕ) :
    0 ≤ primitive (rampEnvelope r a) (a (n+1)) ∧
    primitive (rampEnvelope r a) (a (n+1)) ≤
      a (n+1)*(a n)^r + (a (n+1)/((n:ℝ)+3))*(a (n+1))^r := by
  let g := rampEnvelope r a
  let A := a (n+1)
  let b := rampStart a (n+1)
  have hA : 0 < A := zero_lt_one.trans_le (ha (n+1))
  have hb : 0 ≤ b := (div_nonneg hA.le (by norm_num)).trans (rampStart_bounds ha (n+1)).1
  have hba : b ≤ A := (rampStart_bounds ha (n+1)).2.le
  have hc : Continuous g := rampEnvelope_continuous hr ha hat
  have hmono : Monotone g := rampEnvelope_monotone hr ha
  have h1 : (∫ t in (0:ℝ)..b, g t) ≤ b*(a n)^r := by
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using
      intervalIntegral.integral_mono_on (μ := volume) hb (hc.intervalIntegrable _ _)
        (intervalIntegrable_const) (fun t ht =>
          (hmono ht.2).trans (rampEnvelope_plateau hr ha hm hsep n))
  have h2 : (∫ t in b..A, g t) ≤ (A-b)*A^r := by
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using
      intervalIntegral.integral_mono_on (μ := volume) hba (hc.intervalIntegrable _ _)
        (intervalIntegrable_const) (fun t ht =>
          (hmono ht.2).trans_eq (rampEnvelope_sample hr ha hm hsep (n+1)))
  constructor
  · exact intervalIntegral.integral_nonneg_of_forall hA.le (rampEnvelope_nonneg hr ha)
  · have heq : primitive g A = (∫ t in (0:ℝ)..b, g t) + (∫ t in b..A, g t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
    change primitive g A ≤ _
    rw [heq]
    have hfirst : b*(a n)^r ≤ A*(a n)^r :=
      mul_le_mul_of_nonneg_right hba (Real.rpow_nonneg (zero_le_one.trans (ha n)) r)
    have hwidth : A-b = A/((n:ℝ)+3) := by
      dsimp [A, b, rampStart]
      push_cast
      ring
    rw [hwidth] at h2
    exact (add_le_add h1 h2).trans (add_le_add hfirst le_rfl)


lemma rampEnvelope_normalized_bound {r : ℝ} (hr : 0 < r) {a : ℕ → ℝ}
    (ha : ∀ n, 1 ≤ a n) (hm : Monotone a) (hat : Tendsto a atTop atTop)
    (hsep : ∀ n, 2*a n ≤ a (n+1))
    (hratio : ∀ n : ℕ, ((n:ℝ)+2)*(a n)^r ≤ (a (n+1))^r) (n : ℕ) :
    0 ≤ (a (n+1))^(-(r+1)) * primitive (rampEnvelope r a) (a (n+1)) ∧
    (a (n+1))^(-(r+1)) * primitive (rampEnvelope r a) (a (n+1)) ≤
      1/((n:ℝ)+2) + 1/((n:ℝ)+3) := by
  let A := a (n+1)
  have hA : 0 < A := zero_lt_one.trans_le (ha (n+1))
  have hAr : 0 < A^r := Real.rpow_pos_of_pos hA r
  have hpow : A^(-(r+1))*A*A^r = 1 := by
    calc
      _ = A^(-(r+1))*A^(1:ℝ)*A^r := by rw [Real.rpow_one]
      _ = A^(-(r+1)+1+r) := by rw [← Real.rpow_add hA, ← Real.rpow_add hA]
      _ = 1 := by ring_nf; rw [Real.rpow_zero]
  have hnorm : A^(-(r+1))*A = 1/A^r := (eq_div_iff hAr.ne').mpr hpow
  have hbound := rampEnvelope_primitive_bound hr ha hm hat hsep n
  constructor
  · exact mul_nonneg (Real.rpow_pos_of_pos hA _).le hbound.1
  · calc
      A^(-(r+1)) * primitive (rampEnvelope r a) A ≤
          A^(-(r+1)) * (A*(a n)^r+(A/((n:ℝ)+3))*A^r) :=
        mul_le_mul_of_nonneg_left hbound.2 (Real.rpow_pos_of_pos hA _).le
      _ = (A^(-(r+1))*A)*(a n)^r + (A^(-(r+1))*A*A^r)/((n:ℝ)+3) := by ring
      _ = (a n)^r/A^r + 1/((n:ℝ)+3) := by rw [hpow, hnorm]; ring
      _ ≤ 1/((n:ℝ)+2) + 1/((n:ℝ)+3) := by
        suffices hh : (a n)^r/A^r ≤ 1/((n:ℝ)+2) by linarith
        apply (div_le_div_iff₀ hAr (by positivity : (0:ℝ) < (n:ℝ)+2)).mpr
        simpa only [A, one_mul, mul_one, mul_comm] using hratio n

lemma rampEnvelope_energy_tendsto {r : ℝ} (hr : 0 < r) {a : ℕ → ℝ}
    (ha : ∀ n, 1 ≤ a n) (hm : Monotone a) (hat : Tendsto a atTop atTop)
    (hsep : ∀ n, 2*a n ≤ a (n+1))
    (hratio : ∀ n : ℕ, ((n:ℝ)+2)*(a n)^r ≤ (a (n+1))^r) :
    Tendsto (fun n => (a n)^(-(r+1))*primitive (rampEnvelope r a) (a n))
      atTop (𝓝 0) := by
  have ht (k : ℝ) : Tendsto (fun n : ℕ => 1/((n:ℝ)+k)) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop k tendsto_natCast_atTop_atTop).const_div_atTop 1
  have hlim : Tendsto (fun n : ℕ => 1/((n:ℝ)+2)+1/((n:ℝ)+3)) atTop (𝓝 0) := by
    simpa only [add_zero] using (ht 2).add (ht 3)
  have hs : Tendsto
      (fun n => (a (n+1))^(-(r+1))*primitive (rampEnvelope r a) (a (n+1)))
      atTop (𝓝 0) :=
    squeeze_zero (fun n => (rampEnvelope_normalized_bound hr ha hm hat hsep hratio n).1)
      (fun n => (rampEnvelope_normalized_bound hr ha hm hat hsep hratio n).2) hlim
  exact (tendsto_add_atTop_iff_nat 1).mp hs

/-- Fast separated scales and the finite-maximum envelope realize the required
scalar data for every positive growth exponent. -/
lemma ramp_construction : Spec.RampConstruction := by
  intro p hp hpt
  have hpR := ExpandedFA.PartIV.ConvexEnergySubendpoint.toReal_gt_one hp hpt
  have hr : 0 < p.toReal-1 := sub_pos.mpr hpR
  obtain ⟨a, ha, hm, hat, hsep, hratio⟩ := exists_ramp_scale hr
  refine ⟨rampEnvelope (p.toReal-1) a, a, rampEnvelope_continuous hr ha hat,
    rampEnvelope_monotone hr ha, rampEnvelope_upperGrowth hpR ha,
    rampEnvelope_zero hr ha le_rfl, ha, hat,
    fun n => (rampEnvelope_sample hr ha hm hsep n).ge, ?_⟩
  simpa only [sub_add_cancel] using rampEnvelope_energy_tendsto hr ha hm hat hsep hratio

/-- Both endpoint conclusions fail without the lower growth assumption. -/
theorem counterexample : Spec.Counterexample := by
  exact counterexample_of_ramps ramp_construction

end ExpandedFA.PartIV.ConvexEnergyCounterexample
