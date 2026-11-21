import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.LaplaceEndpoints
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace ExpandedFA.PartIV.LaplaceEndpoints
open LaplaceL2Spec LaplaceEndpointsSpec

lemma halfLine_Ioc {a b : ℝ} (ha : 0 ≤ a) :
    halfLine (Ioc a b) = ENNReal.ofReal (b-a) := by
  rw [Measure.restrict_apply measurableSet_Ioc,
    (show Ioc a b ∩ Ioi 0 = Ioc a b from inter_eq_left.mpr (fun _ hx => lt_of_le_of_lt ha hx.1))]
  exact Real.volume_Ioc

lemma intervalVector_norm (𝕜 : Type) [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ‖intervalVector 𝕜 p a b‖ = (b-a) ^ (1 / p.toReal) := by
  rw [intervalVector, norm_indicatorConstLp' (ne_of_gt (lt_of_lt_of_le zero_lt_one
    (Fact.out : 1 ≤ p))) (by rw [halfLine_Ioc ha]; exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab))]
  simp [Measure.real, halfLine_Ioc ha, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]

lemma laplace_interval_real {𝕜 : Type} [RCLike 𝕜] {a b : ℝ} (ha : 0 ≤ a) (s : ℝ) :
    laplaceIntegral (intervalTest 𝕜 a b) s =
      RCLike.ofReal (∫ t in Ioc a b, Real.exp (-(s*t))) := by
  unfold laplaceIntegral intervalTest laplaceKernel
  have heq : (fun t => (RCLike.ofReal (Real.exp (-(s*t))) : 𝕜) *
      (Ioc a b).indicator (fun _ => 1) t) =
      (Ioc a b).indicator (fun t => (RCLike.ofReal (Real.exp (-(s*t))) : 𝕜)) := by
    funext t
    by_cases ht : t ∈ Ioc a b <;> simp [ht]
  rw [heq]
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    (show Ioc a b ∩ Ioi 0 = Ioc a b from inter_eq_left.mpr (fun _ hx => lt_of_le_of_lt ha hx.1)), integral_ofReal]

lemma carleman_interval_real {𝕜 : Type} [RCLike 𝕜] {a b : ℝ} (ha : 0 ≤ a) (s : ℝ) :
    carlemanIntegral (intervalTest 𝕜 a b) s =
      RCLike.ofReal (∫ t in Ioc a b, (s+t)⁻¹) := by
  unfold carlemanIntegral intervalTest
  have heq : (fun t => (Ioc a b).indicator (fun _ => (1 : 𝕜)) t /
      RCLike.ofReal (s+t)) =
      (Ioc a b).indicator (fun t => (RCLike.ofReal ((s+t)⁻¹) : 𝕜)) := by
    funext t
    by_cases ht : t ∈ Ioc a b <;> simp [ht]
  rw [heq]
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    (show Ioc a b ∩ Ioi 0 = Ioc a b from inter_eq_left.mpr (fun _ hx => lt_of_le_of_lt ha hx.1)), integral_ofReal]

lemma inv_interval_integrable {s a b : ℝ} (hs : 0 < s) (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => (s+t)⁻¹) (Ioc a b) := by
  refine IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
  apply ContinuousOn.integrableOn_Icc
  exact (continuousOn_const.add continuousOn_id).inv₀ fun t ht => by
    have := ht.1
    change s + t ≠ 0
    linarith

theorem laplace_dilation : LaplaceDilation := by
  intro 𝕜 _ f a ha s
  unfold laplaceIntegral laplaceKernel
  have h : (fun t => (RCLike.ofReal (Real.exp (-(s*t))) : 𝕜) * f (a*t)) =
      (fun t => (RCLike.ofReal (Real.exp (-((s/a)*(a*t)))) : 𝕜) * f (a*t)) := by
    funext t
    congr 3
    field_simp
  rw [h]
  simpa only [mul_zero] using
    integral_comp_mul_left_Ioi (fun t => (RCLike.ofReal (Real.exp (-((s/a)*t))) : 𝕜) * f t) 0 ha

lemma interval_integral_lower {a b C : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioc a b)) (hab : a ≤ b)
    (h : ∀ t ∈ Ioc a b, C ≤ f t) :
    C * (b-a) ≤ ∫ t in Ioc a b, f t := by
  have hi := setIntegral_mono_on (integrableOn_const (μ := volume) measure_Ioc_lt_top.ne)
    hf measurableSet_Ioc h
  simpa [integral_const, Measure.real, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab), mul_comm] using hi

lemma laplace_interval_lower (𝕜 : Type) [RCLike 𝕜] {a s : ℝ}
    (ha : 0 < a) (hs : s ∈ Ioc 0 a⁻¹) :
    a * Real.exp (-2) ≤ ‖laplaceIntegral (intervalTest 𝕜 a (2*a)) s‖ := by
  rw [laplace_interval_real ha.le, RCLike.norm_ofReal]
  apply le_trans _ (le_abs_self _)
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(s*t))) (Ioc a (2*a)) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(s*t)))).integrableOn_Ioc
  have hsa : s*a ≤ 1 := by
    have := hs.2
    rwa [← one_div, le_div_iff₀ ha] at this
  have h := interval_integral_lower hi (by linarith) (C := Real.exp (-2)) (by
    intro t ht
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hs.1.le (sub_nonneg.mpr ht.2)])
  convert h using 1; ring

/-- Dilation of the unit interval test to (a,2a). On (0,1/a) its
Laplace image is at least a exp(-2). The indicator norm formula includes p=∞. -/
lemma laplace_operator_scale_bound (𝕜 : Type) [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (T : PositiveLp 𝕜 p →L[𝕜] PositiveLp 𝕜 p)
    (hT : IntervalCompatible laplaceIntegral T) {a : ℝ} (ha : 0 < a) :
    (a * Real.exp (-2)) * (a⁻¹) ^ (1 / p.toReal) ≤
      ‖T‖ * a ^ (1 / p.toReal) := by
  let v := intervalVector 𝕜 p a (2*a)
  let w := intervalVector 𝕜 p 0 a⁻¹
  have hb : ‖(a * Real.exp (-2)) • w‖ ≤ ‖T v‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_smul (a * Real.exp (-2)) w,
      indicatorConstLp_coeFn (p := p) (hs := measurableSet_Ioc)
        (hμs := (measure_Ioc_lt_top (μ := halfLine) (a := 0) (b := a⁻¹)).ne) (c := (1 : 𝕜)),
      hT a (2*a) ha.le (by linarith)] with s hsm hw ht
    change (w : ℝ → 𝕜) s = _ at hw
    change (T v : ℝ → 𝕜) s = _ at ht
    rw [hsm, Pi.smul_apply, hw]
    by_cases hs : s ∈ Ioc 0 a⁻¹
    · rw [indicator_of_mem hs, norm_smul, norm_one, mul_one, Real.norm_eq_abs,
        abs_of_pos (mul_pos ha (Real.exp_pos _)), ht]
      exact laplace_interval_lower 𝕜 ha hs
    · simp [indicator_of_notMem hs, norm_nonneg]
  have hv : ‖v‖ = a ^ (1 / p.toReal) := by
    dsimp [v]
    simpa only [show 2*a-a = a by ring] using
      intervalVector_norm 𝕜 (p := p) ha.le (by linarith : a < 2*a)
  have hw : ‖w‖ = (a⁻¹) ^ (1 / p.toReal) := by
    simpa [w] using intervalVector_norm 𝕜 (p := p) (a := 0) (b := a⁻¹)
      (le_refl 0) (inv_pos.mpr ha)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos ha (Real.exp_pos _)), hw] at hb
  exact hb.trans ((T.le_opNorm v).trans_eq (by rw [hv]))

lemma scaling_exponent_ne_zero {p : ℝ≥0∞} (hp : 1 ≤ p) (hne : p ≠ 2) :
    1 - 2 * (1 / p.toReal) ≠ 0 := by
  by_cases htop : p = ∞
  · simp [htop]
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 htop
  intro h
  have heq : p.toReal = 2 := by
    field_simp at h
    linarith
  apply hne
  apply (ENNReal.toReal_eq_toReal_iff' htop (by norm_num)).mp
  simpa using heq

/-- The resulting norm ratio is at least exp(-2) a^(1-2/p).
Taking a=exp(x) makes either direction of dilation a single exponential
contradiction, including p=∞ where 1/p=0. -/
theorem laplace_unbounded : LaplaceUnbounded := by
  intro 𝕜 _ p hp hne
  let : Fact (1 ≤ p) := ⟨hp⟩
  rintro ⟨T, hT⟩
  let r := 1 / p.toReal
  let q := 1 - 2*r
  have hq : q ≠ 0 := scaling_exponent_ne_zero hp hne
  let x := (Real.log (‖T‖ + 1) + 2) / q
  have hx : q * x = Real.log (‖T‖ + 1) + 2 := by
    dsimp [x]
    field_simp
  have hb := laplace_operator_scale_bound 𝕜 T hT (Real.exp_pos x)
  rw [← Real.exp_neg, ← Real.exp_mul, ← Real.exp_mul] at hb
  change (Real.exp x * Real.exp (-2)) * Real.exp (-x*r) ≤
    ‖T‖ * Real.exp (x*r) at hb
  have hb' : Real.exp (q*x - 2) ≤ ‖T‖ := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos (x*r))).mp
    convert hb using 1
    · rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [q]
      ring
    · ring
  rw [hx, add_sub_cancel_right, Real.exp_log (by positivity : 0 < ‖T‖ + 1)] at hb'
  linarith

lemma carleman_interval_log {𝕜 : Type} [RCLike 𝕜] {a b s : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hs : 0 < s) :
    carlemanIntegral (intervalTest 𝕜 a b) s =
      RCLike.ofReal (Real.log ((s+b)/(s+a))) := by
  rw [carleman_interval_real ha, ← intervalIntegral.integral_of_le hab]
  have heq := intervalIntegral.integral_comp_add_left (fun t : ℝ => t⁻¹) s
    (a := a) (b := b)
  rw [heq, integral_inv_of_pos (by linarith) (by linarith)]

lemma carleman_tail_lower {s : ℝ} (hs : 2 ≤ s) :
    (2*s)⁻¹ ≤ carlemanIntegral (intervalTest ℝ 1 2) s := by
  rw [carleman_interval_real (by norm_num : (0:ℝ) ≤ 1)]
  change (2*s)⁻¹ ≤ ∫ t in Ioc (1:ℝ) 2, (s+t)⁻¹
  have hi := interval_integral_lower
    (inv_interval_integrable (s := s) (a := 1) (b := 2) (by linarith) (by norm_num))
    (by norm_num : (1:ℝ) ≤ 2) (C := (s+2)⁻¹) (by
      intro t ht
      exact (inv_le_inv₀ (by linarith) (by linarith [ht.1])).mpr (by linarith [ht.2]))
  norm_num at hi
  apply le_trans _ hi
  exact (inv_le_inv₀ (by linarith) (by linarith)).mpr (by linarith)

lemma carleman_interval_tail :
    (∀ s : ℝ, 2 ≤ s → (2*s)⁻¹ ≤ carlemanIntegral (intervalTest ℝ 1 2) s) ∧
      ¬ Integrable (carlemanIntegral (intervalTest ℝ 1 2)) halfLine := by
  refine ⟨fun _ hs => carleman_tail_lower hs, ?_⟩
  intro h
  have h' : IntegrableOn (carlemanIntegral (intervalTest ℝ 1 2)) (Ioi 2) :=
    (show IntegrableOn (carlemanIntegral (intervalTest ℝ 1 2)) (Ioi (0:ℝ))
      (volume : Measure ℝ) from h).mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 2))
  apply not_integrableOn_Ioi_inv (a := (2:ℝ))
  apply (h'.const_mul 2).mono' measurable_inv.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change 2 < s at hs
  rw [norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < s)]
  have hb := carleman_tail_lower hs.le
  have heq : (2*s)⁻¹ = s⁻¹ / 2 := by field_simp
  rw [heq] at hb
  linarith

lemma carleman_log_large (M : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioo 0 δ,
      M < carlemanIntegral (intervalTest ℝ 0 1) s := by
  refine ⟨Real.exp (-M), Real.exp_pos _, ?_⟩
  intro s hs
  have hs0 : 0 < s := hs.1
  rw [carleman_interval_log (by norm_num : (0:ℝ) ≤ 0) zero_le_one hs.1]
  change M < Real.log ((s+1)/(s+0))
  simp only [add_zero]
  apply (Real.exp_lt_exp).mp
  rw [Real.exp_log (by positivity : 0 < (s+1)/s)]
  have hb : Real.exp M * s < 1 := by
    have ht := mul_lt_mul_of_pos_left hs.2 (Real.exp_pos M)
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at ht
    exact ht
  apply (lt_div_iff₀ hs.1).mpr
  linarith

/-- The integral formula depends only on the a.e. input class. -/
lemma carlemanIntegral_congr {𝕜 : Type} [RCLike 𝕜] {f g : ℝ → 𝕜}
    (h : f =ᵐ[halfLine] g) : carlemanIntegral f = carlemanIntegral g := by
  funext s
  apply integral_congr_ae
  filter_upwards [h] with t ht
  rw [ht]

lemma carleman_closed_interval (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) :
    carlemanIntegral ((Icc a b).indicator (fun _ => (1 : 𝕜))) =
      carlemanIntegral (intervalTest 𝕜 a b) := by
  exact carlemanIntegral_congr (indicator_ae_eq_of_ae_eq_set
    (Ioc_ae_eq_Icc (μ := halfLine)).symm)

lemma carleman_open_interval (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) :
    carlemanIntegral ((Ioo a b).indicator (fun _ => (1 : 𝕜))) =
      carlemanIntegral (intervalTest 𝕜 a b) := by
  exact carlemanIntegral_congr (indicator_ae_eq_of_ae_eq_set
    (Ioo_ae_eq_Ioc (μ := halfLine)))

theorem carleman_tail : CarlemanTail := by
  unfold CarlemanTail
  rw [carleman_closed_interval]
  exact carleman_interval_tail

theorem carleman_log : CarlemanLog := by
  unfold CarlemanLog
  rw [carleman_open_interval]
  exact ⟨fun s hs => by simpa using
    (carleman_interval_log (𝕜 := ℝ) (a := 0) (b := 1) (by norm_num) zero_le_one hs),
    carleman_log_large⟩

lemma carleman_real_part (𝕜 : Type) [RCLike 𝕜] {a b : ℝ}
    (ha : 0 ≤ a) (s : ℝ) :
    RCLike.re (carlemanIntegral (intervalTest 𝕜 a b) s) =
      carlemanIntegral (intervalTest ℝ a b) s := by
  rw [carleman_interval_real ha, carleman_interval_real ha]
  simp

lemma carleman_real_le_norm (𝕜 : Type) [RCLike 𝕜] {a b : ℝ}
    (ha : 0 ≤ a) (s : ℝ) :
    carlemanIntegral (intervalTest ℝ a b) s ≤
      ‖carlemanIntegral (intervalTest 𝕜 a b) s‖ := by
  rw [carleman_interval_real ha, carleman_interval_real ha, RCLike.norm_ofReal]
  exact le_abs_self _

lemma no_carleman_L1 (𝕜 : Type) [RCLike 𝕜] :
    ¬ ∃ T : PositiveLp 𝕜 1 →L[𝕜] PositiveLp 𝕜 1,
      IntervalCompatible carlemanIntegral T := by
  rintro ⟨T, hT⟩
  let v := intervalVector 𝕜 1 1 2
  have hi : Integrable (fun s => RCLike.re ((T v : ℝ → 𝕜) s)) halfLine :=
    ((memLp_one_iff_integrable).mp (Lp.memLp (T v))).re
  apply carleman_interval_tail.2
  apply hi.congr
  filter_upwards [hT 1 2 (by norm_num) (by norm_num)] with s hs
  change (T v : ℝ → 𝕜) s = _ at hs
  rw [hs]
  exact carleman_real_part 𝕜 (by norm_num) s

lemma no_carleman_Linfty (𝕜 : Type) [RCLike 𝕜] :
    ¬ ∃ T : PositiveLp 𝕜 ∞ →L[𝕜] PositiveLp 𝕜 ∞,
      IntervalCompatible carlemanIntegral T := by
  rintro ⟨T, hT⟩
  let v := intervalVector 𝕜 ∞ 0 1
  let C := ‖T v‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨δ, hδ, hlarge⟩ := carleman_log_large C
  let w := intervalVector 𝕜 ∞ 0 (δ/2)
  have hw : ‖w‖ = 1 := by
    simpa [w] using intervalVector_norm 𝕜 (p := ∞) (a := 0) (b := δ/2)
      (le_refl 0) (by linarith : 0 < δ/2)
  have hb : ‖C • w‖ ≤ ‖T v‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_smul C w,
      indicatorConstLp_coeFn (p := ∞) (hs := measurableSet_Ioc)
        (hμs := (measure_Ioc_lt_top (μ := halfLine) (a := 0) (b := δ/2)).ne) (c := (1 : 𝕜)),
      hT 0 1 (le_refl 0) zero_lt_one] with s hsm hw ht
    change (w : ℝ → 𝕜) s = _ at hw
    change (T v : ℝ → 𝕜) s = _ at ht
    rw [hsm, Pi.smul_apply, hw]
    by_cases hs : s ∈ Ioc 0 (δ/2)
    · rw [indicator_of_mem hs, norm_smul, norm_one, mul_one, Real.norm_eq_abs,
        abs_of_pos hC, ht]
      exact ((hlarge s ⟨hs.1, by linarith [hs.2]⟩).le).trans
        (carleman_real_le_norm 𝕜 (le_refl 0) s)
    · simp [indicator_of_notMem hs, norm_nonneg]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hC, hw, mul_one] at hb
  dsimp [C] at hb
  linarith

theorem carleman_endpoints : CarlemanEndpoints := by
  intro 𝕜 _
  exact ⟨no_carleman_L1 𝕜, no_carleman_Linfty 𝕜⟩

end ExpandedFA.PartIV.LaplaceEndpoints
