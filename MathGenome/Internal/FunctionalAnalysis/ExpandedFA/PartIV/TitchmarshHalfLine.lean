import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.TitchmarshHalfLine
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardySupportBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ExpandedFA.PartIV.TitchmarshHalfLine
open HardyHalfPlaneRepresentationSpec HardyHalfPlaneRepresentation
open HardySupportBridge HardyExponentialFactor

lemma extend_integrable {f : ℝ → ℂ} (hf : Integrable f positiveMeasure) :
    Integrable (extend f) := (integrable_indicator_iff measurableSet_Ioi).mpr hf

lemma extend_supported (f : ℝ → ℂ) : SupportedAbove (extend f) 0 := by
  apply Eventually.of_forall
  intro t ht
  exact indicator_of_notMem (show t ∉ Ioi (0 : ℝ) by simpa using ht.le) _

lemma extend_ae {f g : ℝ → ℂ} (h : f =ᵐ[positiveMeasure] g) :
    extend f =ᵐ[volume] extend g := by
  have h' := (ae_restrict_iff' measurableSet_Ioi).mp h
  filter_upwards [h'] with t ht
  by_cases hp : 0 < t
  · simp [extend, hp, ht hp]
  · simp [extend, hp]

lemma extend_zero_iff (f : ℝ → ℂ) :
    extend f =ᵐ[volume] 0 ↔ f =ᵐ[positiveMeasure] 0 := by
  constructor
  · intro h
    change ∀ᵐ t ∂volume.restrict (Ioi 0), f t = 0
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [h] with t ht hp
    simpa [extend, hp] using ht
  · intro h
    simpa [extend] using extend_ae h

/-- Zero extension realizes exactly the ordinary causal half-line integral. -/
lemma halfConvolution_eq_integral (f g : ℝ → ℂ) (x : ℝ) :
    halfConvolution f g x = ∫ t in Ioo 0 x, f t * g (x - t) := by
  rw [← integral_indicator measurableSet_Ioo]
  change (∫ t, extend f t * extend g (x - t)) = _
  congr 1
  funext t
  by_cases ht0 : 0 < t <;> by_cases htx : t < x <;>
    simp [extend, ht0, sub_pos, htx]

lemma vanishesInitially_iff (f : ℝ → ℂ) {c : ℝ} (_hc : 0 ≤ c) :
    VanishesInitially f c ↔ SupportedAbove (extend f) c := by
  change (∀ᵐ t ∂volume.restrict (Ioo 0 c), f t = 0) ↔ _
  rw [ae_restrict_iff' measurableSet_Ioo]
  constructor
  · intro h
    filter_upwards [h] with t ht htc
    by_cases hp : 0 < t
    · simpa [extend, hp] using ht ⟨hp, htc⟩
    · simp [extend, hp]
  · intro h
    filter_upwards [h] with t ht htc
    simpa [extend, htc.1] using ht htc.2

lemma laplace_extend (f : ℝ → ℂ) (z : ℂ) : laplace (extend f) z = laplace f z := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp [extend, ht]

lemma weighted_integrable_L1 {f : ℝ → ℂ} (hf : Integrable f positiveMeasure)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    Integrable (fun t => kernel z t * f t) positiveMeasure := by
  apply hf.norm.mono' ((by unfold kernel; fun_prop : Continuous (kernel z)).aestronglyMeasurable.mul
    hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖kernel z t * f t‖ ≤ ‖f t‖
  rw [norm_mul, norm_kernel]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by
    have hz' : 0 < z.im := hz
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos hz', mul_pos (mul_pos Real.pi_pos hz') ht]))

lemma norm_laplace_le {f : ℝ → ℂ} (hf : Integrable f positiveMeasure)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    ‖laplace f z‖ ≤ ∫ t, ‖f t‖ ∂positiveMeasure := by
  refine (norm_integral_le_integral_norm _).trans (integral_mono_ae
    (weighted_integrable_L1 hf hz).norm hf.norm ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, norm_kernel]
  apply mul_le_of_le_one_left (norm_nonneg _)
  apply Real.exp_le_one_iff.mpr
  have hz' : 0 < z.im := hz
  nlinarith [Real.pi_pos, mul_pos Real.pi_pos hz', mul_pos (mul_pos Real.pi_pos hz') ht]

/-- The easy implication retains the zero function and the boundary cut `c=0`. -/
lemma boundedShift_of_vanishes {f : ℝ → ℂ} (hf : Integrable f positiveMeasure)
    {c : ℝ} (hc : 0 ≤ c) (hv : VanishesInitially f c) : BoundedShift f c := by
  have hs := (vanishesInitially_iff f hc).mp hv
  have hi : Integrable (translate (extend f) c) := (extend_integrable hf).comp_add_right c
  refine ⟨∫ t, ‖translate (extend f) c t‖ ∂positiveMeasure, ?_⟩
  intro z hz
  have he := laplace_congr (ae_restrict_of_ae (causalDelay_translate hs)) z
  rw [laplace_causalDelay _ hc z, laplace_extend] at he
  rw [← he, ← mul_assoc, exponentialInner_cancel, one_mul]
  exact norm_laplace_le hi.restrict hz

/-- A bounded holomorphic multiplier preserves the actual half-plane H² norm. -/
lemma isH2_bounded_mul {B H : ℂ → ℂ}
    (hB : DifferentiableOn ℂ B upperHalfPlane) (hH : IsH2 H)
    (hbound : ∃ M : ℝ, ∀ z ∈ upperHalfPlane, ‖B z‖ ≤ M) :
    IsH2 (fun z => B z * H z) := by
  obtain ⟨M, hM⟩ := hbound
  obtain ⟨hhol, C, hC, hnorm⟩ := hH
  have hM0 : 0 ≤ M := (norm_nonneg (B Complex.I)).trans (hM Complex.I (by
    simp [upperHalfPlane]))
  refine ⟨hB.mul hhol, M ^ 2 * C, by positivity, ?_⟩
  intro y hy
  obtain ⟨hy2, hiy⟩ := hnorm y hy
  have hb (x : ℝ) : ‖slice B y x‖ ≤ M := hM _ (by
    simpa [upperHalfPlane] using hy)
  have hm : AEStronglyMeasurable (slice B y) volume :=
    (show Continuous (slice B y) from by
      rw [← continuousOn_univ]
      exact hB.continuousOn.comp
        (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) univ)
        (by intro x _; simpa [upperHalfPlane] using hy)).aestronglyMeasurable
  have hm' : AEStronglyMeasurable (slice (fun z => B z * H z) y) volume :=
    hm.mul hy2.aestronglyMeasurable
  have hle : ∀ x, ‖slice (fun z => B z * H z) y x‖ ≤ M * ‖slice H y x‖ := by
    intro x
    exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))
  have hmem : MemLp (slice (fun z => B z * H z) y) 2 volume :=
    (hy2.const_mul (M : ℂ)).mono hm' (Eventually.of_forall (fun x => by
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0] using hle x))
  refine ⟨hmem, ?_⟩
  calc
    (∫ x, ‖slice (fun z => B z * H z) y x‖ ^ 2) ≤
        ∫ x, M ^ 2 * ‖slice H y x‖ ^ 2 := by
      apply integral_mono_ae
        ((memLp_two_iff_integrable_sq_norm hm').mp hmem)
        (((memLp_two_iff_integrable_sq_norm hy2.aestronglyMeasurable).mp hy2).const_mul _)
      exact Eventually.of_forall (fun x => by
        have := hle x
        have hn := norm_nonneg (slice (fun z => B z * H z) y x)
        have hp : 0 ≤ M * ‖slice H y x‖ := mul_nonneg hM0 (norm_nonneg _)
        nlinarith)
    _ = M ^ 2 * ∫ x, ‖slice H y x‖ ^ 2 := integral_const_mul _ _
    _ ≤ M ^ 2 * C := mul_le_mul_of_nonneg_left hiy (sq_nonneg _)

/-- The causal resolvent kernel, with endpoint zero. -/
def resolventKernel (t : ℝ) : ℂ :=
  (Ioi 0).indicator (fun s : ℝ => Complex.exp (-(s : ℂ))) t

def regularize (f : ℝ → ℂ) : ℝ → ℂ := convolution f resolventKernel

lemma resolventKernel_integrable : Integrable resolventKernel := by
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  simpa only [neg_mul, one_mul] using
    integrableOn_exp_mul_complex_Ioi (a := (-1 : ℂ)) (by norm_num) 0

lemma resolventKernel_supported : SupportedAbove resolventKernel 0 := by
  apply Eventually.of_forall
  intro t ht
  simp [resolventKernel, not_lt.mpr ht.le]

lemma norm_resolventKernel_le (t : ℝ) : ‖resolventKernel t‖ ≤ 1 := by
  by_cases ht : 0 < t
  · simp only [resolventKernel, mem_Ioi, ht, indicator_of_mem, Complex.norm_exp,
      Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr (by linarith)
  · simp [resolventKernel, ht]

lemma regularize_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (regularize f) := convolution_integrable hf resolventKernel_integrable

lemma regularize_integrand {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Integrable (fun t => f t * resolventKernel (x - t)) := by
  apply hf.mul_bdd
    (resolventKernel_integrable.aestronglyMeasurable.comp_measurePreserving
      (volume.measurePreserving_sub_left x))
  exact Eventually.of_forall fun t => norm_resolventKernel_le (x - t)

lemma norm_regularize_le {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    ‖regularize f x‖ ≤ ∫ t, ‖f t‖ := by
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono_ae (regularize_integrand hf x).norm hf.norm ?_)
  exact Eventually.of_forall fun t => by
    change ‖f t * resolventKernel (x - t)‖ ≤ ‖f t‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_resolventKernel_le _)

lemma regularize_memLp {f : ℝ → ℂ} (hf : Integrable f) :
    MemLp (regularize f) 2 volume := by
  have hi := regularize_integrable hf
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
  apply (hi.norm.mul_const (∫ t, ‖f t‖)).mono'
    (hi.aestronglyMeasurable.norm.pow 2)
  exact Eventually.of_forall fun x => by
    change ‖‖regularize f x‖ ^ 2‖ ≤ ‖regularize f x‖ * (∫ t, ‖f t‖)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := norm_regularize_le hf x
    nlinarith [mul_le_mul_of_nonneg_left h (norm_nonneg (regularize f x))]

lemma regularize_supported {f : ℝ → ℂ} {c : ℝ} (hc : SupportedAbove f c) :
    SupportedAbove (regularize f) c := by
  simpa [regularize] using convolution_supportedAbove hc resolventKernel_supported

lemma regularize_primitive {f : ℝ → ℂ} (hc : SupportedAbove f 0) {x : ℝ} (hx : 0 ≤ x) :
    regularize f x = Complex.exp (-(x : ℂ)) *
      ∫ t in (0 : ℝ)..x, Complex.exp (t : ℂ) * f t := by
  rw [intervalIntegral.integral_of_le hx, ← integral_const_mul]
  change (∫ t, f t * resolventKernel (x - t)) = _
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [hc, volume.ae_ne 0, volume.ae_ne x] with t ht hn0 hnx
  by_cases ht0 : 0 < t
  · by_cases htx : t < x
    · simp only [resolventKernel, Complex.ofReal_sub, neg_sub, mem_Ioi, sub_pos,
        htx, indicator_of_mem, mem_Ioc, ht0, le_of_lt htx, and_self]
      rw [show (t : ℂ) - (x : ℂ) = -(x : ℂ) + (t : ℂ) by ring, Complex.exp_add]
      ring
    · have hnot : ¬ t ≤ x := by exact lt_of_le_of_ne (not_lt.mp htx) (Ne.symm hnx) |>.not_ge
      simp [resolventKernel, not_lt.mpr (not_le.mp hnot).le, hnot]
  · have htz : t < 0 := lt_of_le_of_ne (not_lt.mp ht0) hn0
    simp [ht htz, not_lt.mpr htz.le]

lemma regularize_support_iff {f : ℝ → ℂ} (hf : Integrable f)
    (hc : SupportedAbove f 0) (c : ℝ) :
    SupportedAbove (regularize f) c ↔ SupportedAbove f c := by
  refine ⟨?_, fun h => regularize_supported h⟩
  intro hs
  by_cases hc0 : c ≤ 0
  · exact supportedAbove_mono hc hc0
  have hcpos : 0 < c := lt_of_not_ge hc0
  let w : ℝ → ℂ := fun t => Complex.exp (t : ℂ) * f t
  let P : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, w t
  have hw : LocallyIntegrable w volume :=
    (hf.locallyIntegrable).continuous_mul (by fun_prop)
  have hP : Continuous P := intervalIntegral.continuous_primitive
    (fun a b => (hw.integrableOn_isCompact isCompact_uIcc).intervalIntegrable) 0
  have hz : P =ᵐ[volume.restrict (Ioo 0 c)] 0 := by
    change ∀ᵐ t ∂volume.restrict (Ioo 0 c), P t = 0
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hs] with t ht htc
    have he := regularize_primitive hc htc.1.le
    rw [ht htc.2] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (Complex.exp_ne_zero _)
  have hPon : EqOn P (0 : ℝ → ℂ) (Ioo 0 c) :=
    Measure.eqOn_open_of_ae_eq hz isOpen_Ioo hP.continuousOn continuousOn_const
  filter_upwards [hc, _root_.LocallyIntegrable.ae_hasDerivAt_integral hw, volume.ae_ne 0] with t ht hd hn0 htc
  by_cases ht0 : 0 < t
  · have hpzero : P =ᶠ[𝓝 t] (0 : ℝ → ℂ) :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht0 htc) hPon
    have hzero : HasDerivAt P 0 t := (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq hpzero
    have he : w t = 0 := (hd 0).unique hzero
    exact (mul_eq_zero.mp he).resolve_left (Complex.exp_ne_zero _)
  · exact ht (lt_of_le_of_ne (not_lt.mp ht0) hn0)

lemma zero_of_supported_all {f : ℝ → ℂ} (hf : ∀ c : ℝ, SupportedAbove f c) :
    f =ᵐ[volume] 0 := by
  have h : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ, t < (n : ℝ) → f t = 0 :=
    ae_all_iff.mpr fun n => hf n
  filter_upwards [h] with t ht
  obtain ⟨n, hn⟩ := exists_nat_gt t
  exact ht n hn

lemma regularize_nonzero {f : ℝ → ℂ} (hf : Integrable f) (hc : SupportedAbove f 0)
    (hn : ¬ (f =ᵐ[volume] 0)) : ¬ (regularize f =ᵐ[volume] 0) := by
  intro hz
  apply hn
  apply zero_of_supported_all
  intro c
  apply (regularize_support_iff hf hc c).mp
  filter_upwards [hz] with t ht _ using ht

lemma regularize_endpoint_iff {f : ℝ → ℂ} (hf : Integrable f)
    (hc : SupportedAbove f 0) (a : ℝ) :
    IsLeftEndpoint (regularize f) a ↔ IsLeftEndpoint f a := by
  simp only [IsLeftEndpoint, regularize_support_iff hf hc]

lemma convolution_assoc_ae {f g h : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h) :
    convolution (convolution f g) h =ᵐ[volume] convolution f (convolution g h) := by
  let L := ContinuousLinearMap.mul ℂ ℂ
  let LR := ContinuousLinearMap.mul ℝ ℝ
  have hfg := hf.ae_convolution_exists L hg
  have hgh := hg.norm.ae_convolution_exists LR hh.norm
  have hfgh := hf.norm.ae_convolution_exists LR
    (hg.norm.integrable_convolution LR hh.norm)
  filter_upwards [hfgh] with x hx
  exact MeasureTheory.convolution_assoc L L L L (fun a b c => mul_assoc a b c)
    hf.aestronglyMeasurable hg.aestronglyMeasurable hh.aestronglyMeasurable hfg hgh hx

lemma convolution_comm (f g : ℝ → ℂ) : convolution f g = convolution g f := by
  exact MeasureTheory.convolution_symm (ContinuousLinearMap.mul ℂ ℂ) (by
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    exact mul_comm y x)

lemma regularize_zero : regularize (0 : ℝ → ℂ) = 0 := by
  funext x
  change (∫ t : ℝ, (0 : ℂ) * resolventKernel (x - t)) = 0
  simp

lemma regularize_congr {f g : ℝ → ℂ} (he : f =ᵐ[volume] g) :
    regularize f = regularize g :=
  MeasureTheory.convolution_congr (ContinuousLinearMap.mul ℂ ℂ) he (g := resolventKernel) EventuallyEq.rfl

lemma regularize_convolution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    convolution (regularize f) g =ᵐ[volume] regularize (convolution f g) := by
  have h1 := convolution_assoc_ae hf resolventKernel_integrable hg
  rw [convolution_comm resolventKernel g] at h1
  exact h1.trans (convolution_assoc_ae hf hg resolventKernel_integrable).symm

lemma regularize_convolution_twice {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    convolution (regularize f) (regularize g) =ᵐ[volume]
      regularize (regularize (convolution f g)) := by
  have h := (convolution_assoc_ae (regularize_integrable hf) hg resolventKernel_integrable).symm
  have he := regularize_congr (regularize_convolution hf hg)
  exact h.trans (EventuallyEq.of_eq he)

/-- All lower support bounds pass unchanged through two regularizations. -/
lemma regularize_twice_support_iff {f : ℝ → ℂ} (hf : Integrable f)
    (hc : SupportedAbove f 0) (c : ℝ) :
    SupportedAbove (regularize (regularize f)) c ↔ SupportedAbove f c := by
  rw [regularize_support_iff (regularize_integrable hf) (regularize_supported hc),
    regularize_support_iff hf hc]

lemma weighted_integrable_whole {f : ℝ → ℂ} (hf : Integrable f)
    (hc : SupportedAbove f 0) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    Integrable (fun t => kernel z t * f t) := by
  have hi := weighted_integrable_L1 hf.restrict hz
  have he : (Ioi (0 : ℝ)).indicator (fun t => kernel z t * f t) =ᵐ[volume]
      (fun t => kernel z t * f t) := by
    filter_upwards [hc, volume.ae_ne 0] with t ht hn
    by_cases hp : 0 < t
    · simp [hp]
    · simp [hp, ht (lt_of_le_of_ne (not_lt.mp hp) hn)]
  exact ((integrable_indicator_iff measurableSet_Ioi).mpr hi).congr he

lemma laplace_convolution_L1 {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hfc : SupportedAbove f 0) (hgc : SupportedAbove g 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    laplace (convolution f g) z = laplace f z * laplace g z := by
  rw [laplace_eq_integral (by simpa using convolution_supportedAbove hfc hgc),
    ← kernel_convolution]
  exact (MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (weighted_integrable_whole hf hfc hz) (weighted_integrable_whole hg hgc hz)).trans (by
      rw [← laplace_eq_integral hfc, ← laplace_eq_integral hgc]
      rfl)

lemma resolventKernel_memLp : MemLp resolventKernel 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm resolventKernel_integrable.aestronglyMeasurable).mpr
  apply resolventKernel_integrable.norm.mono'
    (resolventKernel_integrable.aestronglyMeasurable.norm.pow 2)
  exact Eventually.of_forall fun t => by
    change ‖‖resolventKernel t‖ ^ 2‖ ≤ ‖resolventKernel t‖
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hn := norm_nonneg (resolventKernel t)
    have hb := norm_resolventKernel_le t
    nlinarith

lemma laplace_resolventKernel {z : ℂ} (hz : z ∈ upperHalfPlane) :
    laplace resolventKernel z = (1 - 2 * (Real.pi : ℂ) * Complex.I * z)⁻¹ := by
  have ha : (2 * (Real.pi : ℂ) * Complex.I * z - 1).re < 0 := by
    have hz' : 0 < z.im := hz
    simp only [Complex.sub_re, Complex.one_re]
    norm_num [Complex.mul_re, Complex.mul_im]
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos hz']
  have he : laplace resolventKernel z =
      ∫ t in Ioi (0 : ℝ), Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * z - 1) * (t : ℂ)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [resolventKernel, indicator_of_mem ht, kernel]
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he, integral_exp_mul_complex_Ioi ha 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div, one_div]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * z - 1 =
    -(1 - 2 * (Real.pi : ℂ) * Complex.I * z) by ring, inv_neg, neg_neg]

lemma laplace_regularize {f : ℝ → ℂ} (hf : Integrable f) (hc : SupportedAbove f 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    laplace (regularize f) z =
      laplace f z * (1 - 2 * (Real.pi : ℂ) * Complex.I * z)⁻¹ := by
  rw [regularize, laplace_convolution_L1 hf resolventKernel_integrable hc
    resolventKernel_supported hz, laplace_resolventKernel hz]

lemma laplace_differentiableOn_L1 {f : ℝ → ℂ} (hf : Integrable f)
    (hc : SupportedAbove f 0) : DifferentiableOn ℂ (laplace f) upperHalfPlane := by
  have he : EqOn (laplace f)
      (fun z => (1 - 2 * (Real.pi : ℂ) * Complex.I * z) * laplace (regularize f) z)
      upperHalfPlane := by
    intro z hz
    dsimp only
    rw [laplace_regularize hf hc hz]
    have hn : (1 - 2 * (Real.pi : ℂ) * Complex.I * z) ≠ 0 := by
      intro h
      have he := congrArg Complex.re h
      have hz' : 0 < z.im := hz
      simp [Complex.mul_re, Complex.mul_im] at he
      nlinarith [Real.pi_pos, mul_pos Real.pi_pos hz']
    field_simp
  exact ((by fun_prop : DifferentiableOn ℂ
      (fun z : ℂ => 1 - 2 * (Real.pi : ℂ) * Complex.I * z) upperHalfPlane).mul
    (laplace_differentiableOn _ ((regularize_memLp hf).restrict _))).congr he

lemma vanishes_of_boundedShift {f : ℝ → ℂ} (hf : Integrable f positiveMeasure)
    {c : ℝ} (hc : 0 ≤ c) (hb : BoundedShift f c) : VanishesInitially f c := by
  have hi := extend_integrable hf
  have hs := extend_supported f
  have hB : DifferentiableOn ℂ
      (fun z => exponentialInner (-(2 * Real.pi * c)) z * laplace (extend f) z)
      upperHalfPlane :=
    (by unfold exponentialInner; fun_prop : DifferentiableOn ℂ
      (exponentialInner (-(2 * Real.pi * c))) upperHalfPlane).mul
      (laplace_differentiableOn_L1 hi hs)
  have hbound : ∃ M : ℝ, ∀ z ∈ upperHalfPlane,
      ‖exponentialInner (-(2 * Real.pi * c)) z * laplace (extend f) z‖ ≤ M := by
    simpa only [laplace_extend] using (show ∃ M : ℝ, ∀ z ∈ upperHalfPlane,
      ‖exponentialInner (-(2 * Real.pi * c)) z * laplace f z‖ ≤ M from hb)
  have hH := isH2_bounded_mul hB
    (laplace_isH2 resolventKernel (resolventKernel_memLp.restrict _)) hbound
  have hshift : IsH2 (fun z => exponentialInner (-(2 * Real.pi * c)) z *
      laplace (regularize (extend f)) z) := by
    apply (isH2_congr (G := fun z =>
      (exponentialInner (-(2 * Real.pi * c)) z * laplace (extend f) z) *
        laplace resolventKernel z) ?_).mpr hH
    intro z hz
    dsimp only
    rw [laplace_regularize hi hs hz, laplace_resolventKernel hz]
    exact (mul_assoc _ _ _).symm
  apply (vanishesInitially_iff f hc).mpr
  apply (regularize_support_iff hi hs c).mp
  exact (support_criterion (regularize (extend f)) (regularize_memLp hi)
    (regularize_supported hs) c hc).mpr hshift

theorem bounded_transform_criterion : Spec.BoundedTransformCriterion := by
  intro f hf c hc
  exact ⟨boundedShift_of_vanishes hf hc, vanishes_of_boundedShift hf hc⟩

theorem convolution_endpoints : Spec.ConvolutionEndpoints := by
  intro f g hf hg hfn hgn
  have hfi := extend_integrable hf
  have hgi := extend_integrable hg
  have hfc := extend_supported f
  have hgc := extend_supported g
  have hfn' := (extend_zero_iff f).not.mpr hfn
  have hgn' := (extend_zero_iff g).not.mpr hgn
  obtain ⟨hconv2, hconvn, a, b, ha, hb, hab⟩ :=
    HardySupportBridge.convolution_endpoints (regularize (extend f)) (regularize (extend g))
      (regularize_integrable hfi) (regularize_integrable hgi)
      (regularize_memLp hfi) (regularize_memLp hgi)
      (regularize_nonzero hfi hfc hfn') (regularize_nonzero hgi hgc hgn')
      ⟨0, regularize_supported hfc⟩ ⟨0, regularize_supported hgc⟩
  have he := regularize_convolution_twice hfi hgi
  have hci := convolution_integrable hfi hgi
  have hcc : SupportedAbove (convolution (extend f) (extend g)) 0 := by
    simpa using convolution_supportedAbove hfc hgc
  have hfa := (regularize_endpoint_iff hfi hfc a).mp ha
  have hgb := (regularize_endpoint_iff hgi hgc b).mp hb
  refine ⟨hci, ?_, a, b, (hfa 0).mp hfc, (hgb 0).mp hgc, hfa, hgb, ?_⟩
  · intro hz
    change convolution (extend f) (extend g) =ᵐ[volume] 0 at hz
    have hr : regularize (regularize (convolution (extend f) (extend g))) = 0 := by
      rw [regularize_congr hz, regularize_zero, regularize_zero]
    apply hconvn
    exact he.trans (EventuallyEq.of_eq hr)
  · intro c
    change SupportedAbove (convolution (extend f) (extend g)) c ↔ _
    rw [← regularize_twice_support_iff hci hcc c, ← supportedAbove_congr he c]
    exact hab c

theorem endpoint_addition : Spec.EndpointAddition := by
  intro f g hf hg hfn hgn a b ha hb
  obtain ⟨hi, hn, u, v, hu0, hv0, hu, hv, huv⟩ := convolution_endpoints f g hf hg hfn hgn
  rw [endpoint_unique hu ha, endpoint_unique hv hb] at huv
  exact ⟨hn, huv⟩

lemma complex_ae_zero_iff {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    (fun t => (f t : ℂ)) =ᵐ[μ] 0 ↔ f =ᵐ[μ] 0 := by
  simp only [Filter.EventuallyEq, Pi.zero_apply, Complex.ofReal_eq_zero]

lemma complex_extend_real (f : ℝ → ℝ) :
    extend (fun t => (f t : ℂ)) = fun t => (realExtend f t : ℂ) := by
  funext t
  by_cases ht : 0 < t <;> simp [extend, realExtend, ht]

lemma complex_convolution_real (f g : ℝ → ℝ) :
    halfConvolution (fun t => (f t : ℂ)) (fun t => (g t : ℂ)) =
      fun t => (realHalfConvolution f g t : ℂ) := by
  funext x
  simp only [halfConvolution, HardySupportBridge.convolution, complex_extend_real,
    realHalfConvolution, ← Complex.ofReal_mul]
  exact integral_complex_ofReal

lemma complex_endpoint_real (f : ℝ → ℝ) (a : ℝ) :
    IsLeftEndpoint (fun t => (f t : ℂ)) a ↔ IsRealLeftEndpoint f a := by
  simp only [IsLeftEndpoint, SupportedAbove, IsRealLeftEndpoint, Complex.ofReal_eq_zero]

/-- Explicit transfer to the manuscript's other scalar field. -/
theorem real_convolution_endpoints : Spec.RealConvolutionEndpoints := by
  intro f g hf hg hfn hgn
  obtain ⟨hi, hn, a, b, ha0, hb0, ha, hb, hab⟩ :=
    convolution_endpoints (fun t => (f t : ℂ)) (fun t => (g t : ℂ)) hf.ofReal hg.ofReal
      ((complex_ae_zero_iff positiveMeasure f).not.mpr hfn)
      ((complex_ae_zero_iff positiveMeasure g).not.mpr hgn)
  rw [complex_extend_real] at ha hb
  rw [complex_convolution_real] at hi hn hab
  refine ⟨?_, (complex_ae_zero_iff volume (realHalfConvolution f g)).not.mp hn,
    a, b, ha0, hb0, (complex_endpoint_real _ _).mp ha,
    (complex_endpoint_real _ _).mp hb, (complex_endpoint_real _ _).mp hab⟩
  simpa only [RCLike.re_to_complex, Complex.ofReal_re] using hi.re

theorem real_bounded_transform_criterion : Spec.RealBoundedTransformCriterion := by
  intro f hf c hc
  have h := bounded_transform_criterion (fun t => (f t : ℂ)) hf.ofReal c hc
  exact (complex_ae_zero_iff (volume.restrict (Ioo 0 c)) f).symm.trans h

end ExpandedFA.PartIV.TitchmarshHalfLine
