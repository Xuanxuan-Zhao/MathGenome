import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.HardySmoothMaximalBound
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.AtomicHardySpace
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
Smooth radial maximal bound, paper.tex:18475--18498. A bounded Lipschitz bump
suffices for the analytic atom bound. Local control uses the atom's L∞ bound;
far control uses cancellation, the Lipschitz estimate, and compact support.
The combined majorant is K r / (r + ‖x-c‖)^(d+1), whose integral is independent
of the atom center and radius. Continuous L¹ convolution evaluations then pass
actual atomic series to their original convolutions. Near-minimal coefficient
lifts yield the exact quotient-norm estimate. No dimension is excluded.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
universe v

namespace ExpandedFA.Hardy.HardySmoothMaximalBound
open HardySmoothMaximalBoundSpec

section Evaluation
variable {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]

/-- Integration against a bounded continuous kernel is a continuous functional
on the actual a.e. L¹ quotient. -/
def kernelEvaluation (b : Space d → 𝕜) (hb : Continuous b)
    (B : ℝ≥0) (hB : ∀ x, ‖b x‖ ≤ B) : L1 d 𝕜 →L[𝕜] 𝕜 := by
  have hi (f : L1 d 𝕜) : Integrable (fun y => b y * f y) := by
    apply ((MeasureTheory.L1.integrable_coeFn f).norm.const_mul (B : ℝ)).mono'
    · exact hb.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
    · filter_upwards [] with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _)
  refine LinearMap.mkContinuous
    ({ toFun := fun f => ∫ y, b y * f y
       map_add' := ?_
       map_smul' := ?_ } : L1 d 𝕜 →ₗ[𝕜] 𝕜) B ?_
  · intro f g
    rw [← integral_add (hi f) (hi g)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with y hy
    simpa only [Pi.add_apply, mul_add] using congrArg (fun z => b y * z) hy
  · intro k f
    change _ = k • _
    rw [← integral_smul k]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul k f] with y hy
    simp [hy, smul_eq_mul, mul_left_comm]
  · intro f
    apply (norm_integral_le_integral_norm _).trans
    calc
      (∫ y, ‖b y * f y‖) ≤ ∫ y, (B : ℝ) * ‖f y‖ := by
        apply integral_mono (hi f).norm ((MeasureTheory.L1.integrable_coeFn f).norm.const_mul _)
        intro y
        change ‖b y * f y‖ ≤ (B : ℝ) * ‖f y‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _)
      _ = (B : ℝ) * ‖f‖ := by
        rw [integral_const_mul, MeasureTheory.L1.norm_eq_integral_norm]

theorem dilate_continuous (Φ : Space d → 𝕜) (hΦ : Continuous Φ) (t : ℝ) :
    Continuous (DilateValue Φ t) := by
  exact (hΦ.comp ((continuous_const : Continuous (fun _ : Space d => t⁻¹)).smul
    continuous_id)).const_smul _

theorem dilate_bound (Φ : Space d → 𝕜) (B : ℝ≥0) (hB : ∀ x, ‖Φ x‖ ≤ B)
    (t : ℝ) (x : Space d) :
    ‖DilateValue Φ t x‖ ≤ ‖(t ^ d)⁻¹‖ * B := by
  rw [DilateValue, norm_smul]
  exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)

/-- A fixed-scale convolution value, as a continuous linear functional of f. -/
def convolutionEvaluation (Φ : Space d → 𝕜) (hΦ : Continuous Φ)
    (B : ℝ≥0) (hB : ∀ x, ‖Φ x‖ ≤ B) (t : ℝ) (x : Space d) :
    L1 d 𝕜 →L[𝕜] 𝕜 :=
  kernelEvaluation (fun y => DilateValue Φ t (x-y))
    ((dilate_continuous Φ hΦ t).comp (continuous_const.sub continuous_id))
    (‖(t ^ d)⁻¹‖₊ * B) (by intro y; exact dilate_bound Φ B hB t _)

@[simp] theorem convolutionEvaluation_apply (Φ : Space d → 𝕜) (hΦ : Continuous Φ)
    (B : ℝ≥0) (hB : ∀ x, ‖Φ x‖ ≤ B) (t : ℝ) (x : Space d) (f : L1 d 𝕜) :
    convolutionEvaluation Φ hΦ B hB t x f = ConvolutionValue Φ f t x := rfl

end Evaluation
end ExpandedFA.Hardy.HardySmoothMaximalBound

namespace ExpandedFA.Hardy.HardySmoothMaximalBound
open HardySmoothMaximalBoundSpec
open AtomicHardySpaceSpec

section Extension
variable {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]

/-- Fixed-scale convolution is continuous in x, even for an arbitrary L¹
representative; no pointwise regularity of f is needed. -/
theorem convolution_continuous (Φ : Space d → 𝕜) (hΦ : Continuous Φ)
    (B : ℝ≥0) (hB : ∀ x, ‖Φ x‖ ≤ B) (f : L1 d 𝕜) (t : ℝ) :
    Continuous (ConvolutionValue Φ f t) := by
  have hb : BddAbove (Set.range (fun x => ‖DilateValue Φ t x‖)) :=
    ⟨‖(t ^ d)⁻¹‖ * B, by rintro _ ⟨x, rfl⟩; exact dilate_bound Φ B hB t x⟩
  have hc := hb.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul 𝕜 𝕜) (MeasureTheory.L1.integrable_coeFn f)
    (dilate_continuous Φ hΦ t)
  convert hc using 1
  funext x
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => mul_comm _ _)

/-- An arbitrary supremum of continuous nonnegative functions is lower
semicontinuous. This avoids imposing a countable set of scales in the definition. -/
theorem maximal_measurable (Φ : Space d → 𝕜) (hΦ : Continuous Φ)
    (B : ℝ≥0) (hB : ∀ x, ‖Φ x‖ ≤ B) (f : L1 d 𝕜) :
    Measurable (MaximalValue Φ f) := by
  apply LowerSemicontinuous.measurable
  exact lowerSemicontinuous_biSup fun t _ =>
    (convolution_continuous Φ hΦ B hB f t).enorm.lowerSemicontinuous

/-- The convolution of an actual L¹ atomic sum is dominated pointwise by the
sum of its atom maximal functions. Continuity of the evaluation on L¹ proves
that this is the convolution of the original f, including every scale. -/
theorem maximal_series_le (Φ : Space d → 𝕜) (hΦ : Continuous Φ)
    (B : ℝ≥0) (hB : ∀ x, ‖Φ x‖ ≤ B)
    (a : ℕ → Atom d 𝕜) (c : ℕ → 𝕜) (f : L1 d 𝕜)
    (hf : HasSum (fun j => c j • (a j).val) f) (x : Space d) :
    MaximalValue Φ f x ≤ ∑' j, ‖c j‖ₑ * MaximalValue Φ (a j).val x := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  have hs := hf.mapL (convolutionEvaluation Φ hΦ B hB t x)
  apply hs.enorm_le_of_bounded ENNReal.summable.hasSum
  intro j
  simp only [map_smul, convolutionEvaluation_apply, enorm_smul]
  exact mul_le_mul' le_rfl (le_iSup_of_le t (le_iSup_of_le ht le_rfl))

/-- Integrating the preceding pointwise series gives its coefficient bound. -/
theorem series_integral_bound (Φ : Space d → 𝕜) (hΦ : Continuous Φ)
    (B : ℝ≥0) (hB : ∀ x, ‖Φ x‖ ≤ B) (C : ℝ≥0)
    (hC : ∀ a : Atom d 𝕜, (∫⁻ x, MaximalValue Φ a.val x) ≤ C)
    (a : ℕ → Atom d 𝕜) (c : ℕ → 𝕜) (hc : Summable (fun j => ‖c j‖))
    (f : L1 d 𝕜) (hf : HasSum (fun j => c j • (a j).val) f) :
    (∫⁻ x, MaximalValue Φ f x) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal (∑' j, ‖c j‖) := by
  calc
    (∫⁻ x, MaximalValue Φ f x) ≤
        ∫⁻ x, ∑' j, ‖c j‖ₑ * MaximalValue Φ (a j).val x :=
      lintegral_mono (maximal_series_le Φ hΦ B hB a c f hf)
    _ = ∑' j, ‖c j‖ₑ * ∫⁻ x, MaximalValue Φ (a j).val x := by
      rw [lintegral_tsum]
      · congr 1
        funext j
        exact lintegral_const_mul _ (maximal_measurable Φ hΦ B hB (a j).val)
      · intro j
        exact (measurable_const.mul (maximal_measurable Φ hΦ B hB (a j).val)).aemeasurable
    _ ≤ ∑' j, ‖c j‖ₑ * C := ENNReal.tsum_le_tsum (fun j => mul_le_mul' le_rfl (hC _))
    _ = (C : ℝ≥0∞) * ENNReal.ofReal (∑' j, ‖c j‖) := by
      rw [ENNReal.tsum_mul_right]
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hc]
      simp only [ofReal_norm, mul_comm]

theorem atomic_extension : AtomicExtension.{v} := by
  intro d 𝕜 _ Φ hΦ hB C hC h
  obtain ⟨B, hB⟩ := hB
  refine ⟨maximal_measurable Φ hΦ B hB _, ?_⟩
  have he (ε : ℝ) (hε : 0 < ε) :
      (∫⁻ x, MaximalValue Φ (EmbeddingValue volume h) x) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (‖h‖ + ε) := by
    obtain ⟨c, hc, hn⟩ := Submodule.Quotient.norm_mk_lt h hε
    have : Nonempty (Atom d 𝕜) := AtomicHardySpace.euclidean_atoms_nonempty d 𝕜
    obtain ⟨a, b, hb, hs⟩ := AtomicHardySpace.coefficient_sequence volume c
    have hsum : HasSum (fun j => b j • (a j).val) (EmbeddingValue volume h) := by
      rw [← hc]
      exact hs
    apply (series_integral_bound Φ hΦ B hB C hC a b hb.summable _ hsum).trans
    apply mul_le_mul' le_rfl
    rw [hb.tsum_eq]
    exact ENNReal.ofReal_le_ofReal hn.le
  have hcont : Continuous (fun ε : ℝ => (C : ℝ≥0∞) * ENNReal.ofReal (‖h‖ + ε)) :=
    (ENNReal.continuous_const_mul (by simp)).comp
      (ENNReal.continuous_ofReal.comp (continuous_const.add continuous_id))
  have ht : Tendsto (fun ε : ℝ => (C : ℝ≥0∞) * ENNReal.ofReal (‖h‖ + ε))
      (𝓝[>] 0) (𝓝 ((C : ℝ≥0∞) * ENNReal.ofReal ‖h‖)) := by
    simpa only [add_zero] using hcont.continuousWithinAt.tendsto (s := Set.Ioi 0) (x := 0)
  exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with ε hε using he ε hε)

end Extension
end ExpandedFA.Hardy.HardySmoothMaximalBound

namespace ExpandedFA.Hardy.HardySmoothMaximalBound
open HardySmoothMaximalBoundSpec

/-- Compact support and C¹ regularity give a finite global support radius and
common bound for the function and its derivative, hence a Lipschitz bound. -/
theorem smooth_kernel_control {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (Φ : Space d → 𝕜) (hΦ : ContDiff ℝ 1 Φ) (hs : HasCompactSupport Φ) :
    ∃ R : ℝ, 0 < R ∧ ∃ A : ℝ≥0, KernelControl Φ R A := by
  obtain ⟨R, hR, hsub⟩ := hs.isBounded.subset_ball_lt 0 (0 : Space d)
  have h0 : BddAbove (Set.range (fun x => ‖Φ x‖)) :=
    by simpa only [← Set.range_comp, Function.comp_def] using
      ((hs.isCompact_range hΦ.continuous).image continuous_norm).bddAbove
  have h1 : BddAbove (Set.range (fun x => ‖fderiv ℝ Φ x‖)) :=
    by simpa only [← Set.range_comp, Function.comp_def] using
      (((hs.fderiv ℝ).isCompact_range (hΦ.continuous_fderiv (by decide))).image
        continuous_norm).bddAbove
  obtain ⟨B₀, hB₀⟩ := h0
  obtain ⟨B₁, hB₁⟩ := h1
  let A : ℝ≥0 := ⟨max 0 (max B₀ B₁), le_max_left _ _⟩
  have ha0 (x : Space d) : ‖Φ x‖ ≤ A :=
    (hB₀ (Set.mem_range_self x)).trans ((le_max_left _ _).trans (le_max_right _ _))
  have ha1 (x : Space d) : ‖fderiv ℝ Φ x‖₊ ≤ A := by
    exact_mod_cast (hB₁ (Set.mem_range_self x)).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨R, hR, A, ?_, ha0, lipschitzWith_of_nnnorm_fderiv_le (hΦ.differentiable (by decide)) ha1⟩
  intro x hx
  apply Function.notMem_support.mp
  intro hmem
  have hx' := hsub (subset_tsupport Φ hmem)
  rw [mem_ball_zero_iff] at hx'
  exact (hx.trans hx').false

/-- The uniform C¹ class has the pointwise controls needed by the atom lemma. -/
theorem unit_kernel_control {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (Φ : Space d → 𝕜) (hΦ : ContDiff ℝ 1 Φ)
    (hs : Function.support Φ ⊆ Metric.closedBall 0 1) (A : ℝ≥0)
    (h0 : ∀ x, ‖Φ x‖ ≤ A) (h1 : ∀ x, ‖fderiv ℝ Φ x‖ ≤ A) :
    KernelControl Φ 1 A := by
  refine ⟨?_, h0, lipschitzWith_of_nnnorm_fderiv_le (hΦ.differentiable (by decide)) ?_⟩
  · intro x hx
    apply Function.notMem_support.mp
    intro hmem
    have hm := hs hmem
    rw [mem_closedBall_zero_iff] at hm
    exact (not_le.mpr hx) hm
  · intro x
    exact_mod_cast h1 x

/-- This reduction records exactly the remaining analytic obligation; it does
not assume it in either of the main, independent source statements. -/
theorem bounds_of_uniform_atom_bound (ha : UniformAtomBound.{v}) :
    SmoothBound.{v} ∧ UniformSmoothBound.{v} := by
  constructor
  · intro d 𝕜 _ Φ hΦ hs
    obtain ⟨R, hR, A, hA⟩ := smooth_kernel_control Φ hΦ hs
    obtain ⟨C, hC⟩ := ha d R hR A
    refine ⟨C, ?_⟩
    exact atomic_extension d Φ hΦ.continuous ⟨A, hA.2.1⟩ C (hC Φ hA)
  · intro d A
    obtain ⟨C, hC⟩ := ha d 1 zero_lt_one A
    refine ⟨C, ?_⟩
    intro 𝕜 _ Φ hΦ hs h0 h1
    exact atomic_extension d Φ hΦ.continuous ⟨A, h0⟩ C
      (hC Φ (unit_kernel_control Φ hΦ hs A h0 h1))

end ExpandedFA.Hardy.HardySmoothMaximalBound

namespace ExpandedFA.Hardy.HardySmoothMaximalBound
open HardySmoothMaximalBoundSpec

section Cancellation
variable {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]

/-- The defining integral exists at every point and scale for bounded continuous
bumps and an L¹ input. -/
theorem convolution_integrable (Φ f : Space d → 𝕜) (hΦ : Continuous Φ)
    (B : ℝ≥0) (hB : ∀ x, ‖Φ x‖ ≤ B) (hf : Integrable f) (t : ℝ) (x : Space d) :
    Integrable (fun y => DilateValue Φ t (x-y) * f y) := by
  apply (hf.norm.const_mul (‖(t^d)⁻¹‖ * B)).mono'
  · exact ((dilate_continuous Φ hΦ t).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · filter_upwards [] with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (dilate_bound Φ B hB t _) (norm_nonneg _)

/-- The quantitative Lipschitz estimate after dilation. -/
theorem dilate_sub_bound (Φ : Space d → 𝕜) (A : ℝ≥0) (hA : LipschitzWith A Φ)
    (t : ℝ) (u w : Space d) :
    ‖DilateValue Φ t u - DilateValue Φ t w‖ ≤
      (‖(t^d)⁻¹‖ * A * ‖t⁻¹‖) * ‖u-w‖ := by
  simp only [DilateValue, ← smul_sub, norm_smul]
  calc
    ‖(t^d)⁻¹‖ * ‖Φ (t⁻¹ • u) - Φ (t⁻¹ • w)‖ ≤
        ‖(t^d)⁻¹‖ * (A * ‖t⁻¹ • u - t⁻¹ • w‖) := by
      gcongr
      exact hA.norm_sub_le _ _
    _ = (‖(t^d)⁻¹‖ * A * ‖t⁻¹‖) * ‖u-w‖ := by
      rw [← smul_sub, norm_smul]
      ring

/-- Cancellation subtracts a constant kernel value at the center of the atom.
It holds as an equality of the original Lebesgue integrals. -/
theorem convolution_cancellation (Φ f : Space d → 𝕜) (hΦ : Continuous Φ)
    (B : ℝ≥0) (hB : ∀ x, ‖Φ x‖ ≤ B) (hf : Integrable f)
    (hz : (∫ y, f y) = 0) (t : ℝ) (x c : Space d) :
    ConvolutionValue Φ f t x =
      ∫ y, (DilateValue Φ t (x-y) - DilateValue Φ t (x-c)) * f y := by
  simp_rw [sub_mul]
  rw [integral_sub (convolution_integrable Φ f hΦ B hB hf t x)
    (hf.const_mul _), integral_const_mul, hz, mul_zero, sub_zero]
  rfl

/-- A mean-zero input supported in B(c,r), with L¹ norm at most one, has the
standard cancellation bound at every scale. No smoothness beyond Lipschitz is
needed, and support is only required a.e. -/
theorem cancellation_bound (Φ f : Space d → 𝕜) (hΦ : Continuous Φ)
    (A B : ℝ≥0) (hB : ∀ x, ‖Φ x‖ ≤ B) (hA : LipschitzWith A Φ)
    (hf : Integrable f) (hz : (∫ y, f y) = 0) (c : Space d) (r : ℝ) (hr : 0 < r)
    (hs : ∀ᵐ y ∂volume, y ∉ Metric.ball c r → f y = 0)
    (hn : (∫ y, ‖f y‖) ≤ 1) (t : ℝ) (x : Space d) :
    ‖ConvolutionValue Φ f t x‖ ≤ (‖(t^d)⁻¹‖ * A * ‖t⁻¹‖) * r := by
  let K : ℝ := ‖(t^d)⁻¹‖ * A * ‖t⁻¹‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hi : Integrable (fun y =>
      (DilateValue Φ t (x-y) - DilateValue Φ t (x-c)) * f y) := by
    simp_rw [sub_mul]
    exact (convolution_integrable Φ f hΦ B hB hf t x).sub (hf.const_mul _)
  rw [convolution_cancellation Φ f hΦ B hB hf hz t x c]
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ y, ‖(DilateValue Φ t (x-y) - DilateValue Φ t (x-c)) * f y‖) ≤
        ∫ y, (K*r) * ‖f y‖ := by
      apply integral_mono_ae hi.norm (hf.norm.const_mul _)
      filter_upwards [hs] with y hy
      by_cases hyB : y ∈ Metric.ball c r
      · rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply (dilate_sub_bound Φ A hA t (x-y) (x-c)).trans
        have he : x-y-(x-c) = c-y := by abel
        rw [he, norm_sub_rev]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Metric.mem_ball, dist_eq_norm] using hyB.le) hK
      · simp [hy hyB, mul_zero, norm_zero]
    _ = K*r * ∫ y, ‖f y‖ := integral_const_mul _ _
    _ ≤ K*r := mul_le_of_le_one_right (mul_nonneg hK hr.le) hn

end Cancellation
end ExpandedFA.Hardy.HardySmoothMaximalBound

namespace ExpandedFA.Hardy.HardySmoothMaximalBound
open HardySmoothMaximalBoundSpec

section Tail
variable {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]

/-- Compact support forces the convolution to vanish at scales that cannot
reach the atom ball. -/
theorem convolution_zero_of_small_scale (Φ f : Space d → 𝕜) (R : ℝ)
    (hR : ∀ z, R < ‖z‖ → Φ z = 0) (c : Space d) (r : ℝ)
    (hs : ∀ᵐ y ∂volume, y ∉ Metric.ball c r → f y = 0)
    (t : ℝ) (ht : 0 < t) (x : Space d) (hx : r+t*R ≤ ‖x-c‖) :
    ConvolutionValue Φ f t x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hs] with y hy
  by_cases hyB : y ∈ Metric.ball c r
  · have hyN : ‖y-c‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hyB
    have htri : ‖x-c‖ ≤ ‖x-y‖ + ‖y-c‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (x-y) (y-c)
    have hN : t*R < ‖x-y‖ := by linarith
    have hn : R < ‖t⁻¹ • (x-y)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      have hv := mul_lt_mul_of_pos_left hN (inv_pos.mpr ht)
      simpa only [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul] using hv
    simp [DilateValue, hR _ hn]
  · simp [hy hyB]

/-- Away from twice the support radius, the all-scale supremum has the
integrable decay predicted by cancellation. The denominator is a natural
power, avoiding any conventions about negative real powers at zero. -/
theorem atom_tail_bound (Φ : Space d → 𝕜) (R : ℝ) (hR : 0 < R)
    (A : ℝ≥0) (hΦ : KernelControl Φ R A) (a : Atom d 𝕜)
    (c : Space d) (r : ℝ) (hr : 0 < r)
    (hs : ∀ᵐ y ∂volume, y ∉ Metric.ball c r → a.val y = 0)
    (x : Space d) (hx : 2*r ≤ ‖x-c‖) :
    MaximalValue Φ a.val x ≤
      ENNReal.ofReal ((A : ℝ) * r * (2*R)^(d+1) / ‖x-c‖^(d+1)) := by
  have hD : 0 < ‖x-c‖ := lt_of_lt_of_le (by linarith) hx
  have hΦc := hΦ.2.2.continuous
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  by_cases hsmall : t < ‖x-c‖ / (2*R)
  · have hh : r+t*R ≤ ‖x-c‖ := by
      have hmul := (lt_div_iff₀ (by positivity : 0 < 2*R)).mp hsmall
      nlinarith
    rw [convolution_zero_of_small_scale Φ a.val R hΦ.1 c r hs t ht x hh]
    simp
  · have htD : ‖x-c‖ / (2*R) ≤ t := le_of_not_gt hsmall
    have hinv : t⁻¹ ≤ (2*R) / ‖x-c‖ := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ ht).2
      have hmul := (div_le_iff₀ (by positivity : 0 < 2*R)).mp htD
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).2
      nlinarith
    have hn := cancellation_bound Φ a.val hΦc A A hΦ.2.1 hΦ.2.2
      (MeasureTheory.L1.integrable_coeFn a.val) a.property.1 c r hr hs
      (by rw [← MeasureTheory.L1.norm_eq_integral_norm]; exact AtomicHardySpace.atom_norm_le volume a)
      t x
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    apply hn.trans
    have he : (‖(t^d)⁻¹‖ * (A : ℝ) * ‖t⁻¹‖) * r = (A : ℝ) * r * (t⁻¹)^(d+1) := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos ht _)),
        abs_of_pos (inv_pos.mpr ht), ← inv_pow, pow_succ]
      ring
    rw [he, mul_div_assoc, ← div_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (inv_nonneg.mpr ht.le) hinv (d+1)

end Tail
end ExpandedFA.Hardy.HardySmoothMaximalBound

namespace ExpandedFA.Hardy.HardySmoothMaximalBound
open HardySmoothMaximalBoundSpec

section LocalBound
variable {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]

/-- The absolute integral of a rescaled kernel is unchanged. -/
theorem dilate_integral_norm (Φ : Space d → 𝕜) (t : ℝ) (ht : 0 < t) :
    (∫ y, ‖DilateValue Φ t y‖) = ∫ y, ‖Φ y‖ := by
  simp only [DilateValue, norm_smul]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (fun y : Space d => ‖Φ y‖) ht.le]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos ht _))]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ht.ne'), one_mul]

/-- The elementary local estimate uses the infinity-atom bound instead of L².
The bump's support is enlarged to an open ball only for the proof, avoiding a
boundary-measure argument (also in dimension zero). -/
theorem atom_local_bound (Φ : Space d → 𝕜) (R : ℝ) (hR : 0 < R)
    (A : ℝ≥0) (hΦ : KernelControl Φ R A) (a : Atom d 𝕜)
    (c : Space d) (r : ℝ) (_hr : 0 < r)
    (ha : ∀ᵐ y ∂volume, ‖a.val y‖ ≤ (volume.real (Metric.ball c r))⁻¹)
    (x : Space d) :
    MaximalValue Φ a.val x ≤ ENNReal.ofReal
      ((A : ℝ) * volume.real (Metric.ball (0 : Space d) (2*R)) /
        volume.real (Metric.ball c r)) := by
  have hΦc := hΦ.2.2.continuous
  have hcomp : HasCompactSupport Φ := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Space d) R)
    intro y hy
    exact hΦ.1 y (by simpa only [mem_closedBall_zero_iff, not_le] using hy)
  have hΦi : Integrable Φ := hΦc.integrable_of_hasCompactSupport hcomp
  have hbi : Integrable ((Metric.ball (0 : Space d) (2*R)).indicator (fun _ => (A : ℝ))) :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
      (integrableOn_const measure_ball_ne_top)
  have hib : (∫ y, ‖Φ y‖) ≤ (A : ℝ) * volume.real (Metric.ball (0 : Space d) (2*R)) := by
    calc
      (∫ y, ‖Φ y‖) ≤ ∫ y, (Metric.ball (0 : Space d) (2*R)).indicator (fun _ => (A : ℝ)) y := by
        apply integral_mono hΦi.norm hbi
        intro y
        by_cases hy : y ∈ Metric.ball (0 : Space d) (2*R)
        · simpa only [Set.indicator_of_mem hy] using hΦ.2.1 y
        · have hy' : R < ‖y‖ := by
            have hle : 2*R ≤ ‖y‖ := by simpa only [mem_ball_zero_iff, not_lt] using hy
            linarith
          simp [hΦ.1 y hy', Set.indicator_of_notMem hy]
      _ = _ := by rw [integral_indicator_const _ Metric.isOpen_ball.measurableSet]; simp [smul_eq_mul, mul_comm]
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  have hci := convolution_integrable Φ a.val hΦc A hΦ.2.1
    (MeasureTheory.L1.integrable_coeFn a.val) t x
  have hdi : Integrable (fun y => ‖DilateValue Φ t (x-y)‖) := by
    exact (((hΦi.comp_smul (inv_ne_zero ht.ne')).smul ((t^d)⁻¹)).norm).comp_sub_left x

  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ y, ‖DilateValue Φ t (x-y) * a.val y‖) ≤
        ∫ y, ‖DilateValue Φ t (x-y)‖ * (volume.real (Metric.ball c r))⁻¹ := by
      apply integral_mono_ae hci.norm (hdi.mul_const _)
      filter_upwards [ha] with y hy
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ = (∫ y, ‖Φ y‖) * (volume.real (Metric.ball c r))⁻¹ := by
      rw [integral_mul_const, integral_sub_left_eq_self (μ := (volume : Measure (Space d))) (fun y => ‖DilateValue Φ t y‖),
        dilate_integral_norm Φ t ht]
    _ ≤ _ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hib (by positivity)

end LocalBound
end ExpandedFA.Hardy.HardySmoothMaximalBound

namespace ExpandedFA.Hardy.HardySmoothMaximalBound
open HardySmoothMaximalBoundSpec

section Envelope
variable {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]

private theorem real_ball (c : Space d) (r : ℝ) (hr : 0 < r) :
    volume.real (Metric.ball c r) = r^d * volume.real (Metric.ball (0 : Space d) 1) := by
  simp only [measureReal_def, volume.addHaar_ball_of_pos c hr, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le d)]

private theorem local_bound_simplified (Φ : Space d → 𝕜) (R : ℝ) (hR : 0 < R)
    (A : ℝ≥0) (hΦ : KernelControl Φ R A) (a : Atom d 𝕜)
    (c : Space d) (r : ℝ) (hr : 0 < r)
    (ha : ∀ᵐ y ∂volume, ‖a.val y‖ ≤ (volume.real (Metric.ball c r))⁻¹)
    (x : Space d) :
    MaximalValue Φ a.val x ≤ ENNReal.ofReal ((A : ℝ) * (2*R)^d / r^d) := by
  have hV : volume.real (Metric.ball (0 : Space d) 1) ≠ 0 :=
    (ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_ne_top).ne'
  convert atom_local_bound Φ R hR A hΦ a c r hr ha x using 1
  congr 1
  rw [real_ball 0 (2*R) (by positivity), real_ball c r hr]
  field_simp

private def decayWeight (d : ℕ) (x : Space d) : ℝ := ((1+‖x‖)^(d+1))⁻¹

private theorem decayWeight_integrable (d : ℕ) : Integrable (decayWeight d) := by
  have hi : Integrable (fun x : Space d => (1+‖x‖)^(-((d:ℝ)+1))) :=
    integrable_one_add_norm (by simp only [finrank_euclideanSpace_fin]; linarith)
  convert hi using 1
  funext x
  rw [Real.rpow_neg (by positivity), ← Nat.cast_one, ← Nat.cast_add, Real.rpow_natCast]
  simp [decayWeight]

private theorem decayWeight_nonneg (d : ℕ) (x : Space d) : 0 ≤ decayWeight d x := by
  dsimp [decayWeight]
  positivity

/-- A convenient integrable envelope for the local and far estimates. -/
private theorem two_region_bound (A R r D : ℝ) (d : ℕ) (hA : 0 ≤ A)
    (hR : 0 < R) (hr : 0 < r) (hD : 0 ≤ D) :
    let K := A*(2*R)^d*3^(d+1) + A*(4*R)^(d+1)
    (D < 2*r → A*(2*R)^d/r^d ≤ K*r/(r+D)^(d+1)) ∧
    (2*r ≤ D → A*r*(2*R)^(d+1)/D^(d+1) ≤ K*r/(r+D)^(d+1)) := by
  dsimp
  constructor
  · intro hnear
    apply (div_le_div_iff₀ (pow_pos hr d) (pow_pos (by positivity : 0 < r+D) (d+1))).2
    calc
      A*(2*R)^d*(r+D)^(d+1) ≤ A*(2*R)^d*(3*r)^(d+1) := by
        gcongr
        linarith
      _ = (A*(2*R)^d*3^(d+1))*r*r^d := by rw [mul_pow, pow_succ]; ring
      _ ≤ (A*(2*R)^d*3^(d+1) + A*(4*R)^(d+1))*r*r^d := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr.le d)
        apply mul_le_mul_of_nonneg_right _ hr.le
        exact le_add_of_nonneg_right (by positivity)
  · intro hfar
    have hDp : 0 < D := lt_of_lt_of_le (by positivity : 0 < 2*r) hfar
    apply (div_le_div_iff₀ (pow_pos hDp (d+1))
      (pow_pos (by positivity : 0 < r+D) (d+1))).2
    calc
      A*r*(2*R)^(d+1)*(r+D)^(d+1) ≤ A*r*(2*R)^(d+1)*(2*D)^(d+1) := by
        gcongr
        linarith
      _ = (A*(4*R)^(d+1))*r*D^(d+1) := by
        have hh : (4*R)^(d+1) = (2*R)^(d+1) * 2^(d+1) := by
          rw [← mul_pow]
          congr 1
          ring
        rw [hh, mul_pow (2:ℝ) D]
        ring
      _ ≤ (A*(2*R)^d*3^(d+1) + A*(4*R)^(d+1))*r*D^(d+1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hD (d+1))
        apply mul_le_mul_of_nonneg_right _ hr.le
        exact le_add_of_nonneg_left (by positivity)

private theorem envelope_eq (K r : ℝ) (hr : 0 < r) (c x : Space d) :
    K*r/(r+‖x-c‖)^(d+1) =
      K*(r^d)⁻¹ * decayWeight d (r⁻¹ • (x-c)) := by
  have hsum : r+‖x-c‖ ≠ 0 := (by positivity : 0 < r+‖x-c‖).ne'
  simp only [decayWeight, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  have he : 1+r⁻¹*‖x-c‖ = (r+‖x-c‖)/r := by field_simp
  rw [he, div_pow, inv_div]
  field_simp
  rw [pow_succ]
  ring

private theorem envelope_integrable (K r : ℝ) (hr : 0 < r) (c : Space d) :
    Integrable (fun x => K*r/(r+‖x-c‖)^(d+1)) := by
  simp_rw [envelope_eq K r hr c]
  exact (((decayWeight_integrable d).comp_smul (inv_ne_zero hr.ne')).comp_sub_right c).const_mul _

private theorem envelope_integral (K r : ℝ) (hr : 0 < r) (c : Space d) :
    (∫ x, K*r/(r+‖x-c‖)^(d+1)) = K * ∫ x, decayWeight d x := by
  simp_rw [envelope_eq K r hr c]
  rw [integral_const_mul,
    integral_sub_right_eq_self (μ := (volume : Measure (Space d)))
      (fun x : Space d => decayWeight d (r⁻¹ • x)) c,
    Measure.integral_comp_inv_smul_of_nonneg volume (decayWeight d) hr.le]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  field_simp

end Envelope
end ExpandedFA.Hardy.HardySmoothMaximalBound

namespace ExpandedFA.Hardy.HardySmoothMaximalBound
open HardySmoothMaximalBoundSpec

/-- The uniform atom estimate, proved by the local L∞ estimate and the
cancellation tail, with a single integrable envelope after translation/scaling. -/
theorem uniform_atom_bound : UniformAtomBound.{v} := by
  intro d R hR A
  let K : ℝ := (A : ℝ)*(2*R)^d*3^(d+1) + (A : ℝ)*(4*R)^(d+1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let I : ℝ := ∫ x, decayWeight d x
  have hI : 0 ≤ I := integral_nonneg (decayWeight_nonneg d)
  let C : ℝ≥0 := ⟨K*I, mul_nonneg hK hI⟩
  refine ⟨C, ?_⟩
  intro 𝕜 _ Φ hΦ a
  rcases a.property.2 with ⟨c, r, hr, _, _, hb⟩
  have hs : ∀ᵐ y ∂volume, y ∉ Metric.ball c r → a.val y = 0 := hb.mono (fun _ h => h.1)
  have ha : ∀ᵐ y ∂volume, ‖a.val y‖ ≤ (volume.real (Metric.ball c r))⁻¹ :=
    hb.mono (fun _ h => h.2)
  have hbound (x : Space d) :
      MaximalValue Φ a.val x ≤ ENNReal.ofReal (K*r/(r+‖x-c‖)^(d+1)) := by
    have htwo := two_region_bound A R r ‖x-c‖ d A.coe_nonneg hR hr (norm_nonneg _)
    by_cases hx : ‖x-c‖ < 2*r
    · exact (local_bound_simplified Φ R hR A hΦ a c r hr ha x).trans
        (ENNReal.ofReal_le_ofReal (htwo.1 hx))
    · exact (atom_tail_bound Φ R hR A hΦ a c r hr hs x (le_of_not_gt hx)).trans
        (ENNReal.ofReal_le_ofReal (htwo.2 (le_of_not_gt hx)))
  calc
    (∫⁻ x, MaximalValue Φ a.val x) ≤ ∫⁻ x, ENNReal.ofReal (K*r/(r+‖x-c‖)^(d+1)) :=
      lintegral_mono hbound
    _ = ENNReal.ofReal (∫ x : Space d, K*r/(r+‖x-c‖)^(d+1)) := by
      apply (ofReal_integral_eq_lintegral_ofReal (envelope_integrable K r hr c) _).symm
      exact Filter.Eventually.of_forall (fun x => by positivity)
    _ = (C : ℝ≥0∞) := by
      rw [envelope_integral K r hr c]
      exact ENNReal.ofReal_eq_coe_nnreal (mul_nonneg hK hI)

/-- The smooth radial maximal estimate on the completed atomic Hardy space. -/
theorem smooth_bound : SmoothBound.{v} :=
  (bounds_of_uniform_atom_bound uniform_atom_bound).1

/-- The same constant works for all unit-ball bumps with bounded C¹ norm. -/
theorem uniform_smooth_bound : UniformSmoothBound.{v} :=
  (bounds_of_uniform_atom_bound uniform_atom_bound).2

end ExpandedFA.Hardy.HardySmoothMaximalBound

namespace ExpandedFA.Hardy.HardySmoothMaximalBound
open HardySmoothMaximalBoundSpec

abbrev dilate : DilateType.{v} := @DilateValue
abbrev convolution : ConvolutionType.{v} := @ConvolutionValue
abbrev maximal : MaximalType.{v} := @MaximalValue

theorem convolution_formula : ConvolutionFormula.{v} := by
  intro d 𝕜 _ Φ f t x
  exact (MeasureTheory.convolution_mul_swap (𝕜 := 𝕜)
    (f := DilateValue Φ t) (g := f) (μ := volume) (x := x)).symm

theorem representative_independence : RepresentativeIndependence.{v} := by
  intro d 𝕜 _ Φ f g hfg
  have he (t : ℝ) (x : Space d) : ConvolutionValue Φ f t x = ConvolutionValue Φ g t x := by
    apply integral_congr_ae
    exact hfg.mono (fun y hy => congrArg (fun z => DilateValue Φ t (x-y) * z) hy)
  funext x
  simp only [MaximalValue, he]

end ExpandedFA.Hardy.HardySmoothMaximalBound
