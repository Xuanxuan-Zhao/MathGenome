import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyGrandForward
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyMaximalInterfaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.AtomicHardySpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.HardyCZEndpoint
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
The uniform atom estimate uses a direct local bound: the normalized compact
kernels have L¹ norm at most the unit-ball volume, and an atom has essential
supremum at most its supporting ball's inverse volume. This replaces the
source's local L² maximal argument. The exterior estimate uses cancellation,
the uniform first-derivative bounds, and the support condition. Both bounds
hold before taking the supremum over tests and positive scales.

Fixed convolution evaluations are continuous linear functionals on L¹.
They pass atomic series through convolution pointwise, after which Tonelli
and arbitrarily close quotient representatives yield the stated atomic norm.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace ExpandedFA.PartIV.HardyGrandForward
open ExpandedFA.Fourier HardyMaximalSpec ExpandedFA.Hardy.AtomicHardySpaceSpec

variable {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}

lemma test_lipschitz (hN : 1 ≤ N) (ψ : Tests 𝕜 d N) (x y : Euclidean d) :
    ‖ψ.val x - ψ.val y‖ ≤ (d : ℝ) * ‖x - y‖ := by
  have hb (z : Euclidean d) : ‖fderiv ℝ ψ.val z‖ ≤ (d : ℝ) := by
    apply (ExpandedFA.SingularIntegrals.CZWeak.linear_norm_le_sum_basis _).trans
    calc
      (∑ i : Fin d, ‖fderiv ℝ ψ.val z (basisVector i)‖) ≤ ∑ _i : Fin d, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [coordinatePartial, iteratedFDeriv_one_apply] using
          ψ.property.2.2 1 hN (fun _ => i) z
      _ = _ := by simp
  exact (convex_univ : Convex ℝ (Set.univ : Set (Euclidean d))).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => ψ.property.1.differentiable (by norm_num) z) (fun z _ => hb z)
    (mem_univ y) (mem_univ x)

lemma test_zero_of_norm (ψ : Tests 𝕜 d N) {x : Euclidean d} (hx : 1 ≤ ‖x‖) :
    ψ.val x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have := ψ.property.2.1 h
  simp only [Metric.mem_ball, dist_zero_right] at this
  exact (not_lt_of_ge hx) this

lemma dilate_bound (ψ : Tests 𝕜 d N) (t : ℝ) (ht : 0 < t) (x : Euclidean d) :
    ‖dilate t ψ.val x‖ ≤ (t ^ d)⁻¹ := by
  rw [dilate, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (HardyMaximal.test_bounded ψ _)

lemma dilate_continuous (ψ : Tests 𝕜 d N) (t : ℝ) :
    Continuous (dilate t ψ.val) := by
  unfold dilate
  exact continuous_const.smul (ψ.property.1.continuous.comp (continuous_const_smul t⁻¹))

lemma dilate_integrable (ψ : Tests 𝕜 d N) (t : ℝ) (ht : 0 < t) :
    Integrable (dilate t ψ.val) := by
  have hψ : Integrable ψ.val :=
    ψ.property.1.continuous.integrable_of_hasCompactSupport
      ((isCompact_closedBall (0 : Euclidean d) 1).of_isClosed_subset (isClosed_tsupport _)
        (ψ.property.2.1.trans Metric.ball_subset_closedBall))
  exact (hψ.comp_smul (inv_ne_zero ht.ne')).smul ((t ^ d)⁻¹)

lemma dilate_norm_integral (ψ : Tests 𝕜 d N) (t : ℝ) (ht : 0 < t) :
    (∫ x, ‖dilate t ψ.val x‖) = ∫ x, ‖ψ.val x‖ := by
  simp only [dilate, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (t ^ d)⁻¹)]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (fun x => ‖ψ.val x‖) ht.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ht.ne'), one_mul]

lemma test_integral_bound (ψ : Tests 𝕜 d N) :
    (∫ x, ‖ψ.val x‖) ≤ volume.real (Metric.ball (0 : Euclidean d) 1) := by
  have hb : ∀ x, ‖ψ.val x‖ ≤ (Metric.ball (0 : Euclidean d) 1).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ Metric.ball (0 : Euclidean d) 1
    · simpa [hx] using HardyMaximal.test_bounded ψ x
    · have hz : ψ.val x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (ψ.property.2.1 h))
      simp [hx, hz]
  have hi : Integrable ψ.val := by
    convert dilate_integrable ψ 1 (by norm_num) using 1
    ext x
    simp [HardyMaximalSpec.dilate]
  have hc : Integrable ((Metric.ball (0 : Euclidean d) 1).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const measure_ball_ne_top).integrable_indicator Metric.isOpen_ball.measurableSet
  exact (integral_mono hi.norm hc hb).trans_eq (by rw [integral_indicator_const 1 Metric.isOpen_ball.measurableSet]; simp)

lemma convolve_integrable (ψ : Tests 𝕜 d N) {f : Euclidean d → 𝕜}
    (hf : Integrable f) (t : ℝ) (ht : 0 < t) (x : Euclidean d) :
    Integrable (fun y => dilate t ψ.val (x - y) * f y) :=
  hf.bdd_mul ((dilate_continuous ψ t).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun y => dilate_bound ψ t ht (x - y))

lemma convolve_bound_of_ae_bound (ψ : Tests 𝕜 d N) {f : Euclidean d → 𝕜}
    (hf : Integrable f) {B : ℝ} (hB : ∀ᵐ y, ‖f y‖ ≤ B)
    (t : ℝ) (ht : 0 < t) (x : Euclidean d) :
    ‖convolve (dilate t ψ.val) f x‖ ≤
      B * volume.real (Metric.ball (0 : Euclidean d) 1) := by
  have hbi : 0 ≤ B := by
    obtain ⟨y, hy⟩ := hB.exists
    exact (norm_nonneg _).trans hy
  have hi := convolve_integrable ψ hf t ht x
  have hu := (dilate_integrable ψ t ht).norm.comp_sub_left x
  rw [convolve, convolution_mul_swap]
  calc
    ‖∫ y, dilate t ψ.val (x - y) * f y‖ ≤ ∫ y, ‖dilate t ψ.val (x - y) * f y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, B * ‖dilate t ψ.val (x - y)‖ := by
      apply integral_mono_ae hi.norm (hu.const_mul B)
      filter_upwards [hB] with y hy
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
    _ = B * ∫ y, ‖dilate t ψ.val y‖ := by
      rw [integral_const_mul, integral_sub_left_eq_self (fun y => ‖dilate t ψ.val y‖) volume x]
    _ ≤ B * volume.real (Metric.ball (0 : Euclidean d) 1) := by
      rw [dilate_norm_integral ψ t ht]
      exact mul_le_mul_of_nonneg_left (test_integral_bound ψ) hbi

lemma dilate_difference (hN : 1 ≤ N) (ψ : Tests 𝕜 d N)
    (t : ℝ) (ht : 0 < t) (x y : Euclidean d) :
    ‖dilate t ψ.val x - dilate t ψ.val y‖ ≤
      (d : ℝ) * ‖x - y‖ / t ^ (d + 1) := by
  rw [dilate, dilate, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (t ^ d)⁻¹)]
  calc
    (t ^ d)⁻¹ * ‖ψ.val (t⁻¹ • x) - ψ.val (t⁻¹ • y)‖ ≤
        (t ^ d)⁻¹ * ((d : ℝ) * ‖t⁻¹ • x - t⁻¹ • y‖) :=
      mul_le_mul_of_nonneg_left (test_lipschitz hN ψ _ _) (by positivity)
    _ = _ := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ t⁻¹), pow_succ]
      field_simp

lemma dilate_zero (ψ : Tests 𝕜 d N) (t : ℝ) (ht : 0 < t)
    {x : Euclidean d} (hx : t ≤ ‖x‖) : dilate t ψ.val x = 0 := by
  have h : 1 ≤ ‖t⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ t⁻¹), inv_mul_eq_div]
    exact (le_div_iff₀ ht).mpr (by simpa using hx)
  simp only [dilate, test_zero_of_norm ψ h, smul_zero]

lemma compact_difference (hN : 1 ≤ N) (ψ : Tests 𝕜 d N)
    (t : ℝ) (ht : 0 < t) (x y c : Euclidean d) {R : ℝ}
    (hR : 0 < R) (hx : 2 * R < ‖x - c‖) (hy : ‖y - c‖ ≤ R) :
    ‖dilate t ψ.val (x - y) - dilate t ψ.val (x - c)‖ ≤
      ((d : ℝ) * 2 ^ (d + 1)) * R / ‖x - c‖ ^ (d + 1) := by
  have hD : 0 < ‖x - c‖ := by linarith
  by_cases hs : t ≤ ‖x - c‖ / 2
  · have hxy : t ≤ ‖x - y‖ := by
      have htri : ‖x - c‖ ≤ ‖x - y‖ + ‖y - c‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (x - y) (y - c)
      linarith
    rw [dilate_zero ψ t ht hxy, dilate_zero ψ t ht (by linarith), sub_self, norm_zero]
    positivity
  · have hd := dilate_difference hN ψ t ht (x - y) (x - c)
    have heq : ‖(x - y) - (x - c)‖ = ‖y - c‖ := by
      rw [show (x - y) - (x - c) = -(y - c) by abel, norm_neg]
    rw [heq] at hd
    calc
      ‖dilate t ψ.val (x - y) - dilate t ψ.val (x - c)‖ ≤
          (d : ℝ) * ‖y - c‖ / t ^ (d + 1) := hd
      _ ≤ (d : ℝ) * R / (‖x - c‖ / 2) ^ (d + 1) := by
        apply div_le_div₀ (by positivity) (by gcongr) (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by rw [div_pow]; field_simp

lemma atom_convolve_tail (hN : 1 ≤ N) (ψ : Tests 𝕜 d N)
    (a : AtomValue (𝕜 := 𝕜) (volume : Measure (Euclidean d)))
    (c : Euclidean d) (R : ℝ) (hR : 0 < R)
    (hs : ∀ᵐ y, y ∉ Metric.ball c R → a.val y = 0)
    (t : ℝ) (ht : 0 < t) (x : Euclidean d) (hx : 2 * R < ‖x - c‖) :
    ‖convolve (dilate t ψ.val) a.val x‖ ≤
      ((d : ℝ) * 2 ^ (d + 1)) * R / ‖x - c‖ ^ (d + 1) := by
  let K := ((d : ℝ) * 2 ^ (d + 1)) * R / ‖x - c‖ ^ (d + 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ha := MeasureTheory.L1.integrable_coeFn a.val
  have hi := convolve_integrable ψ ha t ht x
  have hj : Integrable (fun y => (dilate t ψ.val (x - y) - dilate t ψ.val (x - c)) * a.val y) := by
    convert hi.sub (ha.const_mul (dilate t ψ.val (x - c))) using 1
    ext y
    exact sub_mul _ _ _
  have heq : convolve (dilate t ψ.val) a.val x =
      ∫ y, (dilate t ψ.val (x - y) - dilate t ψ.val (x - c)) * a.val y := by
    rw [convolve, convolution_mul_swap]
    simp only [sub_mul]
    rw [integral_sub hi (ha.const_mul _), integral_const_mul, a.property.1, mul_zero, sub_zero]
  rw [heq]
  calc
    ‖∫ y, (dilate t ψ.val (x - y) - dilate t ψ.val (x - c)) * a.val y‖ ≤
        ∫ y, ‖(dilate t ψ.val (x - y) - dilate t ψ.val (x - c)) * a.val y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, K * ‖a.val y‖ := by
      apply integral_mono_ae hj.norm (ha.norm.const_mul K)
      filter_upwards [hs] with y hy
      by_cases hyB : y ∈ Metric.ball c R
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (compact_difference hN ψ t ht x y c hR hx
            (le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hyB))) (norm_nonneg _)
      · simp [hy hyB]
    _ = K * ‖a.val‖ := by rw [integral_const_mul, MeasureTheory.L1.norm_eq_integral_norm]
    _ ≤ K := mul_le_of_le_one_right hK (ExpandedFA.Hardy.AtomicHardySpace.atom_norm_le volume a)

lemma grand_atom_pointwise (hN : 1 ≤ N)
    (a : AtomValue (𝕜 := 𝕜) (volume : Measure (Euclidean d))) :
    ∃ (c : Euclidean d) (R : ℝ), 0 < R ∧
      (∀ x, grand N (a.val : Euclidean d → 𝕜) x ≤
        ENNReal.ofReal ((volume.real (Metric.ball c R))⁻¹ *
          volume.real (Metric.ball (0 : Euclidean d) 1))) ∧
      (∀ x, 2 * R < ‖x - c‖ → grand N (a.val : Euclidean d → 𝕜) x ≤
        ENNReal.ofReal (((d : ℝ) * 2 ^ (d + 1)) * R / ‖x - c‖ ^ (d + 1))) := by
  obtain ⟨c, R, hR, _, _, hb⟩ := a.property.2
  refine ⟨c, R, hR, ?_, ?_⟩
  · intro x
    apply iSup_le
    intro t
    apply iSup_le
    intro ψ
    exact ENNReal.ofReal_le_ofReal (convolve_bound_of_ae_bound ψ
      (MeasureTheory.L1.integrable_coeFn a.val) (hb.mono fun y hy => hy.2) t.val t.property x)
  · intro x hx
    apply iSup_le
    intro t
    apply iSup_le
    intro ψ
    exact ENNReal.ofReal_le_ofReal (atom_convolve_tail hN ψ a c R hR
      (hb.mono fun y hy => hy.1) t.val t.property x hx)


/-- An explicit (nonoptimal) constant, independent of scalar field and order. -/
def atomConstant (d : ℕ) : ℝ :=
  (2 : ℝ) ^ d * volume.real (Metric.ball (0 : Euclidean d) 1) +
    ((d : ℝ) * 2 ^ (d + 1)) * (d : ℝ) * volume.real (Metric.ball (0 : Euclidean d) 1) / 2

lemma atomConstant_nonneg (d : ℕ) : 0 ≤ atomConstant d := by
  unfold atomConstant
  positivity

lemma atom_lintegral_bound (hd : 0 < d) (hN : 1 ≤ N)
    (a : AtomValue (𝕜 := 𝕜) (volume : Measure (Euclidean d))) :
    (∫⁻ x, grand N (a.val : Euclidean d → 𝕜) x) ≤ ENNReal.ofReal (atomConstant d) := by
  obtain ⟨c, R, hR, hlocal, htail⟩ := grand_atom_pointwise hN a
  let V := volume.real (Metric.ball c R)
  let v := volume.real (Metric.ball (0 : Euclidean d) 1)
  let A := (d : ℝ) * 2 ^ (d + 1)
  let B := Metric.closedBall c (2 * R)
  let w : Euclidean d → ℝ := fun x =>
    (Ioi (2 * R)).indicator (fun r : ℝ => 1 / r ^ (d + 1)) ‖x - c‖
  let g : Euclidean d → ℝ := fun x => B.indicator (fun _ => V⁻¹ * v) x + A * R * w x
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hR).ne' measure_ball_ne_top
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hv : 0 ≤ v := measureReal_nonneg
  have hw (x : Euclidean d) : 0 ≤ w x := by
    apply Set.indicator_nonneg _ _
    intro r hr
    have : 0 < r := lt_trans (by positivity : 0 < 2 * R) hr
    positivity
  obtain ⟨hwi, hwe⟩ := ExpandedFA.SingularIntegrals.CZWeak.radial_tail hd (2 * R) (by positivity)
  have hwi' : Integrable w := hwi.comp_sub_right c
  have hwe' : (∫ x, w x) = (d : ℝ) * v / (2 * R) := by
    exact (integral_sub_right_eq_self (fun z : Euclidean d =>
      (Ioi (2 * R)).indicator (fun r : ℝ => 1 / r ^ (d + 1)) ‖z‖) c).trans hwe
  have hci : Integrable (B.indicator (fun _ => V⁻¹ * v)) :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator Metric.isClosed_closedBall.measurableSet
  have hgi : Integrable g := hci.add (hwi'.const_mul (A * R))
  have hg (x : Euclidean d) : 0 ≤ g x := by
    exact add_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) x)
      (mul_nonneg (mul_nonneg hA hR.le) (hw x))
  have hpoint (x : Euclidean d) : grand N (a.val : Euclidean d → 𝕜) x ≤ ENNReal.ofReal (g x) := by
    by_cases hx : x ∈ B
    · apply (hlocal x).trans
      apply ENNReal.ofReal_le_ofReal
      dsimp [g]
      rw [Set.indicator_of_mem hx]
      exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hA hR.le) (hw x))
    · have hx' : 2 * R < ‖x - c‖ := by
        simpa only [B, Metric.mem_closedBall, dist_eq_norm, not_le] using hx
      apply (htail x hx').trans_eq
      congr 1
      dsimp [g, w]
      rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (show ‖x - c‖ ∈ Ioi (2 * R) from hx')]
      dsimp [A]
      ring
  calc
    (∫⁻ x, grand N (a.val : Euclidean d → 𝕜) x) ≤ ∫⁻ x, ENNReal.ofReal (g x) := lintegral_mono hpoint
    _ = ENNReal.ofReal (∫ x, g x) :=
      (ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg)).symm
    _ = ENNReal.ofReal (atomConstant d) := by
      congr 1
      rw [integral_add hci (hwi'.const_mul (A * R)), integral_indicator_const _ Metric.isClosed_closedBall.measurableSet,
        integral_const_mul, hwe', ExpandedFA.Hardy.HardyCZEndpoint.doubled_ball_volume c R hR]
      change (2 ^ d * V) • (V⁻¹ * v) + A * R * ((d : ℝ) * v / (2 * R)) = atomConstant d
      simp only [smul_eq_mul]
      dsimp [atomConstant, A, v]
      field_simp [hV.ne', hR.ne']

theorem atom_estimate : HardyGrandForwardSpec.AtomEstimate := by
  intro d N hd hN
  refine ⟨Real.toNNReal (atomConstant d), ?_⟩
  intro 𝕜 _ a
  have h1 : 1 ≤ N := by dsimp [AdmissibleOrder, peetreExponent] at hN; omega
  change (∫⁻ x, grand N (a.val : Euclidean d → 𝕜) x) ≤ ENNReal.ofReal (atomConstant d)
  exact atom_lintegral_bound hd h1 a

lemma convolve_evaluation_bound (ψ : Tests 𝕜 d N)
    (t : ℝ) (ht : 0 < t) (x : Euclidean d) (f : L1 𝕜 d) :
    ‖convolve (dilate t ψ.val) f x‖ ≤ (t ^ d)⁻¹ * ‖f‖ := by
  have hf := MeasureTheory.L1.integrable_coeFn f
  rw [convolve, convolution_mul_swap]
  calc
    ‖∫ y, dilate t ψ.val (x - y) * f y‖ ≤ ∫ y, ‖dilate t ψ.val (x - y) * f y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, (t ^ d)⁻¹ * ‖f y‖ := by
      apply integral_mono (convolve_integrable ψ hf t ht x).norm (hf.norm.const_mul _)
      intro y
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (dilate_bound ψ t ht _) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul, MeasureTheory.L1.norm_eq_integral_norm]

/-- Each fixed test and scale is a continuous linear functional on the genuine
L¹ quotient. This permits passing an atomic series through convolution. -/
def convolutionEvaluation (ψ : Tests 𝕜 d N) (t : Scale) (x : Euclidean d) :
    L1 𝕜 d →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous {
    toFun := fun f => convolve (dilate t.val ψ.val) f x
    map_add' := by
      intro f g
      rw [convolve, convolve, convolve, convolution_mul_swap, convolution_mul_swap, convolution_mul_swap]
      calc
        (∫ y, dilate t.val ψ.val (x - y) * (f + g) y) =
            ∫ y, (dilate t.val ψ.val (x - y) * f y + dilate t.val ψ.val (x - y) * g y) := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_add f g] with y hy
          simp only [hy, Pi.add_apply, mul_add]
        _ = _ := integral_add
          (convolve_integrable ψ (MeasureTheory.L1.integrable_coeFn f) t.val t.property x)
          (convolve_integrable ψ (MeasureTheory.L1.integrable_coeFn g) t.val t.property x)
    map_smul' := by
      intro k f
      simp only [RingHom.id_apply]
      rw [convolve, convolve, convolution_mul_swap, convolution_mul_swap, ← integral_smul]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul k f] with y hy
      rw [hy]
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
  } ((t.val ^ d)⁻¹) (fun f => convolve_evaluation_bound ψ t.val t.property x f)

lemma grand_series_le (a : ℕ → AtomValue (𝕜 := 𝕜) (volume : Measure (Euclidean d)))
    (b : ℕ → 𝕜) (f : L1 𝕜 d) (hf : HasSum (fun j => b j • (a j).val) f)
    (x : Euclidean d) :
    grand N (f : Euclidean d → 𝕜) x ≤
      ∑' j, ENNReal.ofReal ‖b j‖ * grand N ((a j).val : Euclidean d → 𝕜) x := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ψ
  have hs := (convolutionEvaluation ψ t x).hasSum hf
  change HasSum (fun j => convolutionEvaluation ψ t x (b j • (a j).val))
    (convolutionEvaluation ψ t x f) at hs
  simp only [map_smul] at hs
  rw [ofReal_norm]
  apply hs.enorm_le_of_bounded ENNReal.summable.hasSum
  intro j
  rw [enorm_smul, ← ofReal_norm, ← ofReal_norm]
  apply mul_le_mul_right
  change ENNReal.ofReal ‖convolve (dilate t.val ψ.val) (a j).val x‖ ≤
    grand N ((a j).val : Euclidean d → 𝕜) x
  exact le_iSup_of_le t (le_iSup_of_le ψ le_rfl)

lemma series_lintegral_bound (hd : 0 < d) (hN : 1 ≤ N)
    (a : ℕ → AtomValue (𝕜 := 𝕜) (volume : Measure (Euclidean d)))
    (b : ℕ → 𝕜) (hb : Summable (fun j => ‖b j‖))
    (f : L1 𝕜 d) (hf : HasSum (fun j => b j • (a j).val) f) :
    (∫⁻ x, grand N (f : Euclidean d → 𝕜) x) ≤
      ENNReal.ofReal (atomConstant d * ∑' j, ‖b j‖) := by
  have hm (j : ℕ) : Measurable (grand N ((a j).val : Euclidean d → 𝕜)) :=
    (HardyMaximal.grand_regularity N _ (MeasureTheory.L1.integrable_coeFn (a j).val)).2
  calc
    (∫⁻ x, grand N (f : Euclidean d → 𝕜) x) ≤
        ∫⁻ x, ∑' j, ENNReal.ofReal ‖b j‖ * grand N ((a j).val : Euclidean d → 𝕜) x :=
      lintegral_mono (grand_series_le a b f hf)
    _ = ∑' j, ENNReal.ofReal ‖b j‖ * ∫⁻ x, grand N ((a j).val : Euclidean d → 𝕜) x := by
      rw [lintegral_tsum (f := fun j x => ENNReal.ofReal ‖b j‖ *
        grand N ((a j).val : Euclidean d → 𝕜) x)
        (fun j => (measurable_const.mul (hm j)).aemeasurable)]
      congr 1
      funext j
      exact lintegral_const_mul _ (hm j)
    _ ≤ ∑' j, ENNReal.ofReal ‖b j‖ * ENNReal.ofReal (atomConstant d) := by
      apply ENNReal.tsum_le_tsum
      intro j
      exact mul_le_mul_right (atom_lintegral_bound hd hN (a j)) _
    _ = ENNReal.ofReal (atomConstant d * ∑' j, ‖b j‖) := by
      rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg (b j)) hb,
        ← ENNReal.ofReal_mul (tsum_nonneg (fun j => norm_nonneg (b j))), mul_comm]

lemma synthesis_lintegral_bound (hd : 0 < d) (hN : 1 ≤ N)
    (c : CoefficientsValue (𝕜 := 𝕜) (volume : Measure (Euclidean d))) :
    (∫⁻ x, grand N (SynthesisValue volume c : Euclidean d → 𝕜) x) ≤
      ENNReal.ofReal (atomConstant d * ‖c‖) := by
  have := ExpandedFA.Hardy.AtomicHardySpace.euclidean_atoms_nonempty d 𝕜
  obtain ⟨a, b, hb, hf⟩ := ExpandedFA.Hardy.AtomicHardySpace.coefficient_sequence volume c
  simpa only [hb.tsum_eq] using series_lintegral_bound hd hN a b hb.summable _ hf

lemma hardy_lintegral_bound (hd : 0 < d) (hN : 1 ≤ N) (h : Hardy 𝕜 d) :
    (∫⁻ x, grand N (EmbeddingValue volume h : Euclidean d → 𝕜) x) ≤
      ENNReal.ofReal (atomConstant d * ‖h‖) := by
  let I := ∫⁻ x, grand N (EmbeddingValue volume h : Euclidean d → 𝕜) x
  let C := atomConstant d
  have hC : 0 ≤ C := atomConstant_nonneg d
  have hb (c : CoefficientsValue (𝕜 := 𝕜) (volume : Measure (Euclidean d)))
      (hc : (KernelValue volume).mkQ c = h) : I ≤ ENNReal.ofReal (C * ‖c‖) := by
    have he : SynthesisValue volume c = EmbeddingValue volume h :=
      congrArg (EmbeddingValue volume) hc
    simpa only [he] using synthesis_lintegral_bound hd hN c
  obtain ⟨c₀, hc₀⟩ := (KernelValue (𝕜 := 𝕜) (volume : Measure (Euclidean d))).mkQ_surjective h
  have hIfin : I ≠ (∞ : ℝ≥0∞) := (lt_of_le_of_lt (hb c₀ hc₀) ENNReal.ofReal_lt_top).ne
  apply (ENNReal.le_ofReal_iff_toReal_le hIfin (mul_nonneg hC (norm_nonneg h))).mpr
  apply le_of_forall_pos_le_add
  intro ε hε
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  obtain ⟨c, hc, hcn⟩ := Submodule.Quotient.norm_mk_lt h hδ
  have hi : I.toReal ≤ C * ‖c‖ :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC (norm_nonneg _)) (hb c hc)
  calc
    I.toReal ≤ C * ‖c‖ := hi
    _ ≤ C * (‖h‖ + ε / (C + 1)) := mul_le_mul_of_nonneg_left hcn.le hC
    _ ≤ C * ‖h‖ + ε := by
      have hsmall : C * (ε / (C + 1)) ≤ ε := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by linarith : 0 < C + 1)).mpr
        nlinarith
      nlinarith

theorem forward : HardyGrandForwardSpec.Forward := by
  intro d N hd hN
  refine ⟨Real.toNNReal (atomConstant d), ?_⟩
  intro 𝕜 _ h
  have h1 : 1 ≤ N := by dsimp [AdmissibleOrder, peetreExponent] at hN; omega
  change (∫⁻ x, grand N (EmbeddingValue volume h : Euclidean d → 𝕜) x) ≤
    ENNReal.ofReal (atomConstant d) * ENNReal.ofReal ‖h‖
  rw [← ENNReal.ofReal_mul (atomConstant_nonneg d)]
  exact hardy_lintegral_bound hd h1 h

end ExpandedFA.PartIV.HardyGrandForward
