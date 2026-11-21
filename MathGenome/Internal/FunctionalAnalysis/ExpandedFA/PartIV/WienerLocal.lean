import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.WienerLocal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Filter
open scoped Topology FourierTransform ContDiff

namespace ExpandedFA.PartIV.WienerLocal
open ExpandedFA.Fourier

variable {d : ℕ}
abbrev L1 (d : ℕ) := MeasureTheory.Lp ℂ 1 (volume : Measure (Euclidean d))

/-- The character in the Fourier integral, with the manuscript's sign. -/
def phase (ξ x : Euclidean d) : ℂ := Real.fourierChar (-inner ℝ x ξ)

@[simp] lemma norm_phase (ξ x : Euclidean d) : ‖phase ξ x‖ = 1 := by
  exact Circle.norm_coe _

lemma continuous_phase (ξ : Euclidean d) : Continuous (phase ξ) := by
  unfold phase
  fun_prop


lemma phase_add (ξ η x : Euclidean d) : phase (ξ + η) x = phase ξ x * phase η x := by
  simp [phase, inner_add_right, AddChar.map_add_eq_mul, mul_comm]

lemma phase_smul (t : ℝ) (ξ x : Euclidean d) : phase ξ (t • x) = phase (t • ξ) x := by
  simp [phase, inner_smul_left, inner_smul_right]

lemma fourier_eq (f : Euclidean d → ℂ) (ξ : Euclidean d) :
    𝓕 f ξ = ∫ x, phase ξ x * f x := by
  simp [Real.fourier_eq, phase, Circle.smul_def, smul_eq_mul]

def translate (y : Euclidean d) (g : L1 d) : L1 d :=
  Lp.compMeasurePreserving (fun x => x - y) (measurePreserving_sub_right volume y) g

lemma translate_coe (y : Euclidean d) (g : L1 d) :
    ⇑(translate y g) =ᵐ[volume] fun x => g (x - y) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_sub_right volume y)

@[simp] lemma translate_zero (g : L1 d) : translate 0 g = g := by
  apply Lp.ext
  filter_upwards [translate_coe 0 g] with x hx
  simpa using hx

@[simp] lemma norm_translate (y : Euclidean d) (g : L1 d) : ‖translate y g‖ = ‖g‖ := by
  exact Lp.norm_compMeasurePreserving _ _

lemma continuous_translate (g : L1 d) : Continuous (fun y => translate y g) := by
  let q : Euclidean d → C(Euclidean d, Euclidean d) :=
    fun y => ⟨fun x => x - y, continuous_id.sub continuous_const⟩
  have hq : Continuous q := ContinuousMap.continuous_of_continuous_uncurry q
    (continuous_snd.sub continuous_fst)
  exact continuous_const.compMeasurePreservingLp hq
    (fun y => measurePreserving_sub_right volume y) (by norm_num)

/-- Fourier evaluation is a bounded linear functional on the genuine L¹ space. -/
def evaluation (ξ : Euclidean d) : L1 d →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ ξ).comp (Real.Lp.fourierTransformCLM (Euclidean d) ℂ)

@[simp] lemma evaluation_apply (ξ : Euclidean d) (g : L1 d) :
    evaluation ξ g = 𝓕 (g : Euclidean d → ℂ) ξ := rfl

lemma evaluation_translate (ξ y : Euclidean d) (g : L1 d) :
    evaluation ξ (translate y g) = phase ξ y * evaluation ξ g := by
  rw [evaluation_apply, Real.fourier_congr_ae (translate_coe y g)]
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ (Euclidean d)) (g : Euclidean d → ℂ) (-y)) ξ
  simpa [Real.fourier_eq, VectorFourier.fourierIntegral, Function.comp_def, phase,
    Circle.smul_def, smul_eq_mul, sub_eq_add_neg] using h

/-- The translation difference, integrated in L¹ rather than pointwise. -/
def difference (f : Euclidean d → ℂ) (ξ₀ : Euclidean d) (g : L1 d)
    (t : ℝ) (y : Euclidean d) : L1 d :=
  (f y * phase ξ₀ y) • (g - translate (t • y) g)

lemma difference_measurable {f : Euclidean d → ℂ} (hf : Integrable f)
    (ξ₀ : Euclidean d) (g : L1 d) (t : ℝ) :
    AEStronglyMeasurable (difference f ξ₀ g t) := by
  have hc : Continuous (fun y : Euclidean d => g - translate (t • y) g) :=
    continuous_const.sub ((continuous_translate g).comp (continuous_const_smul t))
  exact (hf.aestronglyMeasurable.mul (continuous_phase ξ₀).aestronglyMeasurable).smul
    hc.aestronglyMeasurable

lemma norm_difference_le (f : Euclidean d → ℂ) (ξ₀ : Euclidean d) (g : L1 d)
    (t : ℝ) (y : Euclidean d) :
    ‖difference f ξ₀ g t y‖ ≤ ‖f y‖ * (2 * ‖g‖) := by
  simp only [difference, norm_smul, norm_mul, norm_phase, mul_one]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖g - translate (t • y) g‖ ≤ ‖g‖ + ‖translate (t • y) g‖ := norm_sub_le _ _
    _ = 2 * ‖g‖ := by rw [norm_translate]; ring

lemma difference_integrable {f : Euclidean d → ℂ} (hf : Integrable f)
    (ξ₀ : Euclidean d) (g : L1 d) (t : ℝ) :
    Integrable (difference f ξ₀ g t) := by
  exact (hf.norm.mul_const (2 * ‖g‖)).mono'
    (difference_measurable hf ξ₀ g t) (.of_forall (norm_difference_le f ξ₀ g t))

/-- Wide-kernel corrections converge to zero in L¹. -/
lemma correction_tendsto_zero {f : Euclidean d → ℂ} (hf : Integrable f)
    (ξ₀ : Euclidean d) (g : L1 d) :
    Tendsto (fun t : ℝ => ∫ y, difference f ξ₀ g t y) (𝓝 0) (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (l := 𝓝 (0 : ℝ))
    (f := fun _ : Euclidean d => (0 : L1 d))
    (fun y => ‖f y‖ * (2 * ‖g‖))
    (.of_forall (difference_measurable hf ξ₀ g))
    (.of_forall (fun t => .of_forall (norm_difference_le f ξ₀ g t)))
    (hf.norm.mul_const (2 * ‖g‖)) ?_
  · simpa using h
  · exact .of_forall fun y => by
      have hy : Tendsto (fun t : ℝ => t • y) (𝓝 0) (𝓝 0) := by
        have hh : Continuous (fun t : ℝ => t • y) := by fun_prop
        have hh' := hh.tendsto (0 : ℝ)
        rw [zero_smul] at hh'
        exact hh'
      have ht : Tendsto (fun t : ℝ => translate (t • y) g) (𝓝 0) (𝓝 g) := by
        simpa only [Function.comp_def, translate_zero] using
          ((continuous_translate g).tendsto 0).comp hy
      simpa [difference] using
        ((tendsto_const_nhds (x := g)).sub ht).const_smul (f y * phase ξ₀ y)

lemma integrable_phase_mul {f : Euclidean d → ℂ} (hf : Integrable f) (ξ : Euclidean d) :
    Integrable (fun y => phase ξ y * f y) := by
  simpa [phase, Circle.smul_def, smul_eq_mul] using
    (Real.fourierIntegral_convergent_iff ξ).mpr hf

/-- The exact transform of the L¹-valued correction integral. -/
lemma evaluation_correction {f : Euclidean d → ℂ} (hf : Integrable f)
    (ξ₀ : Euclidean d) (g : L1 d) (t : ℝ) (η : Euclidean d) :
    evaluation η (∫ y, difference f ξ₀ g t y) =
      (𝓕 f ξ₀ - 𝓕 f (ξ₀ + t • η)) * evaluation η g := by
  rw [← (evaluation η).integral_comp_comm (difference_integrable hf ξ₀ g t)]
  calc
    (∫ y, evaluation η (difference f ξ₀ g t y)) =
        ∫ y, (phase ξ₀ y * f y - phase (ξ₀ + t • η) y * f y) * evaluation η g := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [difference, map_smul, map_sub, evaluation_translate, smul_eq_mul,
        phase_add, ← phase_smul]
      ring
    _ = _ := by
      rw [integral_mul_const, integral_sub (integrable_phase_mul hf ξ₀)
        (integrable_phase_mul hf (ξ₀ + t • η)), fourier_eq, fourier_eq]

/-- A frequency plateau with compact support, used to separate reflected frequencies. -/
lemma exists_supported_plateau_kernel (d : ℕ) :
    ∃ g : L1 d, (∀ᶠ η in 𝓝 (0 : Euclidean d), evaluation η g = 1) ∧
      ∀ η, 2 ≤ ‖η‖ → evaluation η g = 0 := by
  let b : ContDiffBump (0 : Euclidean d) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  have hc : HasCompactSupport (fun x => (b x : ℂ)) :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) rfl
  have hs : ContDiff ℝ ∞ (fun x => (b x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  let ψ : Schwartz ℂ d := hc.toSchwartzMap hs
  let g : Schwartz ℂ d := 𝓕⁻ ψ
  have heval (η : Euclidean d) : evaluation η (g.toLp 1) = (b η : ℂ) := by
    rw [evaluation_apply, Real.fourier_congr_ae (g.coeFn_toLp 1)]
    rw [← SchwartzMap.fourier_coe]
    change (𝓕 (𝓕⁻ ψ) : Schwartz ℂ d) η = (b η : ℂ)
    rw [FourierTransform.fourier_fourierInv_eq]
    rfl
  refine ⟨g.toLp 1, ?_, ?_⟩
  · filter_upwards [Metric.ball_mem_nhds (0 : Euclidean d)
      (by norm_num : (0 : ℝ) < 1)] with η hη
    rw [heval, b.one_of_mem_closedBall (Metric.ball_subset_closedBall hη)]
    rfl
  · intro η hη
    rw [heval, b.zero_of_le_dist (by simpa [b, dist_zero_right] using hη)]
    rfl

/-- An L¹ kernel whose Fourier transform is one on a neighborhood of zero. -/
lemma exists_plateau_kernel (d : ℕ) :
    ∃ g : L1 d, ∀ᶠ η in 𝓝 (0 : Euclidean d), evaluation η g = 1 := by
  obtain ⟨g, hg, _⟩ := exists_supported_plateau_kernel d
  exact ⟨g, hg⟩

/-- L¹-normalized dilation and modulation back to the chosen frequency. -/
def rescaleModulate (t : ℝ) (ξ₀ : Euclidean d) (H : L1 d) (x : Euclidean d) : ℂ :=
  (t ^ d) • (phase (-ξ₀) x * H (t • x))

lemma rescaleModulate_integrable {t : ℝ} (ht : 0 < t) (ξ₀ : Euclidean d) (H : L1 d) :
    Integrable (rescaleModulate t ξ₀ H) := by
  exact (integrable_phase_mul ((MeasureTheory.L1.integrable_coeFn H).comp_smul ht.ne')
    (-ξ₀)).smul (t ^ d)

lemma rescaleModulate_norm {t : ℝ} (ht : 0 < t) (ξ₀ : Euclidean d) (H : L1 d) :
    (∫ x, ‖rescaleModulate t ξ₀ H x‖) = ‖H‖ := by
  simp only [rescaleModulate, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg ht.le d), norm_mul, norm_phase, one_mul]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume
    (fun x : Euclidean d => ‖H x‖) t (hR := ht.le)]
  simp only [Euclidean, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d ht.ne'), one_mul]
  exact (MeasureTheory.L1.norm_eq_integral_norm H).symm

lemma fourier_rescaleModulate {t : ℝ} (ht : 0 < t) (ξ₀ : Euclidean d)
    (H : L1 d) (ξ : Euclidean d) :
    𝓕 (rescaleModulate t ξ₀ H) ξ = evaluation (t⁻¹ • (ξ - ξ₀)) H := by
  have hcancel : t • (t⁻¹ • (ξ - ξ₀)) = ξ - ξ₀ := by
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  calc
    𝓕 (rescaleModulate t ξ₀ H) ξ =
        (t ^ d) • ∫ x, phase (ξ - ξ₀) x * H (t • x) := by
      rw [fourier_eq, ← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [rescaleModulate, mul_smul_comm, ← mul_assoc, ← phase_add, sub_eq_add_neg]
    _ = (t ^ d) • ∫ x, phase (t⁻¹ • (ξ - ξ₀)) (t • x) * H (t • x) := by
      simp only [phase_smul, hcancel]
    _ = (t ^ d) • ((t ^ d)⁻¹ •
        ∫ x, phase (t⁻¹ • (ξ - ξ₀)) x * H x) := by
      rw [Measure.integral_comp_smul_of_nonneg volume
        (fun x : Euclidean d => phase (t⁻¹ • (ξ - ξ₀)) x * H x) t (hR := ht.le)]
      simp [Euclidean]
    _ = evaluation (t⁻¹ • (ξ - ξ₀)) H := by
      rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero d ht.ne'), one_smul,
        evaluation_apply, fourier_eq]

/-- Local Fourier flattening, including the zero-dimensional case. -/
theorem local_flattening : Specs.ExpandedFA.PartIV.WienerLocal.LocalFlattening := by
  intro d f hf ξ₀ ε hε
  obtain ⟨g, hg⟩ := exists_plateau_kernel d
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ‖∫ y, difference f ξ₀ g t y‖ < ε := by
    have hn := (correction_tendsto_zero hf ξ₀ g).norm
    exact (show Tendsto (fun t : ℝ => ‖∫ y, difference f ξ₀ g t y‖)
      (𝓝 0) (𝓝 0) by simpa using hn).eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hδsmall⟩ := Metric.eventually_nhds_iff.mp hsmall
  let t : ℝ := δ / 2
  have ht : 0 < t := half_pos hδ
  have htδ : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    exact half_lt_self hδ
  let H : L1 d := ∫ y, difference f ξ₀ g t y
  refine ⟨rescaleModulate t ξ₀ H, rescaleModulate_integrable ht ξ₀ H, ?_, ?_⟩
  · rw [rescaleModulate_norm ht]
    exact hδsmall htδ
  · have hη : Tendsto (fun ξ : Euclidean d => t⁻¹ • (ξ - ξ₀)) (𝓝 ξ₀) (𝓝 0) := by
      have hc : Continuous (fun ξ : Euclidean d => t⁻¹ • (ξ - ξ₀)) := by fun_prop
      simpa using hc.tendsto ξ₀
    filter_upwards [hη.eventually hg] with ξ hξ
    rw [integralFourier_eq_native, fourier_rescaleModulate ht]
    change evaluation (t⁻¹ • (ξ - ξ₀)) (∫ y, difference f ξ₀ g t y) = _
    rw [evaluation_correction hf, hξ, mul_one]
    have hfreq : ξ₀ + t • (t⁻¹ • (ξ - ξ₀)) = ξ := by
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul, add_sub_cancel]
    rw [hfreq, integralFourier_eq_native, integralFourier_eq_native]

/-- Flattening can be localized away from any distinct prescribed frequency. -/
lemma local_flattening_away (f : Euclidean d → ℂ) (hf : Integrable f)
    (ξ₀ η₀ : Euclidean d) (hne : η₀ ≠ ξ₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : Euclidean d → ℂ, Integrable h ∧ (∫ x, ‖h x‖) < ε ∧
      (∀ᶠ ξ in 𝓝 ξ₀, 𝓕 h ξ = 𝓕 f ξ₀ - 𝓕 f ξ) ∧
      (∀ᶠ η in 𝓝 η₀, 𝓕 h η = 0) := by
  obtain ⟨g, hg, hgsupp⟩ := exists_supported_plateau_kernel d
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ‖∫ y, difference f ξ₀ g t y‖ < ε := by
    have hn := (correction_tendsto_zero hf ξ₀ g).norm
    exact (show Tendsto (fun t : ℝ => ‖∫ y, difference f ξ₀ g t y‖)
      (𝓝 0) (𝓝 0) by simpa using hn).eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hδsmall⟩ := Metric.eventually_nhds_iff.mp hsmall
  have hdist : 0 < ‖η₀ - ξ₀‖ := norm_sub_pos_iff.mpr hne
  let t : ℝ := min (δ / 2) (‖η₀ - ξ₀‖ / 4)
  have ht : 0 < t := lt_min (half_pos hδ) (by linarith)
  have htδ : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have htsep : 2 < ‖t⁻¹ • (η₀ - ξ₀)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    apply (lt_inv_mul_iff₀ ht).mpr
    have := min_le_right (δ / 2) (‖η₀ - ξ₀‖ / 4)
    change t ≤ ‖η₀ - ξ₀‖ / 4 at this
    linarith
  let H : L1 d := ∫ y, difference f ξ₀ g t y
  refine ⟨rescaleModulate t ξ₀ H, rescaleModulate_integrable ht ξ₀ H, ?_, ?_, ?_⟩
  · rw [rescaleModulate_norm ht]
    exact hδsmall htδ
  · have hη : Tendsto (fun ξ : Euclidean d => t⁻¹ • (ξ - ξ₀)) (𝓝 ξ₀) (𝓝 0) := by
      have hc : Continuous (fun ξ : Euclidean d => t⁻¹ • (ξ - ξ₀)) := by fun_prop
      simpa using hc.tendsto ξ₀
    filter_upwards [hη.eventually hg] with ξ hξ
    rw [fourier_rescaleModulate ht]
    change evaluation (t⁻¹ • (ξ - ξ₀)) (∫ y, difference f ξ₀ g t y) = _
    rw [evaluation_correction hf, hξ, mul_one]
    have hfreq : ξ₀ + t • (t⁻¹ • (ξ - ξ₀)) = ξ := by
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul, add_sub_cancel]
    rw [hfreq]
  · have hc : Continuous (fun η : Euclidean d => ‖t⁻¹ • (η - ξ₀)‖) := by fun_prop
    filter_upwards [(hc.tendsto η₀).eventually (lt_mem_nhds htsep)] with η hη
    rw [fourier_rescaleModulate ht]
    change evaluation (t⁻¹ • (η - ξ₀)) (∫ y, difference f ξ₀ g t y) = _
    rw [evaluation_correction hf, hgsupp _ hη.le, mul_zero]

open scoped ComplexConjugate

lemma phase_neg (ξ x : Euclidean d) : phase (-ξ) x = conj (phase ξ x) := by
  simp [phase, inner_neg_right, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]

/-- Complex conjugation reflects frequency in the ordinary integral transform. -/
lemma fourier_conj (f : Euclidean d → ℂ) (ξ : Euclidean d) :
    𝓕 (fun x => conj (f x)) ξ = conj (𝓕 f (-ξ)) := by
  rw [fourier_eq, fourier_eq, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [map_mul, phase_neg]

lemma fourier_real_symmetry (f : Euclidean d → ℝ) (ξ : Euclidean d) :
    conj (𝓕 (fun x => (f x : ℂ)) (-ξ)) = 𝓕 (fun x => (f x : ℂ)) ξ := by
  rw [← fourier_conj]
  simp only [Complex.conj_ofReal]

/-- Taking real parts averages the transform with its conjugate reflection. -/
lemma fourier_re (h : Euclidean d → ℂ) (hh : Integrable h) (ξ : Euclidean d) :
    𝓕 (fun x => ((h x).re : ℂ)) ξ =
      (𝓕 h ξ + conj (𝓕 h (-ξ))) / 2 := by
  have hconj : Integrable (fun x => conj (h x)) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hh
  calc
    𝓕 (fun x => ((h x).re : ℂ)) ξ =
        ((∫ x, phase ξ x * h x) + (∫ x, phase ξ x * conj (h x))) / 2 := by
      rw [fourier_eq, ← integral_add (integrable_phase_mul hh ξ)
        (integrable_phase_mul hconj ξ), ← integral_div]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← mul_add, Complex.add_conj]
      push_cast
      ring
    _ = _ := by rw [← fourier_eq, ← fourier_eq, fourier_conj]

lemma integral_norm_re_le (h : Euclidean d → ℂ) (hh : Integrable h) :
    (∫ x, ‖(h x).re‖) ≤ ∫ x, ‖h x‖ := by
  apply integral_mono hh.re.norm hh.norm
  intro x
  exact Complex.abs_re_le_norm (h x)

lemma fourier_const_mul (c : ℂ) (h : Euclidean d → ℂ) (ξ : Euclidean d) :
    𝓕 (fun x => c * h x) ξ = c * 𝓕 h ξ := by
  rw [fourier_eq, fourier_eq, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- Real flattening uses conjugate reflection, with separate treatment of zero frequency. -/
theorem real_local_flattening : Specs.ExpandedFA.PartIV.WienerLocal.RealLocalFlattening := by
  intro d f hf ξ₀ ε hε
  let fc : Euclidean d → ℂ := fun x => (f x : ℂ)
  have hfc : Integrable fc := hf.ofReal
  by_cases hzero : ξ₀ = 0
  · subst ξ₀
    obtain ⟨h, hh, hnorm, hflat⟩ := local_flattening d fc hfc 0 ε hε
    simp only [integralFourier_eq_native] at hflat
    refine ⟨fun x => (h x).re, hh.re,
      lt_of_le_of_lt (integral_norm_re_le h hh) hnorm, ?_⟩
    have hreflect : ∀ᶠ ξ in 𝓝 (0 : Euclidean d),
        𝓕 h (-ξ) = 𝓕 fc 0 - 𝓕 fc (-ξ) := by
      have ht : Tendsto (fun ξ : Euclidean d => -ξ) (𝓝 0) (𝓝 0) := by
        simpa using continuous_neg.tendsto (0 : Euclidean d)
      exact ht.eventually hflat
    have hreal0 : conj (𝓕 fc 0) = 𝓕 fc 0 := by
      simpa [fc] using fourier_real_symmetry f (0 : Euclidean d)
    filter_upwards [hflat, hreflect] with ξ hξ hneg
    simp only [integralFourier_eq_native]
    rw [fourier_re h hh, hξ, hneg, map_sub, hreal0,
      show conj (𝓕 fc (-ξ)) = 𝓕 fc ξ from fourier_real_symmetry f ξ]
    change (𝓕 fc 0 - 𝓕 fc ξ + (𝓕 fc 0 - 𝓕 fc ξ)) / 2 = _
    ring
  · have hne : -ξ₀ ≠ ξ₀ := by
      intro he
      apply hzero
      have he' : ξ₀ + ξ₀ = 0 := by
        calc ξ₀ + ξ₀ = -ξ₀ + ξ₀ := congrArg (fun z => z + ξ₀) he.symm
             _ = 0 := neg_add_cancel ξ₀
      have he'' : (2 : ℝ) • ξ₀ = 0 := by simpa [two_smul] using he'
      exact (smul_eq_zero.mp he'').resolve_left (by norm_num)
    obtain ⟨h, hh, hnorm, hflat, haway⟩ :=
      local_flattening_away fc hfc ξ₀ (-ξ₀) hne (ε / 2) (half_pos hε)
    refine ⟨fun x => 2 * (h x).re, hh.re.const_mul 2, ?_, ?_⟩
    · have hn : (∫ x, ‖2 * (h x).re‖) = 2 * ∫ x, ‖(h x).re‖ := by
        simp only [norm_mul, Real.norm_ofNat, integral_const_mul]
      rw [hn]
      have := integral_norm_re_le h hh
      linarith
    · have hreflect : ∀ᶠ ξ in 𝓝 ξ₀, 𝓕 h (-ξ) = 0 :=
        (continuous_neg.tendsto ξ₀).eventually haway
      filter_upwards [hflat, hreflect] with ξ hξ hneg
      simp only [integralFourier_eq_native, Complex.ofReal_mul, Complex.ofReal_ofNat]
      rw [fourier_const_mul, fourier_re h hh, hξ, hneg, map_zero, add_zero]
      change 2 * ((𝓕 fc ξ₀ - 𝓕 fc ξ) / 2) = _
      ring

end ExpandedFA.PartIV.WienerLocal
