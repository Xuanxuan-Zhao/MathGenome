import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinNonuniqueFourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Set
open scoped FourierTransform ComplexConjugate
namespace ExpandedFA.PartIV.KreinNonuniqueFourier

/-- The actual function in the adopted manuscript. -/
def h (x : ℝ) : ℝ := Real.exp (-Real.cosh x)

def hc (x : ℝ) : ℂ := (h x : ℂ)

lemma h_smooth : ContDiff ℝ ⊤ h := by unfold h; fun_prop

lemma h_even : Function.Even h := by intro x; simp [h]

lemma cosh_quadratic_lower (x : ℝ) : x ^ 2 / 2 ≤ Real.cosh x := by
  have hx := (Real.hasSum_cosh x).summable.le_tsum 1
    (fun n _ => div_nonneg (pow_nonneg (sq_nonneg x) n |>.trans_eq (pow_mul x 2 n).symm)
      (Nat.cast_nonneg _))
  rw [← (Real.hasSum_cosh x).tsum_eq]
  simpa using hx

lemma sinh_abs_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  rw [Real.abs_sinh, ← Real.cosh_abs x]
  exact (Real.sinh_lt_cosh _).le

lemma half_decay_integrable : Integrable (fun x : ℝ => Real.exp (-Real.cosh x / 2)) := by
  apply (integrable_exp_neg_mul_sq (b := (1/4 : ℝ)) (by norm_num)).mono'
    (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  nlinarith [cosh_quadratic_lower x]

/-- Fixed polynomial powers of cosh are absorbed by half the exponential decay. -/
lemma cosh_pow_decay (n : ℕ) (x : ℝ) :
    Real.cosh x ^ n * h x ≤
      (2 ^ n * (n.factorial : ℝ)) * Real.exp (-Real.cosh x / 2) := by
  have hy : 0 ≤ Real.cosh x / 2 := by positivity
  have hb := Real.pow_div_factorial_le_exp (Real.cosh x / 2) hy n
  have hf : (0 : ℝ) < n.factorial := by positivity
  have he : Real.exp (-Real.cosh x) > 0 := Real.exp_pos _
  have heq : Real.exp (Real.cosh x / 2) * Real.exp (-Real.cosh x) =
      Real.exp (-Real.cosh x / 2) := by rw [← Real.exp_add]; congr 1; ring
  have hb' : Real.cosh x ^ n ≤
      (2 ^ n * (n.factorial : ℝ)) * Real.exp (Real.cosh x / 2) := by
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at hb
    nlinarith
  calc
    _ ≤ ((2 ^ n * (n.factorial : ℝ)) * Real.exp (Real.cosh x / 2)) *
        Real.exp (-Real.cosh x) := mul_le_mul_of_nonneg_right hb' he.le
    _ = _ := by rw [mul_assoc, heq]

lemma cosh_pow_h_integrable (n : ℕ) :
    Integrable (fun x : ℝ => Real.cosh x ^ n * h x) := by
  apply (half_decay_integrable.const_mul (2 ^ n * (n.factorial : ℝ))).mono'
    (by unfold h; fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold h; positivity)]
  exact cosh_pow_decay n x

lemma h_integrable : Integrable h := by simpa using cosh_pow_h_integrable 0

lemma h_hasDerivAt (x : ℝ) : HasDerivAt h (-Real.sinh x * h x) x := by
  change HasDerivAt (fun y => Real.exp (-Real.cosh y)) _ x
  simpa only [h, Pi.neg_apply, mul_comm] using (Real.hasDerivAt_cosh x).neg.exp

lemma h_deriv : deriv h = fun x => -Real.sinh x * h x :=
  funext (fun x => (h_hasDerivAt x).deriv)

lemma h_second_deriv : deriv (deriv h) =
    fun x => (Real.sinh x ^ 2 - Real.cosh x) * h x := by
  rw [h_deriv]
  funext x
  convert (((Real.hasDerivAt_sinh x).neg).mul (h_hasDerivAt x)).deriv using 1
  simp only [Pi.neg_apply]
  ring

lemma h_deriv_integrable : Integrable (deriv h) := by
  rw [h_deriv]
  apply (cosh_pow_h_integrable 1).mono' (by unfold h; fun_prop)
  filter_upwards [] with x
  simp only [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), h]
  simpa [pow_one] using mul_le_mul_of_nonneg_right (sinh_abs_le_cosh x)
    (Real.exp_pos (-Real.cosh x)).le

lemma h_second_deriv_integrable : Integrable (deriv (deriv h)) := by
  rw [h_second_deriv]
  apply ((cosh_pow_h_integrable 2).add (cosh_pow_h_integrable 1)).mono'
    (by unfold h; fun_prop)
  filter_upwards [] with x
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (show 0 < h x from Real.exp_pos _)]
  have hb : |Real.sinh x ^ 2 - Real.cosh x| ≤ Real.cosh x ^ 2 + Real.cosh x := by
    calc
      _ ≤ |Real.sinh x ^ 2| + |Real.cosh x| := abs_sub _ _
      _ ≤ Real.cosh x ^ 2 + Real.cosh x := by
        rw [abs_of_nonneg (sq_nonneg _), abs_of_pos (Real.cosh_pos _), Real.sinh_sq]
        linarith
  simpa [pow_one, add_mul, h] using mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le

lemma hc_smooth : ContDiff ℝ ⊤ hc :=
  Complex.ofRealCLM.contDiff.comp h_smooth

lemma hc_integrable : Integrable hc := h_integrable.ofReal

lemma hc_deriv : deriv hc = fun x => ((deriv h x : ℝ) : ℂ) := by
  funext x
  exact (h_hasDerivAt x).ofReal_comp.deriv.trans
    (congrArg Complex.ofReal (congrFun h_deriv x).symm)

lemma hc_second_deriv : deriv (deriv hc) =
    fun x => ((deriv (deriv h) x : ℝ) : ℂ) := by
  rw [hc_deriv]
  funext x
  have hd : Differentiable ℝ (deriv h) := by rw [h_deriv]; unfold h; fun_prop
  exact (hd x).hasDerivAt.ofReal_comp.deriv

lemma hc_derivatives_integrable (k : ℕ) (hk : k ≤ 2) :
    Integrable (iteratedDeriv k hc) := by
  interval_cases k
  · simpa using hc_integrable
  · simpa [iteratedDeriv_succ, hc_deriv] using
      (h_deriv_integrable.ofReal : Integrable (fun x : ℝ => ((deriv h x : ℝ) : ℂ)))
  · simpa [iteratedDeriv_succ, hc_second_deriv] using
      (h_second_deriv_integrable.ofReal : Integrable (fun x : ℝ => ((deriv (deriv h) x : ℝ) : ℂ)))

lemma fourier_continuous {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

/-- A C²/L¹ criterion suffices here; no Schwartz certificate is assumed. -/
lemma fourier_integrable_of_two_derivatives {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (hd : ∀ k ≤ 2, Integrable (iteratedDeriv k f)) : Integrable (𝓕 f) := by
  let C := (∫ x, ‖f x‖) + (4 * Real.pi ^ 2)⁻¹ * ∫ x, ‖iteratedDeriv 2 f x‖
  apply (integrable_inv_one_add_sq.const_mul C).mono'
    (fourier_continuous (by simpa using hd 0 (by omega))).aestronglyMeasurable
  filter_upwards [] with u
  have hb := Real.one_add_sq_mul_norm_fourier_le hf hd u
  change (1 + u ^ 2) * ‖𝓕 f u‖ ≤ C at hb
  have hu : 0 < 1 + u ^ 2 := by positivity
  calc
    ‖𝓕 f u‖ ≤ C / (1 + u ^ 2) := (le_div_iff₀ hu).mpr (by nlinarith)
    _ = _ := by rw [div_eq_mul_inv]

lemma hc_fourier_integrable : Integrable (𝓕 hc) :=
  fourier_integrable_of_two_derivatives (hc_smooth.of_le (by simp))
    hc_derivatives_integrable

/-- Native Fourier frequency uses 2π; this density will subsequently be folded
by ξ ↦ |2πξ|, producing ordinary angular frequencies. -/
def density (u : ℝ) : ℝ := (𝓕 hc u).re

lemma density_continuous : Continuous density :=
  Complex.continuous_re.comp (fourier_continuous hc_integrable)

lemma density_integrable : Integrable density := hc_fourier_integrable.re

lemma hc_fourier_real (u : ℝ) : (𝓕 hc u).im = 0 := by
  have he : conj (𝓕 hc u) = 𝓕 hc u := by
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
    rw [← integral_neg_eq_self
      (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * u) * Complex.I) • hc x) volume]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [smul_eq_mul, map_mul, ← Complex.exp_conj,
      Complex.conj_ofReal, Complex.conj_I, hc, h, Real.cosh_neg]
    congr 2
    push_cast
    ring
  have hi := congrArg Complex.im he
  simp at hi
  linarith

lemma cosine_inversion (s : ℝ) :
    h s = ∫ u : ℝ, Real.cos ((2 * Real.pi * u) * s) * density u := by
  have hi := congrArg (RCLike.re : ℂ → ℝ)
    (hc_integrable.fourierInv_fourier_eq hc_fourier_integrable hc_smooth.continuous.continuousAt
      (v := s))
  simp only [Real.fourierInv_eq', smul_eq_mul] at hi
  have hint : Integrable (fun u : ℝ =>
      Complex.exp (↑(2 * Real.pi * inner ℝ u s) * Complex.I) * 𝓕 hc u) := by
    apply hc_fourier_integrable.bdd_mul (c := 1) (by fun_prop)
    filter_upwards [] with u
    simp only [Complex.norm_exp_ofReal_mul_I, le_refl]
  rw [← integral_re hint] at hi
  change (∫ u : ℝ, (Complex.exp (↑(2 * Real.pi * inner ℝ u s) * Complex.I) *
    𝓕 hc u).re) = h s at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [Complex.mul_re, hc_fourier_real, mul_zero, sub_zero,
    Complex.exp_ofReal_mul_I_re, real_inner_comm, Real.inner_apply, density]
  congr 2
  ring

/-- Fold a real signed density to nonnegative angular frequencies. -/
def foldedMeasure (g : ℝ → ℝ) : Measure ℝ :=
  Measure.map (fun u : ℝ => |2 * Real.pi * u|)
    (volume.withDensity (fun u => ENNReal.ofReal (g u)))

lemma positive_density_finite {g : ℝ → ℝ} (hg : Integrable g) :
    IsFiniteMeasure (volume.withDensity (fun u => ENNReal.ofReal (g u))) := by
  apply isFiniteMeasure_withDensity
  have ht := (hasFiniteIntegral_iff_ofReal
    (ae_of_all volume (fun u => le_max_right (g u) 0))).mp hg.pos_part.hasFiniteIntegral
  simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le] using ht.ne

lemma foldedMeasure_finite {g : ℝ → ℝ} (hg : Integrable g) :
    IsFiniteMeasure (foldedMeasure g) := by
  haveI := positive_density_finite hg
  unfold foldedMeasure
  infer_instance

lemma foldedMeasure_support (g : ℝ → ℝ) : foldedMeasure g (Iio 0) = 0 := by
  rw [foldedMeasure, Measure.map_apply (by fun_prop) measurableSet_Iio]
  have he : (fun u : ℝ => |2 * Real.pi * u|) ⁻¹' Iio 0 = ∅ := by
    ext u
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false]
    exact not_lt_of_ge (abs_nonneg _)
  rw [he, measure_empty]

lemma cosine_integrable_finite (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) :
    Integrable (fun a => Real.cos (a * s)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [] with a
  exact (Real.norm_eq_abs _).trans_le (Real.abs_cos_le_one _)

lemma foldedMeasure_cosine {g : ℝ → ℝ} (hg : Continuous g) (s : ℝ) :
    (∫ a, Real.cos (a * s) ∂foldedMeasure g) =
      ∫ u : ℝ, Real.cos ((2 * Real.pi * u) * s) * max (g u) 0 := by
  rw [foldedMeasure, integral_map (by fun_prop) (by fun_prop)]
  rw [integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (ae_of_all volume (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1
  rcases le_total 0 (2 * Real.pi * u) with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_nonpos hu, neg_mul, Real.cos_neg]

lemma cosine_density_part_integrable (s : ℝ) (ε : ℝ) :
    Integrable (fun u : ℝ => Real.cos ((2 * Real.pi * u) * s) *
      max (ε * density u) 0) := by
  apply (density_integrable.const_mul ε).pos_part.bdd_mul (c := 1) (by
    exact (by fun_prop : Continuous (fun u : ℝ => Real.cos ((2 * Real.pi * u) * s))).aestronglyMeasurable)
  filter_upwards [] with u
  simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one ((2 * Real.pi * u) * s)

theorem signed_cosine_representation : Spec.SignedCosineRepresentation := by
  let αp := foldedMeasure density
  let αm := foldedMeasure (fun u => -density u)
  have hp : IsFiniteMeasure αp := foldedMeasure_finite density_integrable
  have hm : IsFiniteMeasure αm := foldedMeasure_finite density_integrable.neg
  haveI := hp
  haveI := hm
  refine ⟨αp, αm, hp, hm, foldedMeasure_support _, foldedMeasure_support _, ?_⟩
  intro s
  refine ⟨cosine_integrable_finite αp s, cosine_integrable_finite αm s, ?_⟩
  rw [show αp = foldedMeasure density from rfl,
    show αm = foldedMeasure (fun u => -density u) from rfl,
    foldedMeasure_cosine density_continuous,
    foldedMeasure_cosine (g := fun u => -density u) (by exact density_continuous.neg),
    ← integral_sub]
  · change h s = _
    rw [cosine_inversion]
    apply integral_congr_ae
    filter_upwards [] with u
    rw [← mul_sub]
    congr 1
    simp only [max_def]
    split_ifs <;> linarith
  · simpa using cosine_density_part_integrable s 1
  · simpa using cosine_density_part_integrable s (-1)

end ExpandedFA.PartIV.KreinNonuniqueFourier
