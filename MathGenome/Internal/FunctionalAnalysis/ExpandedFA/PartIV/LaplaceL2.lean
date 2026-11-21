import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.LaplaceL2
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.SchurWeighted
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace ExpandedFA.PartIV.LaplaceL2
open LaplaceL2Spec

lemma weight_integrable {s : ℝ} (hs : 0 < s) :
    Integrable (fun t : ℝ => Real.exp (-(s*t)) * t ^ (- (1/2 : ℝ))) halfLine := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1/2:ℝ))
      (by norm_num) (by norm_num) hs).congr
      (Filter.Eventually.of_forall fun t => mul_comm _ _)

lemma weight_integral {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ, Real.exp (-(s*t)) * t ^ (- (1/2 : ℝ)) ∂halfLine) =
      Real.sqrt Real.pi * s ^ (- (1/2 : ℝ)) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1/2) (by norm_num) hs
  rw [Real.Gamma_one_half_eq] at h
  simp only [one_div, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le] at h
  calc
    _ = ∫ t : ℝ in Ioi 0, t ^ ((1/2:ℝ) - 1) * Real.exp (-(s*t)) := by
      congr 1
      funext t
      norm_num
      ring
    _ = _ := by simpa only [one_div] using h.trans (mul_comm _ _)

def weight (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (t ^ (- (1/2 : ℝ)))

def schurConstant : ℝ≥0 := ⟨Real.sqrt Real.pi, Real.sqrt_nonneg _⟩

lemma weight_measurable : Measurable weight := by
  unfold weight
  fun_prop

lemma weight_positive_finite : ∀ᵐ t ∂halfLine, 0 < weight t ∧ weight t < ∞ := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact ⟨ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos ht _), ENNReal.ofReal_lt_top⟩

lemma kernel_enorm (𝕜 : Type) [RCLike 𝕜] (s t : ℝ) :
    ‖laplaceKernel 𝕜 s t‖ₑ = ENNReal.ofReal (Real.exp (-(s*t))) := by
  rw [← ofReal_norm]
  simp [laplaceKernel]

lemma schur_row (𝕜 : Type) [RCLike 𝕜] {s : ℝ} (hs : 0 < s) :
    (∫⁻ t, ‖laplaceKernel 𝕜 s t‖ₑ * weight t ∂halfLine) =
      (schurConstant : ℝ≥0∞) * weight s := by
  simp_rw [kernel_enorm, weight, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rw [← ofReal_integral_eq_lintegral_ofReal (weight_integrable hs)]
  · rw [weight_integral hs, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1
    exact ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg ht.le _)

lemma schur_hypotheses (𝕜 : Type) [RCLike 𝕜] :
    ExpandedFA.PartV.SchurWeightedSpec.Hypotheses halfLine halfLine
      (fun p : ℝ × ℝ => laplaceKernel 𝕜 p.1 p.2)
      weight weight schurConstant schurConstant := by
  refine ⟨?_, weight_measurable, weight_measurable, weight_positive_finite,
    weight_positive_finite, ?_, ?_⟩
  · unfold laplaceKernel
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (schur_row 𝕜 hs).le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [laplaceKernel, mul_comm] using (schur_row 𝕜 ht).le

/-- Schur's construction applied to the actual Laplace kernel. -/
def laplaceOperator (𝕜 : Type) [RCLike 𝕜] : Space 𝕜 →L[𝕜] Space 𝕜 :=
  ExpandedFA.PartV.SchurWeighted.integralOperator _ _ _ _ _ (schur_hypotheses 𝕜)

lemma laplace_norm (𝕜 : Type) [RCLike 𝕜] :
    ‖laplaceOperator 𝕜‖ ≤ Real.sqrt Real.pi := by
  have h := ExpandedFA.PartV.SchurWeighted.integralOperator_norm _ _ _ _ _
    (schur_hypotheses 𝕜)
  change ‖laplaceOperator 𝕜‖ ≤ Real.sqrt (Real.sqrt Real.pi * Real.sqrt Real.pi) at h
  rwa [Real.sqrt_mul_self (Real.sqrt_nonneg _)] at h

lemma laplace_memLp {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (hf : MemLp f 2 halfLine) :
    MemLp (laplaceIntegral f) 2 halfLine :=
  ExpandedFA.PartV.SchurWeighted.output_memLp _ _ _ _ _ (schur_hypotheses 𝕜) f hf

lemma laplace_ae {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (hf : MemLp f 2 halfLine) :
    (laplaceOperator 𝕜 (hf.toLp f) : ℝ → 𝕜) =ᵐ[halfLine] laplaceIntegral f := by
  exact (ExpandedFA.PartV.SchurWeighted.integralOperator_ae _ _ _ _ _
    (schur_hypotheses 𝕜) (hf.toLp f)).trans
      (ExpandedFA.PartV.L2Kernel.kernel_representative_independence halfLine halfLine
        (fun p : ℝ × ℝ => laplaceKernel 𝕜 p.1 p.2) _ _ f
        Filter.EventuallyEq.rfl hf.coeFn_toLp)

lemma kernel_norm (𝕜 : Type) [RCLike 𝕜] (s t : ℝ) :
    ‖laplaceKernel 𝕜 s t‖ = Real.exp (-(s*t)) := by
  simp [laplaceKernel]

lemma kernel_measurable (𝕜 : Type) [RCLike 𝕜] :
    Measurable (fun p : ℝ × ℝ => laplaceKernel 𝕜 p.1 p.2) := by
  unfold laplaceKernel
  fun_prop

lemma exp_memLp {s : ℝ} (hs : 0 < s) :
    MemLp (fun t : ℝ => Real.exp (-(s*t))) 2 halfLine := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have h := integrableOn_exp_mul_Ioi (a := -(2*s)) (by linarith) 0
  have heq : (fun t : ℝ => Real.exp (-(s*t)) ^ 2) =
      (fun t : ℝ => Real.exp (-(2*s)*t)) := by
    funext t
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq]
  exact h

lemma kernel_memLp (𝕜 : Type) [RCLike 𝕜] {s : ℝ} (hs : 0 < s) :
    MemLp (laplaceKernel 𝕜 s) 2 halfLine := by
  apply (memLp_two_iff_integrable_sq_norm (by unfold laplaceKernel; fun_prop)).mpr
  simpa only [kernel_norm] using (exp_memLp hs).integrable_sq

lemma laplace_integrable {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜)
    (hf : MemLp f 2 halfLine) {s : ℝ} (hs : 0 < s) :
    Integrable (fun t => laplaceKernel 𝕜 s t * f t) halfLine :=
  (kernel_memLp 𝕜 hs).integrable_mul hf

/-- The absolute Laplace integral is itself an L² function. -/
lemma absolute_laplace_memLp {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜)
    (hf : MemLp f 2 halfLine) :
    MemLp (fun s => ∫ t, ‖laplaceKernel 𝕜 s t * f t‖ ∂halfLine) 2 halfLine := by
  convert laplace_memLp (fun t => ‖f t‖) hf.norm using 1
  funext s
  congr 1
  funext t
  rw [norm_mul, kernel_norm]
  rfl

/-- A weighted L²–L² pairing gives absolute Fubini for the symmetric kernel. -/
lemma pairing_integrable {𝕜 : Type} [RCLike 𝕜] (f g : ℝ → 𝕜)
    (hf : MemLp f 2 halfLine) (hg : MemLp g 2 halfLine) :
    Integrable (fun p : ℝ × ℝ => star (f p.1) *
      (laplaceKernel 𝕜 p.1 p.2 * g p.2)) (halfLine.prod halfLine) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => star (f p.1) *
      (laplaceKernel 𝕜 p.1 p.2 * g p.2)) (halfLine.prod halfLine) :=
    hf.aestronglyMeasurable.comp_fst.star.mul
      ((kernel_measurable 𝕜).aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd)
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (laplace_integrable g hg hs).const_mul _
  · have h := hf.norm.integrable_mul (absolute_laplace_memLp g hg)
    convert h using 1
    funext s
    simp only [norm_mul, norm_star]
    exact integral_const_mul _ _

/-- Absolute Fubini for composing the two Laplace integrals, at every s > 0. -/
lemma square_integrable {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜)
    (hf : MemLp f 2 halfLine) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : ℝ × ℝ => laplaceKernel 𝕜 s p.1 *
      (laplaceKernel 𝕜 p.1 p.2 * f p.2)) (halfLine.prod halfLine) := by
  convert pairing_integrable (laplaceKernel 𝕜 s) f (kernel_memLp 𝕜 hs) hf using 1
  simp only [laplaceKernel, RCLike.star_def, RCLike.conj_ofReal]

lemma kernel_composition_integral (𝕜 : Type) [RCLike 𝕜] {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (z : 𝕜) :
    (∫ u, laplaceKernel 𝕜 s u * (laplaceKernel 𝕜 u t * z) ∂halfLine) =
      z / RCLike.ofReal (s+t) := by
  have heq : (fun u => laplaceKernel 𝕜 s u * (laplaceKernel 𝕜 u t * z)) =
      (fun u => RCLike.ofReal (Real.exp (-(s+t)*u)) * z) := by
    funext u
    simp only [laplaceKernel, ← mul_assoc, ← map_mul, ← Real.exp_add]
    rw [show -(s*u) + -(u*t) = -(s+t)*u by ring]
  rw [heq, integral_mul_const, integral_ofReal]
  have h := integral_exp_mul_Ioi (a := -(s+t)) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div] at h
  change (RCLike.ofReal (∫ u in Ioi 0, Real.exp (-(s+t)*u))) * z = _
  rw [h]
  simp only [map_inv₀, div_eq_mul_inv]
  exact mul_comm _ _

lemma carleman_integrable {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜)
    (hf : MemLp f 2 halfLine) {s : ℝ} (hs : 0 < s) :
    Integrable (fun t => f t / RCLike.ofReal (s+t)) halfLine := by
  apply (square_integrable f hf hs).integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact kernel_composition_integral 𝕜 hs ht (f t)

lemma laplace_square_integral {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜)
    (hf : MemLp f 2 halfLine) {s : ℝ} (hs : 0 < s) :
    laplaceIntegral (laplaceIntegral f) s = carlemanIntegral f s := by
  unfold laplaceIntegral carlemanIntegral
  calc
    _ = ∫ u, ∫ t, laplaceKernel 𝕜 s u * (laplaceKernel 𝕜 u t * f t)
        ∂halfLine ∂halfLine := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact (integral_const_mul _ _).symm
    _ = ∫ t, ∫ u, laplaceKernel 𝕜 s u * (laplaceKernel 𝕜 u t * f t)
        ∂halfLine ∂halfLine := integral_integral_swap (square_integrable f hf hs)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact kernel_composition_integral 𝕜 hs ht (f t)

lemma kernel_pairing_integral {𝕜 : Type} [RCLike 𝕜]
    (f : ℝ → 𝕜) (t : ℝ) (z : 𝕜) :
    (∫ s, star (f s) * (laplaceKernel 𝕜 s t * z) ∂halfLine) =
      star (laplaceIntegral f t) * z := by
  have heq : (fun s => star (f s) * (laplaceKernel 𝕜 s t * z)) =
      (fun s => star (laplaceKernel 𝕜 t s * f s) * z) := by
    funext s
    simp only [star_mul, laplaceKernel, RCLike.star_def, RCLike.conj_ofReal]
    rw [mul_comm t s]
    ring
  rw [heq, integral_mul_const]
  simp only [RCLike.star_def, integral_conj, laplaceIntegral]

lemma laplace_selfAdjoint (𝕜 : Type) [RCLike 𝕜] (f g : Space 𝕜) :
    inner 𝕜 (laplaceOperator 𝕜 f) g = inner 𝕜 f (laplaceOperator 𝕜 g) := by
  have hf := laplace_ae f (Lp.memLp f)
  have hg := laplace_ae g (Lp.memLp g)
  simp only [Lp.toLp_coeFn] at hf hg
  symm
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ s, star (f s) * laplaceIntegral g s ∂halfLine := by
      apply integral_congr_ae
      filter_upwards [hg] with s hs
      simp only [hs, RCLike.inner_apply, RCLike.star_def]
      exact mul_comm _ _
    _ = ∫ s, ∫ t, star (f s) * (laplaceKernel 𝕜 s t * g t)
        ∂halfLine ∂halfLine := by
      apply integral_congr_ae
      filter_upwards [] with s
      exact (integral_const_mul _ _).symm
    _ = ∫ t, ∫ s, star (f s) * (laplaceKernel 𝕜 s t * g t)
        ∂halfLine ∂halfLine :=
      integral_integral_swap (pairing_integrable f g (Lp.memLp f) (Lp.memLp g))
    _ = ∫ t, star (laplaceIntegral f t) * g t ∂halfLine := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact kernel_pairing_integral f t (g t)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf] with t ht
      simp only [ht, RCLike.inner_apply, RCLike.star_def]
      exact mul_comm _ _

lemma laplaceIntegral_congr {𝕜 : Type} [RCLike 𝕜] {f g : ℝ → 𝕜}
    (h : f =ᵐ[halfLine] g) (s : ℝ) :
    laplaceIntegral f s = laplaceIntegral g s := by
  apply integral_congr_ae
  filter_upwards [h] with t ht
  rw [ht]

/-- The Carleman operator is the composition square of the bounded Laplace operator. -/
def carlemanOperator (𝕜 : Type) [RCLike 𝕜] : Space 𝕜 →L[𝕜] Space 𝕜 :=
  (laplaceOperator 𝕜).comp (laplaceOperator 𝕜)

lemma carleman_ae {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜)
    (hf : MemLp f 2 halfLine) :
    (carlemanOperator 𝕜 (hf.toLp f) : ℝ → 𝕜) =ᵐ[halfLine] carlemanIntegral f := by
  have h := laplace_ae (laplaceOperator 𝕜 (hf.toLp f)) (Lp.memLp _)
  simp only [Lp.toLp_coeFn] at h
  filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with s hs hpos
  change (laplaceOperator 𝕜 (laplaceOperator 𝕜 (hf.toLp f)) : ℝ → 𝕜) s = _
  rw [hs, laplaceIntegral_congr (laplace_ae f hf), laplace_square_integral f hf hpos]

/-- Bounded self-adjoint Laplace transform, with its Carleman square and
absolute Fubini on every L² input. -/
theorem laplace_l2 : LaplaceTheorem := by
  intro 𝕜 _
  refine ⟨laplaceOperator 𝕜, carlemanOperator 𝕜, laplace_norm 𝕜,
    laplace_selfAdjoint 𝕜, rfl, ?_⟩
  intro f hf
  exact ⟨fun _ hs => laplace_integrable f hf hs,
    fun _ hs => carleman_integrable f hf hs, laplace_ae f hf, carleman_ae f hf,
    fun _ hs => square_integrable f hf hs, fun _ hs => laplace_square_integral f hf hs⟩

end ExpandedFA.PartIV.LaplaceL2
