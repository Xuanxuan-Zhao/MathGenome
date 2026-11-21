import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.HamburgerDeterminacy
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Moments.HamburgerExistence
import Mathlib.MeasureTheory.Function.L2Space
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SelfAdjointRangeCriterion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ExpandedFA.Moments.HamburgerDeterminacy
open HamburgerDeterminacySpec

/-- Unnormalized Poisson kernel; its total mass is π. -/
def poissonKernel (ε x : ℝ) : ℝ := ε / (x ^ 2 + ε ^ 2)

lemma poissonKernel_pos {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 < poissonKernel ε x := by
  unfold poissonKernel
  exact div_pos hε (by positivity)

lemma continuous_poissonKernel {ε : ℝ} (hε : 0 < ε) :
    Continuous (poissonKernel ε) := by
  unfold poissonKernel
  exact continuous_const.div (continuous_id.pow 2 |>.add continuous_const)
    (fun x => ne_of_gt (by positivity))

lemma poissonKernel_scaled {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    poissonKernel ε x = ε⁻¹ * (1 + (x / ε) ^ 2)⁻¹ := by
  unfold poissonKernel
  field_simp
  ring

lemma poissonKernel_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (poissonKernel ε) := by
  change Integrable (fun x => poissonKernel ε x)
  simp_rw [poissonKernel_scaled hε.ne']
  exact (integrable_inv_one_add_sq.comp_div hε.ne').const_mul _

lemma poissonKernel_integral {ε : ℝ} (hε : 0 < ε) :
    (∫ x, poissonKernel ε x) = Real.pi := by
  simp_rw [poissonKernel_scaled hε.ne']
  rw [integral_const_mul]
  have hi := Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) ε
  simp only [integral_univ_inv_one_add_sq, abs_of_pos hε, smul_eq_mul] at hi
  rw [hi]
  field_simp

lemma poissonKernel_translate_integrable {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun a => poissonKernel ε (a - t)) :=
  (poissonKernel_integrable hε).comp_sub_right t

lemma poissonKernel_translate_integral {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ a, poissonKernel ε (a - t)) = Real.pi := by
  rw [integral_sub_right_eq_self, poissonKernel_integral hε]

/-- Resolvent kernels are integrable against arbitrary finite positive measures. -/
theorem integrable_cauchyKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    {z : ℂ} (hz : z.im ≠ 0) : Integrable (fun t : ℝ => (z - (t : ℂ))⁻¹) μ := by
  have hne (t : ℝ) : z - (t : ℂ) ≠ 0 := by
    intro he
    have := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at this
    exact hz this
  apply Integrable.mono' (integrable_const (|z.im|⁻¹))
    (((continuous_const.sub Complex.continuous_ofReal).inv₀ hne).aestronglyMeasurable)
  apply ae_of_all
  intro t
  change ‖(z - (t : ℂ))⁻¹‖ ≤ |z.im|⁻¹
  rw [norm_inv]
  apply inv_anti₀ (abs_pos.mpr hz)
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
    Complex.abs_im_le_norm (z - (t : ℂ))

/-- The imaginary part of a Cauchy transform is its Poisson integral, with the
minus sign coming from the shared z − t convention. -/
theorem neg_im_cauchyTransform (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a : ℝ) {ε : ℝ} (hε : 0 < ε) :
    -(cauchyTransform μ ((a : ℂ) + (ε : ℂ) * Complex.I)).im =
      ∫ t, poissonKernel ε (a - t) ∂μ := by
  have hz : ((a : ℂ) + (ε : ℂ) * Complex.I).im ≠ 0 := by
    simpa using hε.ne'
  unfold cauchyTransform
  change -RCLike.im (∫ t : ℝ, ((a : ℂ) + (ε : ℂ) * Complex.I - (t : ℂ))⁻¹ ∂μ) = _
  rw [← integral_im (integrable_cauchyKernel μ hz), ← integral_neg]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp [poissonKernel, Complex.normSq_apply, Complex.mul_im,
    Complex.mul_re, pow_two]
  ring

/-- Averaging a bounded continuous function against the fixed Cauchy density
is well-defined, even when the function has no compact support. -/
def poissonAverage (ε : ℝ) (f : ℝ →ᵇ ℝ) (t : ℝ) : ℝ :=
  ∫ y : ℝ, (1 + y ^ 2)⁻¹ * f (t - ε * y)

lemma poissonAverage_integrable (ε : ℝ) (f : ℝ →ᵇ ℝ) (t : ℝ) :
    Integrable (fun y : ℝ => (1 + y ^ 2)⁻¹ * f (t - ε * y)) := by
  apply (integrable_inv_one_add_sq.mul_const ‖f‖).mono' (by fun_prop)
  apply ae_of_all
  intro y
  rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (1 + y ^ 2)⁻¹)]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (by positivity)

lemma poissonAverage_bound (ε : ℝ) (f : ℝ →ᵇ ℝ) (t : ℝ) :
    ‖poissonAverage ε f t‖ ≤ Real.pi * ‖f‖ := by
  unfold poissonAverage
  calc ‖∫ y : ℝ, (1 + y ^ 2)⁻¹ * f (t - ε * y)‖
    _ ≤ ∫ y : ℝ, ‖(1 + y ^ 2)⁻¹ * f (t - ε * y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, (1 + y ^ 2)⁻¹ * ‖f‖ := by
      apply integral_mono (poissonAverage_integrable ε f t).norm
        (integrable_inv_one_add_sq.mul_const _)
      intro y
      change ‖(1 + y ^ 2)⁻¹ * f (t - ε * y)‖ ≤ (1 + y ^ 2)⁻¹ * ‖f‖
      rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (1 + y ^ 2)⁻¹)]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (by positivity)
    _ = Real.pi * ‖f‖ := by rw [integral_mul_const, integral_univ_inv_one_add_sq]

/-- The Poisson averages converge at each point by dominated convergence after
rescaling to a fixed integrable density. -/
lemma poissonAverage_tendsto (f : ℝ →ᵇ ℝ) (t : ℝ) :
    Tendsto (fun ε : ℝ => poissonAverage ε f t) (𝓝 0) (𝓝 (Real.pi * f t)) := by
  have hlim : Tendsto (fun ε : ℝ => poissonAverage ε f t) (𝓝 0)
      (𝓝 (∫ y : ℝ, (1 + y ^ 2)⁻¹ * f t)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun y : ℝ => (1 + y ^ 2)⁻¹ * ‖f‖)
    · exact Eventually.of_forall (fun ε => (poissonAverage_integrable ε f t).aestronglyMeasurable)
    · apply Eventually.of_forall
      intro ε
      apply ae_of_all
      intro y
      rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (1 + y ^ 2)⁻¹)]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (by positivity)
    · exact integrable_inv_one_add_sq.mul_const _
    · apply ae_of_all
      intro y
      apply Tendsto.const_mul
      apply f.continuous.continuousAt.tendsto.comp
      simpa using (tendsto_const_nhds (x := t)).sub ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).mul_const y)
  simpa only [integral_mul_const, integral_univ_inv_one_add_sq] using hlim

lemma poissonAverage_eq (f : ℝ →ᵇ ℝ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    poissonAverage ε f t = ∫ a, poissonKernel ε (a - t) * f a := by
  let q : ℝ → ℝ := fun a => poissonKernel ε (a - t) * f a
  have hscale (y : ℝ) :
      (1 + y ^ 2)⁻¹ * f (t - ε * y) = ε * q (t - ε * y) := by
    dsimp [q, poissonKernel]
    have he : (t - ε * y - t) ^ 2 + ε ^ 2 = ε ^ 2 * (1 + y ^ 2) := by ring
    rw [he]
    field_simp
  have hchange : (∫ y : ℝ, q (t - ε * y)) = ε⁻¹ * ∫ a, q a := by
    have he := Measure.integral_comp_mul_left (fun x : ℝ => q (t - x)) ε
    simpa only [abs_inv, abs_of_pos hε, smul_eq_mul,
      integral_sub_left_eq_self] using he
  unfold poissonAverage
  simp_rw [hscale]
  rw [integral_const_mul, hchange]
  change ε * (ε⁻¹ * ∫ a, q a) = ∫ a, q a
  rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]

lemma poisson_test_integrable (f : ℝ →ᵇ ℝ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun a => poissonKernel ε (a - t) * f a) := by
  apply ((poissonKernel_translate_integrable hε t).mul_const ‖f‖).mono' (by
    exact ((continuous_poissonKernel hε).comp (continuous_id.sub continuous_const) |>.mul
      f.continuous).aestronglyMeasurable)
  apply ae_of_all
  intro a
  rw [norm_mul, Real.norm_of_nonneg (poissonKernel_pos hε _).le]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (poissonKernel_pos hε _).le

lemma poisson_test_norm_integral_le (f : ℝ →ᵇ ℝ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ a, ‖poissonKernel ε (a - t) * f a‖) ≤ Real.pi * ‖f‖ := by
  calc (∫ a, ‖poissonKernel ε (a - t) * f a‖)
    _ ≤ ∫ a, poissonKernel ε (a - t) * ‖f‖ := by
      apply integral_mono (poisson_test_integrable f t hε).norm
        ((poissonKernel_translate_integrable hε t).mul_const _)
      intro a
      try dsimp only
      rw [norm_mul, Real.norm_of_nonneg (poissonKernel_pos hε _).le]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (poissonKernel_pos hε _).le
    _ = Real.pi * ‖f‖ := by rw [integral_mul_const, poissonKernel_translate_integral hε t]

lemma poisson_test_prod_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℝ × ℝ => poissonKernel ε (p.2 - p.1) * f p.2)
      (μ.prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => poissonKernel ε (p.2 - p.1) * f p.2) (μ.prod volume) :=
    (((continuous_poissonKernel hε).comp (continuous_snd.sub continuous_fst)).mul
      (f.continuous.comp continuous_snd)).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  refine ⟨ae_of_all _ (fun t => poisson_test_integrable f t hε), ?_⟩
  exact (integrable_const (Real.pi * ‖f‖)).mono' hm.norm.integral_prod_right'
    (ae_of_all _ (fun t => le_trans (le_of_eq (Real.norm_of_nonneg
      (integral_nonneg (fun a => norm_nonneg _)))) (poisson_test_norm_integral_le f t hε)))

/-- The smoothed integral is determined by the transform, without a support or
absolute-continuity assumption on the finite measure. -/
lemma integral_poissonAverage (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ t, poissonAverage ε f t ∂μ) =
      ∫ a, f a * (-(cauchyTransform μ ((a : ℂ) + (ε : ℂ) * Complex.I)).im) := by
  simp_rw [poissonAverage_eq f _ hε]
  rw [integral_integral_swap (poisson_test_prod_integrable μ f hε)]
  apply integral_congr_ae
  apply ae_of_all
  intro a
  dsimp only
  rw [integral_mul_const, mul_comm]
  rw [neg_im_cauchyTransform μ a hε]

/-- Integration against any finite measure commutes with the limit of the
uniformly bounded Poisson averages. -/
lemma integral_poissonAverage_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun ε : ℝ => ∫ t, poissonAverage ε f t ∂μ) (𝓝 0)
      (𝓝 (Real.pi * ∫ t, f t ∂μ)) := by
  have hm (ε : ℝ) : AEStronglyMeasurable (poissonAverage ε f) μ := by
    unfold poissonAverage
    exact (show AEStronglyMeasurable
      (fun p : ℝ × ℝ => (1 + p.2 ^ 2)⁻¹ * f (p.1 - ε * p.2)) (μ.prod volume) by
        fun_prop).integral_prod_right'
  have ht : Tendsto (fun ε : ℝ => ∫ t, poissonAverage ε f t ∂μ) (𝓝 0)
      (𝓝 (∫ t, Real.pi * f t ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => Real.pi * ‖f‖)
    · exact Eventually.of_forall hm
    · exact Eventually.of_forall (fun ε => ae_of_all _ (poissonAverage_bound ε f))
    · exact integrable_const _
    · exact ae_of_all _ (poissonAverage_tendsto f)
  simpa only [integral_const_mul] using ht

/-- Finite positive Borel measures on ℝ are determined by their Cauchy transforms
on the nonreal points. -/
theorem cauchy_transform_injectivity : CauchyTransformInjectivity := by
  intro μ ν hμ hν hC
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have he : (fun ε : ℝ => ∫ t, poissonAverage ε f t ∂μ) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ∫ t, poissonAverage ε f t ∂ν) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [integral_poissonAverage μ f hε, integral_poissonAverage ν f hε]
    apply integral_congr_ae
    apply ae_of_all
    intro a
    dsimp only
    rw [hC _ (by simpa using (show 0 < ε from hε).ne')]
  have hlimμ := (integral_poissonAverage_tendsto μ f).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hlimν := (integral_poissonAverage_tendsto ν f).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have heq : Real.pi * (∫ t, f t ∂μ) = Real.pi * (∫ t, f t ∂ν) :=
    tendsto_nhds_unique (hlimμ.congr' he) hlimν
  exact mul_left_cancel₀ Real.pi_ne_zero heq

section ResolventSubspace
open Unbounded
universe u v
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Every nonreal shift of a self-adjoint operator has full range. The domain
here is the actual partial-operator domain. -/
lemma selfAdjoint_shift_surjective (S : Operator ℂ H H) (hS : Unbounded.IsSelfAdjoint S)
    (z : ℂ) (hz : z.im ≠ 0) (x : H) :
    ∃ y : S.domain, z • (y : H) - S y = x := by
  have hc : S.IsClosed := by
    rw [hS.2]
    exact hilbertAdjoint_isClosed S hS.1
  have hs : IsSymmetric S := ⟨hS.1, hS.2.le⟩
  have hzc : (starRingEnd ℂ z).im ≠ 0 := by simpa using hz
  have hr := closed_symmetric_shift_range S hc hs z hz
  rw [hS.deficiencySpace_eq_bot _ hzc, Submodule.bot_orthogonal_eq_top] at hr
  have hx : x ∈ Unbounded.range (shift z S) := by rw [hr]; trivial
  exact hx

/-- Intertwining on the initial graph extends to its closure whenever the
ambient operator is closed. This uses only continuity of the isometric embedding. -/
lemma graph_closure_intertwining (S : Operator ℂ H H) (hS : S.IsClosable)
    (T : Operator ℂ K K) (hT : T.IsClosed) (J : H →ₗᵢ[ℂ] K)
    (hJ : ∀ y : S.domain, (J (y : H), J (S y)) ∈ T.graph) :
    ∀ y : S.closure.domain, (J (y : H), J (S.closure y)) ∈ T.graph := by
  have hc : _root_.IsClosed {p : H × H | (J p.1, J p.2) ∈ T.graph} :=
    hT.preimage ((J.continuous.comp continuous_fst).prodMk
      (J.continuous.comp continuous_snd))
  have hs : (S.graph : Set (H × H)) ⊆ {p : H × H | (J p.1, J p.2) ∈ T.graph} := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨a, rfl, rfl⟩ := S.mem_graph_iff.mp hxy
    exact hJ a
  have hclosed := closure_minimal hs hc
  intro y
  have hmem : ((y : H), S.closure y) ∈ closure (S.graph : Set (H × H)) := by
    change ((y : H), S.closure y) ∈ S.graph.topologicalClosure
    rw [hS.graph_closure_eq_closure_graph]
    exact S.closure.mem_graph y
  exact hclosed hmem

/-- An ambient symmetric extension cannot move a nonreal resolvent solution
outside an embedded self-adjoint subspace. J need not be surjective. This is the
key domain argument for a representing measure with nondense polynomials. -/
theorem resolvent_solution_mem_range (S : Operator ℂ H H) (hS : Unbounded.IsSelfAdjoint S)
    (T : Operator ℂ K K) (hT : IsSymmetric T) (J : H →ₗᵢ[ℂ] K)
    (hJ : ∀ y : S.domain, (J (y : H), J (S y)) ∈ T.graph)
    (z : ℂ) (hz : z.im ≠ 0) (x : H) (w : T.domain)
    (hw : z • (w : K) - T w = J x) : (w : K) ∈ J.toLinearMap.range := by
  obtain ⟨y, hy⟩ := selfAdjoint_shift_surjective S hS z hz x
  obtain ⟨yT, hyT, hTy⟩ := T.mem_graph_iff.mp (hJ y)
  have heq : T (w - yT) - z • ((w - yT : T.domain) : K) = 0 := by
    rw [LinearPMap.map_sub]
    change T w - T yT - z • ((w : K) - (yT : K)) = 0
    rw [hTy, hyT]
    have hJhy : z • J (y : H) - J (S y) = J x := by
      simpa only [map_sub, map_smul] using congrArg J hy
    rw [smul_sub]
    calc _ = (z • J (y : H) - J (S y)) - (z • (w : K) - T w) := by module
         _ = 0 := by rw [hJhy, hw, sub_self]
  have hb := hT.nonreal_lower_bound z (w - yT)
  rw [heq, norm_zero] at hb
  have hn : ‖((w - yT : T.domain) : K)‖ = 0 := by
    have hp := abs_pos.mpr hz
    nlinarith [norm_nonneg (((w - yT : T.domain) : K))]
  have hv : (w : K) = J (y : H) := by
    have := norm_eq_zero.mp hn
    change (w : K) - (yT : K) = 0 at this
    rw [hyT] at this
    exact sub_eq_zero.mp this
  exact ⟨(y : H), hv.symm⟩

end ResolventSubspace

section RepresentingMeasures
open Polynomial PolynomialMomentHilbertSpaceSpec HamburgerExistenceProof

/-- Polynomial evaluation is integrable because every absolute moment is finite. -/
lemma integrable_polynomial_eval {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (p : ℂ[X]) :
    Integrable (fun t : ℝ => p.eval (t : ℂ)) μ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    ext t
    simp
  | monomial n c =>
    simpa only [eval_monomial] using
      (RepresentsHamburgerMoments.integrable_complex_pow hμ n).const_mul c

lemma integral_polynomial_eval {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (p : ℂ[X]) :
    (∫ t : ℝ, p.eval (t : ℂ) ∂μ) = momentFunctional m p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, map_add]
    rw [integral_add (integrable_polynomial_eval hμ p)
      (integrable_polynomial_eval hμ q), hp, hq]
  | monomial n c =>
    simp only [eval_monomial, momentFunctional_monomial]
    rw [integral_const_mul, RepresentsHamburgerMoments.integral_complex_pow hμ]

lemma eval_conjugate_real (p : ℂ[X]) (t : ℝ) :
    (p.map (starRingEnd ℂ)).eval (t : ℂ) = star (p.eval (t : ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c => simp

lemma memLp_polynomial_eval {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (p : ℂ[X]) :
    MemLp (fun t : ℝ => p.eval (t : ℂ)) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
  have hi := (integrable_polynomial_eval hμ (p.map (starRingEnd ℂ) * p)).re
  convert hi using 1
  ext t
  simp only [eval_mul, eval_conjugate_real]
  simpa only [RCLike.inner_apply, starRingEnd_apply, mul_comm] using
    (norm_sq_eq_re_inner (𝕜 := ℂ) (p.eval (t : ℂ)))

/-- This map uses the moment quotient, so null polynomials cause no restriction. -/
def polynomialEvaluationL2 {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (h : HankelNonnegative m) :
    MomentPolynomials m h →ₗ[ℂ] Lp ℂ 2 μ where
  toFun p := (memLp_polynomial_eval hμ (rawPolynomial p)).toLp
    (fun t : ℝ => (rawPolynomial p).eval (t : ℂ))
  map_add' p q := by
    apply Lp.ext
    filter_upwards [(memLp_polynomial_eval hμ (rawPolynomial (p + q))).coeFn_toLp,
      (memLp_polynomial_eval hμ (rawPolynomial p)).coeFn_toLp,
      (memLp_polynomial_eval hμ (rawPolynomial q)).coeFn_toLp,
      Lp.coeFn_add ((memLp_polynomial_eval hμ (rawPolynomial p)).toLp _)
        ((memLp_polynomial_eval hμ (rawPolynomial q)).toLp _)] with t ht hp hq ha
    rw [ht, ha]
    simp only [Pi.add_apply, hp, hq]
    exact eval_add
  map_smul' c p := by
    apply Lp.ext
    filter_upwards [(memLp_polynomial_eval hμ (rawPolynomial (c • p))).coeFn_toLp,
      (memLp_polynomial_eval hμ (rawPolynomial p)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_polynomial_eval hμ (rawPolynomial p)).toLp _)] with t ht hp hs
    simp only [RingHom.id_apply]
    rw [ht, hs]
    simp only [Pi.smul_apply, hp]
    change (c • rawPolynomial p).eval (t : ℂ) = c * (rawPolynomial p).eval (t : ℂ)
    simp

lemma polynomialEvaluationL2_inner {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (h : HankelNonnegative m)
    (p q : MomentPolynomials m h) :
    inner ℂ (polynomialEvaluationL2 hμ h p) (polynomialEvaluationL2 hμ h q) =
      momentForm m (rawPolynomial p) (rawPolynomial q) := by
  rw [L2.inner_def, momentForm, ← integral_polynomial_eval hμ]
  apply integral_congr_ae
  filter_upwards [(memLp_polynomial_eval hμ (rawPolynomial p)).coeFn_toLp,
    (memLp_polynomial_eval hμ (rawPolynomial q)).coeFn_toLp] with t hp hq
  change inner ℂ (((memLp_polynomial_eval hμ (rawPolynomial p)).toLp _) t)
    (((memLp_polynomial_eval hμ (rawPolynomial q)).toLp _) t) = _
  rw [hp, hq]
  simp only [eval_mul, eval_conjugate_real, RCLike.inner_apply, starRingEnd_apply, mul_comm]

lemma polynomialEvaluationL2_norm {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (h : HankelNonnegative m)
    (p : MomentPolynomials m h) :
    ‖polynomialEvaluationL2 hμ h p‖ = ‖polynomialClass m h p‖ := by
  have he : ‖polynomialEvaluationL2 hμ h p‖ ^ 2 = ‖polynomialClass m h p‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), polynomialEvaluationL2_inner]
    change RCLike.re (momentForm m p p) = _
    rw [← polynomialClass_inner m h p p]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (polynomialClass m h p)).symm
  nlinarith [norm_nonneg (polynomialEvaluationL2 hμ h p),
    norm_nonneg (polynomialClass m h p)]

/-- The canonical isometry into an arbitrary representing L² space. Surjectivity
is neither claimed nor needed. -/
def representingIsometry {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (h : HankelNonnegative m) :
    MomentHilbertSpace m h →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  (polynomialEvaluationL2 hμ h).extendOfIsometry (polynomialClass_dense m h)
    (polynomialEvaluationL2_norm hμ h)

@[simp] lemma representingIsometry_class {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (h : HankelNonnegative m)
    (p : MomentPolynomials m h) :
    representingIsometry hμ h (polynomialClass m h p) = polynomialEvaluationL2 hμ h p :=
  LinearMap.extendOfIsometry_eq _ _ _ p

lemma cauchyKernel_ne_zero {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    z - (t : ℂ) ≠ 0 := by
  intro he
  have := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at this
  exact hz this

lemma cauchyKernel_norm_le {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    ‖(z - (t : ℂ))⁻¹‖ ≤ |z.im|⁻¹ := by
  rw [norm_inv]
  apply inv_anti₀ (abs_pos.mpr hz)
  simpa using Complex.abs_im_le_norm (z - (t : ℂ))

lemma memLp_conjugate_cauchyKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    {z : ℂ} (hz : z.im ≠ 0) :
    MemLp (fun t : ℝ => star ((z - (t : ℂ))⁻¹)) 2 μ := by
  apply MemLp.of_bound (C := |z.im|⁻¹)
  · exact ((continuous_const.sub Complex.continuous_ofReal).inv₀
      (cauchyKernel_ne_zero hz) |>.star).aestronglyMeasurable
  · exact ae_of_all _ (fun t => by simpa only [norm_star] using cauchyKernel_norm_le hz t)

/-- A continuous functional whose values on polynomial vectors are the Cauchy
integrals of those polynomials. -/
def cauchyFunctional {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (h : HankelNonnegative m)
    (z : ℂ) (hz : z.im ≠ 0) : MomentHilbertSpace m h →L[ℂ] ℂ := by
  letI := hμ.1
  exact (innerSL ℂ ((memLp_conjugate_cauchyKernel μ hz).toLp _)).comp
    (representingIsometry hμ h).toContinuousLinearMap

lemma cauchyFunctional_class {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (h : HankelNonnegative m)
    (z : ℂ) (hz : z.im ≠ 0) (p : MomentPolynomials m h) :
    cauchyFunctional hμ h z hz (polynomialClass m h p) =
      ∫ t : ℝ, (z - (t : ℂ))⁻¹ * (rawPolynomial p).eval (t : ℂ) ∂μ := by
  letI := hμ.1
  change inner ℂ ((memLp_conjugate_cauchyKernel μ hz).toLp _)
    (representingIsometry hμ h (polynomialClass m h p)) = _
  rw [representingIsometry_class, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_conjugate_cauchyKernel μ hz).coeFn_toLp,
    (memLp_polynomial_eval hμ (rawPolynomial p)).coeFn_toLp] with t ht hp
  change inner ℂ (((memLp_conjugate_cauchyKernel μ hz).toLp _) t)
    (((memLp_polynomial_eval hμ (rawPolynomial p)).toLp _) t) = _
  rw [ht, hp]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_star, mul_comm]

/-- Multiplying by z − X cancels the resolvent kernel. Its integral is fixed
by the moments, even if polynomial vectors do not fill the representing L². -/
lemma cauchyFunctional_shift_class {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (h : HankelNonnegative m)
    (z : ℂ) (hz : z.im ≠ 0) (p : MomentPolynomials m h) :
    cauchyFunctional hμ h z hz
      (z • polynomialClass m h p - polynomialClass m h (multiplyX m h p)) =
      momentFunctional m (rawPolynomial p) := by
  rw [← map_smul, ← map_sub]
  rw [cauchyFunctional_class, ← integral_polynomial_eval hμ]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  change (z - (t : ℂ))⁻¹ *
    ((z • rawPolynomial p) - X * rawPolynomial p).eval (t : ℂ) = _
  simp only [eval_sub, eval_smul, smul_eq_mul, eval_mul, eval_X]
  rw [← sub_mul, inv_mul_cancel_left₀ (cauchyKernel_ne_zero hz t)]

end RepresentingMeasures

section Annihilator
open Unbounded
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A continuous linear functional vanishing on a nonreal shifted graph of an
essentially self-adjoint operator is zero. Graph closure avoids choosing a
sequence of polynomial resolvent approximants. -/
lemma functional_eq_zero_of_shift (S : Operator ℂ H H)
    (hS : SymmetryAndDeficienciesSpec.essentiallySelfAdjointValue S)
    (z : ℂ) (hz : z.im ≠ 0) (F : H →L[ℂ] ℂ)
    (hF : ∀ y : S.domain, F (z • (y : H) - S y) = 0) : F = 0 := by
  have hc : _root_.IsClosed {p : H × H | F (z • p.1 - p.2) = 0} :=
    isClosed_eq (F.continuous.comp
      ((continuous_const.smul continuous_fst).sub continuous_snd)) continuous_const
  have hs : (S.graph : Set (H × H)) ⊆ {p : H × H | F (z • p.1 - p.2) = 0} := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨a, rfl, rfl⟩ := S.mem_graph_iff.mp hxy
    exact hF a
  have hclosed := closure_minimal hs hc
  ext x
  obtain ⟨y, hy⟩ := selfAdjoint_shift_surjective S.closure hS.2.2 z hz x
  have hm : ((y : H), S.closure y) ∈ closure (S.graph : Set (H × H)) := by
    change ((y : H), S.closure y) ∈ S.graph.topologicalClosure
    rw [hS.2.1.graph_closure_eq_closure_graph]
    exact S.closure.mem_graph y
  have he := hclosed hm
  change F (z • (y : H) - S.closure y) = 0 at he
  simpa only [hy, zero_apply] using he

end Annihilator

/-- Essential self-adjointness fixes the Cauchy transform of every representing
measure, including measures for which polynomials are not dense in L². -/
theorem representing_cauchyTransform_eq (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hS : Unbounded.SymmetryAndDeficienciesSpec.essentiallySelfAdjointValue
      (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h))
    (μ ν : Measure ℝ) (hμ : RepresentsHamburgerMoments m μ)
    (hν : RepresentsHamburgerMoments m ν) (z : ℂ) (hz : z.im ≠ 0) :
    cauchyTransform μ z = cauchyTransform ν z := by
  let F := cauchyFunctional hμ h z hz - cauchyFunctional hν h z hz
  have hF : F = 0 := by
    apply functional_eq_zero_of_shift _ hS z hz F
    intro y
    obtain ⟨p, hp⟩ := y.property
    have hval : PolynomialMomentHilbertSpaceSpec.multiplicationValue m h y =
        polynomialClass m h (multiplyX m h p) := by
      have hy : y = ⟨polynomialClass m h p, LinearMap.mem_range_self _ p⟩ :=
        Subtype.ext hp.symm
      rw [hy]
      exact minimalMultiplication_apply m h p
    change cauchyFunctional hμ h z hz (z • (y : MomentHilbertSpace m h) - _) -
      cauchyFunctional hν h z hz (z • (y : MomentHilbertSpace m h) - _) = 0
    rw [hval, ← hp, cauchyFunctional_shift_class, cauchyFunctional_shift_class, sub_self]
  have he := congrArg (fun G : MomentHilbertSpace m h →L[ℂ] ℂ =>
    G (polynomialClass m h 1)) hF
  change cauchyFunctional hμ h z hz (polynomialClass m h 1) -
    cauchyFunctional hν h z hz (polynomialClass m h 1) = 0 at he
  rw [cauchyFunctional_class, cauchyFunctional_class] at he
  have he := sub_eq_zero.mp he
  change (∫ t : ℝ, (z - (t : ℂ))⁻¹ * (1 : Polynomial ℂ).eval (t : ℂ) ∂μ) =
    (∫ t : ℝ, (z - (t : ℂ))⁻¹ * (1 : Polynomial ℂ).eval (t : ℂ) ∂ν) at he
  simpa only [Polynomial.eval_one, mul_one, cauchyTransform] using he

/-- Uniqueness is among all representing positive measures and includes zero mass. -/
theorem determinate_of_essentiallySelfAdjoint (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hS : Unbounded.SymmetryAndDeficienciesSpec.essentiallySelfAdjointValue
      (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h)) : Determinate m := by
  obtain ⟨μ, hμ⟩ := (hamburger_existence m).1.mp ((hankelNonnegative_iff_finite m).mp h)
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  letI := hμ.1
  letI := hν.1
  exact cauchy_transform_injectivity ν μ (representing_cauchyTransform_eq m h hS ν μ hν hμ)

section CyclicResolvents
open Polynomial PolynomialMomentHilbertSpaceSpec Unbounded

/-- Ordinary polynomials mapped into the same canonical moment completion. -/
private abbrev polyVector (m : ℕ → ℝ) (h : HankelNonnegative m) :
    ℂ[X] →ₗ[ℂ] MomentHilbertSpace m h := polynomialClass m h

lemma minimalMultiplication_poly (m : ℕ → ℝ) (h : HankelNonnegative m) (p : ℂ[X]) :
    (multiplicationValue m h) ⟨polyVector m h p, LinearMap.mem_range_self _ _⟩ =
      polyVector m h (X * p) :=
  minimalMultiplication_apply m h (ofPolynomial p)

/-- A deficiency vector is determined by its coefficient against the constant
polynomial. This proof also applies to degenerate moment spaces. -/
lemma deficiency_vector_eq_zero (m : ℕ → ℝ) (h : HankelNonnegative m)
    (z : ℂ) (y : MomentHilbertSpace m h)
    (hy : y ∈ deficiencySpace (multiplicationValue m h) z)
    (he : inner ℂ (constantValue m h) y = 0) : y = 0 := by
  obtain ⟨hyd, hyv⟩ := (mem_deficiencySpace_iff _ z y).mp hy
  have hstep (p : ℂ[X]) : inner ℂ (polyVector m h (X * p)) y =
      z * inner ℂ (polyVector m h p) y := by
    rw [← minimalMultiplication_poly]
    rw [hilbertAdjoint_inner _ (minimalMultiplication_dense m h) ⟨y, hyd⟩,
      hyv, inner_smul_right]
  have hpoly (p : ℂ[X]) : inner ℂ (polyVector m h p) y = 0 := by
    induction p using Polynomial.induction_on with
    | C c =>
      have hc : (C c : ℂ[X]) = c • (1 : ℂ[X]) := by
        rw [← C_mul', mul_one]
      rw [hc, map_smul]
      change inner ℂ (c • constantValue m h) y = 0
      exact (inner_smul_left (𝕜 := ℂ) (constantValue m h) y c).trans
        (by rw [he, mul_zero])
    | add p q hp hq => rw [map_add, inner_add_left, hp, hq, add_zero]
    | monomial n c ih =>
      have hp : (C c * X ^ (n + 1) : ℂ[X]) = X * (C c * X ^ n) := by ring
      rw [hp, hstep, ih, mul_zero]
  have hall : ∀ x : MomentHilbertSpace m h, inner ℂ x y = 0 := by
    intro x
    exact (polynomialClass_dense m h).induction_on x
      (p := fun x => inner ℂ x y = 0)
      (isClosed_eq (by fun_prop) continuous_const)
      (fun p => hpoly (rawPolynomial p))
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp (hall y)

/-- Two resolvents of extensions coincide if their constant-vector scalar
coefficients coincide. Cyclicity is proved from polynomial multiplication. -/
lemma extension_eq_of_resolvent_coefficient (m : ℕ → ℝ) (h : HankelNonnegative m)
    (A B : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h))
    (hA : Unbounded.IsSelfAdjoint A) (hB : Unbounded.IsSelfAdjoint B)
    (hSA : multiplicationValue m h ≤ A) (hSB : multiplicationValue m h ≤ B)
    (z : ℂ) (R : ResolventInverse A z) (Q : ResolventInverse B z)
    (he : inner ℂ (constantValue m h) (R.inverse (constantValue m h)) =
      inner ℂ (constantValue m h) (Q.inverse (constantValue m h))) : A = B := by
  have hs : IsSymmetric (multiplicationValue m h) := by
    exact ⟨minimalMultiplication_dense m h,
      LinearPMap.IsFormalAdjoint.le_adjoint (minimalMultiplication_dense m h)
        (minimalMultiplication_symmetric m h)⟩
  have hAa : A ≤ hilbertAdjoint (multiplicationValue m h) :=
    symmetric_extension_le_adjoint _ A hs ⟨hA.1, hA.2.le⟩ hSA
  have hBa : B ≤ hilbertAdjoint (multiplicationValue m h) :=
    symmetric_extension_le_adjoint _ B hs ⟨hB.1, hB.2.le⟩ hSB
  let e := constantValue m h
  let u : (hilbertAdjoint (multiplicationValue m h)).domain :=
    ⟨R.inverse e, hAa.1 (R.mem_domain e)⟩
  let v : (hilbertAdjoint (multiplicationValue m h)).domain :=
    ⟨Q.inverse e, hBa.1 (Q.mem_domain e)⟩
  have hu : hilbertAdjoint (multiplicationValue m h) u = A ⟨R.inverse e, R.mem_domain e⟩ :=
    (hAa.2 rfl).symm
  have hv : hilbertAdjoint (multiplicationValue m h) v = B ⟨Q.inverse e, Q.mem_domain e⟩ :=
    (hBa.2 rfl).symm
  have hdef : R.inverse e - Q.inverse e ∈ deficiencySpace (multiplicationValue m h) z := by
    apply (mem_deficiencySpace_iff _ z _).mpr
    refine ⟨(u - v).property, ?_⟩
    change hilbertAdjoint (multiplicationValue m h) (u - v) = _
    rw [LinearPMap.map_sub, hu, hv]
    have hr := R.right_inverse e
    have hq := Q.right_inverse e
    rw [smul_sub]
    have hr' : A ⟨R.inverse e, R.mem_domain e⟩ = z • R.inverse e - e := by
      rw [eq_sub_iff_add_eq]
      rw [sub_eq_iff_eq_add] at hr
      rw [hr, add_comm]
    have hq' : B ⟨Q.inverse e, Q.mem_domain e⟩ = z • Q.inverse e - e := by
      rw [eq_sub_iff_add_eq]
      rw [sub_eq_iff_eq_add] at hq
      rw [hq, add_comm]
    rw [hr', hq']
    module
  have heq : R.inverse e = Q.inverse e := by
    apply sub_eq_zero.mp
    apply deficiency_vector_eq_zero m h z _ hdef
    rw [inner_sub_right]
    exact sub_eq_zero.mpr he
  have hstepA (p : ℂ[X]) : R.inverse (polyVector m h (X * p)) =
      z • R.inverse (polyVector m h p) - polyVector m h p := by
    let x : (multiplicationValue m h).domain :=
      ⟨polyVector m h p, LinearMap.mem_range_self _ _⟩
    have ha : A ⟨(x : MomentHilbertSpace m h), hSA.1 x.property⟩ =
        polyVector m h (X * p) := (hSA.2 rfl).symm.trans (minimalMultiplication_poly m h p)
    have hr := R.left_inverse ⟨(x : MomentHilbertSpace m h), hSA.1 x.property⟩
    rw [ha, map_sub, map_smul] at hr
    apply eq_sub_iff_add_eq.mpr
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hr).symm
  have hstepB (p : ℂ[X]) : Q.inverse (polyVector m h (X * p)) =
      z • Q.inverse (polyVector m h p) - polyVector m h p := by
    let x : (multiplicationValue m h).domain :=
      ⟨polyVector m h p, LinearMap.mem_range_self _ _⟩
    have ha : B ⟨(x : MomentHilbertSpace m h), hSB.1 x.property⟩ =
        polyVector m h (X * p) := (hSB.2 rfl).symm.trans (minimalMultiplication_poly m h p)
    have hr := Q.left_inverse ⟨(x : MomentHilbertSpace m h), hSB.1 x.property⟩
    rw [ha, map_sub, map_smul] at hr
    apply eq_sub_iff_add_eq.mpr
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hr).symm
  have hpoly (p : ℂ[X]) : R.inverse (polyVector m h p) = Q.inverse (polyVector m h p) := by
    induction p using Polynomial.induction_on with
    | C c =>
      have hc : (C c : ℂ[X]) = c • (1 : ℂ[X]) := by
        rw [← C_mul', mul_one]
      rw [hc, map_smul, map_smul, map_smul]
      exact congrArg (c • ·) heq
    | add p q hp hq => simp only [map_add, hp, hq]
    | monomial n c ih =>
      have hp : (C c * X ^ (n + 1) : ℂ[X]) = X * (C c * X ^ n) := by ring
      rw [hp, hstepA, hstepB, ih]
  have hRQ : R.inverse = Q.inverse := by
    apply DFunLike.coe_injective
    apply (polynomialClass_dense m h).equalizer R.inverse.continuous Q.inverse.continuous
    funext p
    exact hpoly (rawPolynomial p)
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    rintro ⟨x, y⟩ hxy
    obtain ⟨a, rfl, rfl⟩ := A.mem_graph_iff.mp hxy
    let t := z • (a : MomentHilbertSpace m h) - A a
    have ht : Q.inverse t = (a : MomentHilbertSpace m h) := by
      rw [← hRQ]; exact R.left_inverse a
    have hg := B.mem_graph ⟨Q.inverse t, Q.mem_domain t⟩
    have hq := Q.right_inverse t
    have hv : B ⟨Q.inverse t, Q.mem_domain t⟩ = A a := by
      conv_lhs at hq => lhs; rw [ht]
      dsimp [t] at hq
      exact sub_right_inj.mp hq
    rw [hv] at hg
    simpa only [ht] using hg
  · apply LinearPMap.le_of_le_graph
    rintro ⟨x, y⟩ hxy
    obtain ⟨a, rfl, rfl⟩ := B.mem_graph_iff.mp hxy
    let t := z • (a : MomentHilbertSpace m h) - B a
    have ht : R.inverse t = (a : MomentHilbertSpace m h) := by
      rw [hRQ]; exact Q.left_inverse a
    have hg := A.mem_graph ⟨R.inverse t, R.mem_domain t⟩
    have hr := R.right_inverse t
    have hv : A ⟨R.inverse t, R.mem_domain t⟩ = B a := by
      conv_lhs at hr => lhs; rw [ht]
      dsimp [t] at hr
      exact sub_right_inj.mp hr
    rw [hv] at hg
    simpa only [ht] using hg

end CyclicResolvents


section SpectralMeasures
open Unbounded SpectralMeasure MeasurableSpectralCalculus
open UnboundedNormalSpectralTheorem.SpectralRepresentation
open HamburgerExistenceProof PolynomialMomentHilbertSpaceSpec
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : ProjectionValuedMeasure ℝ H}

lemma bounded_cauchyKernel {z : ℂ} (hz : z.im ≠ 0) :
    SpectralMeasure.Spec.IsBoundedMeasurable (fun t : ℝ => (z - (t : ℂ))⁻¹) :=
  ⟨((continuous_const.sub Complex.continuous_ofReal).inv₀
    (cauchyKernel_ne_zero hz)).measurable, ⟨|z.im|⁻¹, cauchyKernel_norm_le hz⟩⟩

/-- The nonreal bounded spectral multiplier is a two-sided inverse on the
maximal real-coordinate domain. -/
lemma real_spectral_resolvent (C : BoundedRealization E) (z : ℂ) (hz : z.im ≠ 0) :
    ∃ R : ResolventInverse (measurableIntegral C (fun t : ℝ => (t : ℂ))) z,
      R.inverse = C.integral (fun t : ℝ => (z - (t : ℂ))⁻¹) := by
  let f : ℝ → ℂ := fun t => (t : ℂ)
  let g : ℝ → ℂ := fun t => (z - (t : ℂ))⁻¹
  have hg : SpectralMeasure.Spec.IsBoundedMeasurable g := bounded_cauchyKernel hz
  have hfg : f * g = z • g - (fun _ => 1) := by
    funext t
    change (t : ℂ) * (z - (t : ℂ))⁻¹ = z * (z - (t : ℂ))⁻¹ - 1
    field_simp [cauchyKernel_ne_zero hz t]
    ring
  have hb : SpectralMeasure.Spec.IsBoundedMeasurable (f * g) := by
    rw [hfg]
    exact BorelNormSpectrum.bounded_sub (hg.smul z) (BorelNormSpectrum.bounded_const 1)
  have hC : C.integral (f * g) = z • C.integral g - 1 := by
    rw [hfg, C.sub _ _ (hg.smul z) (BorelNormSpectrum.bounded_const 1),
      C.smul z _ hg, C.one]
  let T := measurableIntegral C f
  have hgraph (x : H) : (C.integral g x, C.integral (f * g) x) ∈ T.graph :=
    bounded_product_graph C Complex.continuous_ofReal.measurable hg hb x
  have hmem (x : H) : C.integral g x ∈ T.domain :=
    LinearPMap.mem_domain_of_mem_graph (hgraph x)
  have hact (x : H) : T ⟨C.integral g x, hmem x⟩ = C.integral (f * g) x :=
    T.mem_graph_snd_inj (T.mem_graph _) (hgraph x) rfl
  refine ⟨{
    inverse := C.integral g
    mem_domain := hmem
    right_inverse := ?_
    left_inverse := ?_ }, rfl⟩
  · intro x
    rw [hact, hC]
    change z • C.integral g x - (z • C.integral g x - x) = x
    module
  · intro x
    have hh := bounded_product_commutes C Complex.continuous_ofReal.measurable hg hb x
    rw [map_sub, map_smul, hh, hC]
    change z • C.integral g (x : H) - (z • C.integral g (x : H) - (x : H)) = (x : H)
    module

lemma spectral_resolvent_coefficient (C : BoundedRealization E)
    (A : Operator ℂ H H)
    (hCA : measurableIntegral C (fun t : ℝ => (t : ℂ)) = A)
    (z : ℂ) (hz : z.im ≠ 0) (e : H) :
    ∃ R : ResolventInverse A z,
      inner ℂ e (R.inverse e) = cauchyTransform (C.measure e) z := by
  subst A
  obtain ⟨R, hR⟩ := real_spectral_resolvent C z hz
  refine ⟨R, ?_⟩
  rw [hR]
  exact SpectralMoments.scalar_bounded C _ (bounded_cauchyKernel hz) e

/-- The scalar measure of any chosen self-adjoint extension represents the
moments. Keeping the chosen measure is needed to compare different extensions. -/
lemma spectral_measure_represents (m : ℕ → ℝ) (h : HankelNonnegative m)
    (A : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h))
    (hSA : multiplicationValue m h ≤ A) (hA : Unbounded.IsSelfAdjoint A)
    {E : ProjectionValuedMeasure ℝ (MomentHilbertSpace m h)} (C : BoundedRealization E)
    (hCA : measurableIntegral C (fun t : ℝ => (t : ℂ)) = A) :
    RepresentsHamburgerMoments m (C.measure (constantValue m h)) := by
  have hm := hamburger_extension_realizes m h A hSA hA
  rw [← hCA] at hm
  refine ⟨C.finite _, ?_, ?_⟩
  · intro n
    obtain ⟨he, _⟩ := hm.2 n
    have hp := SpectralMoments.power_integrable C Complex.continuous_ofReal.measurable n
      ⟨constantValue m h, he⟩
    simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs] using hp.norm
  · intro n
    obtain ⟨he, hev⟩ := hm.2 n
    have hp := (SpectralMoments.scalar_power C Complex.continuous_ofReal.measurable n
      ⟨constantValue m h, he⟩).symm.trans hev
    apply Complex.ofReal_injective
    simpa only [← Complex.ofReal_pow, integral_complex_ofReal] using hp

lemma selfAdjoint_extension_unique_of_determinate (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hd : Determinate m)
    (A B : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h))
    (hSA : multiplicationValue m h ≤ A) (hA : Unbounded.IsSelfAdjoint A)
    (hSB : multiplicationValue m h ≤ B) (hB : Unbounded.IsSelfAdjoint B) : A = B := by
  have hcA : A.IsClosed := by
    rw [hA.2]
    exact hilbertAdjoint_isClosed A hA.1
  have hcB : B.IsClosed := by
    rw [hB.2]
    exact hilbertAdjoint_isClosed B hB.1
  obtain ⟨⟨EA, C, hCA, _⟩, _⟩ :=
    UnboundedNormalSpectralTheorem.selfadjoint_spectral _ A hA.1 hcA hA.2.symm
  obtain ⟨⟨EB, D, hDB, _⟩, _⟩ :=
    UnboundedNormalSpectralTheorem.selfadjoint_spectral _ B hB.1 hcB hB.2.symm
  have hμ := spectral_measure_represents m h A hSA hA C hCA
  have hν := spectral_measure_represents m h B hSB hB D hDB
  have hmeasure : C.measure (constantValue m h) = D.measure (constantValue m h) :=
    hd.unique hμ hν
  obtain ⟨R, hR⟩ := spectral_resolvent_coefficient C A hCA Complex.I (by simp)
    (constantValue m h)
  obtain ⟨Q, hQ⟩ := spectral_resolvent_coefficient D B hDB Complex.I (by simp)
    (constantValue m h)
  apply extension_eq_of_resolvent_coefficient m h A B hA hB hSA hSB Complex.I R Q
  rw [hR, hQ, hmeasure]

end SpectralMeasures

section UniqueExtension
open Unbounded Unbounded.ClosedSymmetricExtensionsSpec
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Negating a full unitary extension parameter gives another self-adjoint
extension. If it is the same extension, both deficiency spaces vanish. -/
lemma selfAdjoint_of_unique_extension (S : Operator ℂ H H) (hc : S.IsClosed)
    (hs : IsSymmetric S) (A : Operator ℂ H H)
    (hSA : S ≤ A) (hA : Unbounded.IsSelfAdjoint A)
    (hunique : ∀ B : Operator ℂ H H, S ≤ B → Unbounded.IsSelfAdjoint B → B = A) :
    Unbounded.IsSelfAdjoint S := by
  have hcA : A.IsClosed := by
    rw [hA.2]
    exact hilbertAdjoint_isClosed A hA.1
  obtain ⟨p, hp, _⟩ := closedSymmetricExtension_classification S hc hs A hcA
    ⟨hA.1, hA.2.le⟩ hSA
  have hAp : Unbounded.IsSelfAdjoint (extensionValue S p) := hp ▸ hA
  obtain ⟨hfull, honto⟩ := (closedSymmetricExtension_selfAdjoint_iff S hc hs p).mp hAp
  let q : ExtensionParameter S := {
    initialSpace := p.initialSpace
    closed_initialSpace := p.closed_initialSpace
    isometry := {
      toLinearMap := -p.isometry.toLinearMap
      norm_map' := fun u => by
        change ‖-p.isometry u‖ = ‖u‖
        rw [norm_neg, p.isometry.norm_map] } }
  have hqonto : Function.Surjective q.isometry := by
    intro v
    obtain ⟨u, hu⟩ := honto (-v)
    refine ⟨u, ?_⟩
    change -p.isometry u = v
    rw [hu, neg_neg]
  have hq : Unbounded.IsSelfAdjoint (extensionValue S q) :=
    (closedSymmetricExtension_selfAdjoint_iff S hc hs q).mpr ⟨hfull, hqonto⟩
  have hpq : p = q := by
    apply closedSymmetricExtension_injective S hs
    exact hp.trans (hunique _ (le_closedSymmetricExtension S hs q) hq).symm
  have hpair : parameterPairSpace S p = parameterPairSpace S q :=
    congrArg (parameterPairSpace S) hpq
  have hzero (u : p.initialSpace) : u = 0 := by
    have hm : ((u : SymmetryAndDeficienciesSpec.deficiencyPlusValue S), p.isometry u) ∈
        parameterPairSpace S p := ⟨u, rfl⟩
    rw [hpair] at hm
    obtain ⟨v, hv⟩ := hm
    have hval : v = u := Subtype.ext (congrArg Prod.fst hv)
    have hw : -p.isometry u = p.isometry u := by
      have hv' := congrArg Prod.snd hv
      change -p.isometry v = p.isometry u at hv'
      rwa [hval] at hv'
    have hw2 : (2 : ℂ) • p.isometry u = 0 := by
      rw [two_smul, ← neg_eq_iff_add_eq_zero]
      exact hw
    have hz : p.isometry u = 0 := (smul_eq_zero.mp hw2).resolve_left (by norm_num)
    exact p.isometry.injective (hz.trans (map_zero _).symm)
  have hplus : deficiencyPlus S = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    let u : p.initialSpace := ⟨⟨x, hx⟩, by rw [hfull]; trivial⟩
    exact congrArg (fun v : p.initialSpace =>
      ((v : SymmetryAndDeficienciesSpec.deficiencyPlusValue S) : H)) (hzero u)
  have hminus : deficiencyMinus S = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    obtain ⟨u, hu⟩ := honto ⟨x, hx⟩
    rw [hzero u, map_zero] at hu
    exact (congrArg (fun v : SymmetryAndDeficienciesSpec.deficiencyMinusValue S => (v : H)) hu).symm
  exact (closed_symmetric_selfAdjoint_iff_deficiencies S hc hs).mpr ⟨hplus, hminus⟩

end UniqueExtension

/-- The main determinacy equivalence for the exact canonical polynomial operator. -/
theorem hamburger_determinacy : HamburgerDeterminacySpec.Determinacy := by
  intro m h
  constructor
  · intro hd
    have hs : Unbounded.IsSymmetric (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h) :=
      ⟨minimalMultiplication_dense m h,
        LinearPMap.IsFormalAdjoint.le_adjoint (minimalMultiplication_dense m h)
          (minimalMultiplication_symmetric m h)⟩
    refine ⟨hs.1, hs.isClosable, ?_⟩
    obtain ⟨A, hSA, hA⟩ := hamburger_polynomial_extension m h
    have hcA : A.IsClosed := by
      rw [hA.2]
      exact Unbounded.hilbertAdjoint_isClosed A hA.1
    have hCA : (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h).closure ≤ A := by
      apply LinearPMap.le_of_le_graph
      rw [← hs.isClosable.graph_closure_eq_closure_graph]
      exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hSA) hcA
    apply selfAdjoint_of_unique_extension _ hs.isClosable.closure_isClosed
      (HamburgerExistenceProof.symmetric_closure _ hs) A hCA hA
    intro B hCB hB
    exact selfAdjoint_extension_unique_of_determinate m h hd B A
      ((PolynomialMomentHilbertSpaceSpec.multiplicationValue m h).le_closure.trans hCB) hB hSA hA
  · exact determinate_of_essentiallySelfAdjoint m h

end ExpandedFA.Moments.HamburgerDeterminacy
