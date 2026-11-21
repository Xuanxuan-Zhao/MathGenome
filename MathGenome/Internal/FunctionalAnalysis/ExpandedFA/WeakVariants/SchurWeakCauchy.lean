import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.WeakVariants.SchurWeakCauchy
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.Schur
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
universe u v
namespace ExpandedFA.WeakVariants.SchurWeakCauchy

theorem weakCauchy_norm_convergence : Spec.WeakCauchyNormConvergence.{u} := by
  intro 𝕜 _ x hx
  exact cauchySeq_tendsto_of_complete
    (ExpandedFA.P1.Schur.l1_weakCauchy_normCauchy x hx)

/-- Only a countable set of dyadic points can be zeros of the sine. -/
lemma rademacher_sine_ne_zero_ae (n : ℕ) :
    ∀ᵐ t ∂intervalMeasure, Real.sin ((2 : ℝ) ^ (n+1) * Real.pi * t) ≠ 0 := by
  have hc : Set.Countable {t : ℝ | Real.sin ((2 : ℝ) ^ (n+1) * Real.pi * t) = 0} := by
    apply (Set.countable_range (fun k : ℤ => (k : ℝ) / (2 : ℝ) ^ (n+1))).mono
    intro t ht
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp ht
    refine ⟨k, ?_⟩
    have htwo : (2 : ℝ) ^ (n+1) ≠ 0 := by positivity
    apply (div_eq_iff htwo).mpr
    nlinarith [Real.pi_pos]
  have : NullSingletonClass intervalMeasure := by
    dsimp [intervalMeasure]; infer_instance
  exact hc.ae_notMem intervalMeasure

lemma rademacherReal_norm_ae (n : ℕ) :
    ∀ᵐ t ∂intervalMeasure, ‖rademacherReal n t‖ = 1 := by
  filter_upwards [rademacher_sine_ne_zero_ae n] with t ht
  unfold rademacherReal
  rcases lt_or_gt_of_ne ht with h | h <;> simp [h, not_lt_of_ge h.le]

lemma rademacher_norm_ae (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    ∀ᵐ t ∂intervalMeasure, ‖rademacher 𝕜 n t‖ = 1 := by
  simpa only [rademacher, RCLike.norm_ofReal, ← Real.norm_eq_abs] using
    rademacherReal_norm_ae n

theorem rademacher_norm_one : Spec.RademacherNorm.{u} := by
  intro 𝕜 _ n
  rw [rademacherLp, Lp.norm_toLp]
  have heq : eLpNorm (rademacher 𝕜 n) 1 intervalMeasure =
      eLpNorm (fun _ : ℝ => (1 : ℝ)) 1 intervalMeasure := by
    apply eLpNorm_congr_norm_ae (rademacher_memLp 𝕜 1 n).aestronglyMeasurable
      aestronglyMeasurable_const
    simpa using rademacher_norm_ae 𝕜 n
  rw [heq]
  simp [eLpNorm_const' (p := 1) (1 : ℝ) (by simp) (by simp)]

/-- The first half of the next function is a copy of the preceding function. -/
lemma rademacherReal_succ_half (n : ℕ) (t : ℝ) :
    rademacherReal (n+1) (t/2) = rademacherReal n t := by
  unfold rademacherReal
  have heq : (2 : ℝ) ^ (n+1+1) * Real.pi * (t/2) =
      (2 : ℝ) ^ (n+1) * Real.pi * t := by rw [pow_succ]; ring
  rw [heq]

/-- The second half is another copy, since the extra phase is an even multiple of π. -/
lemma rademacherReal_succ_half_add (n : ℕ) (t : ℝ) :
    rademacherReal (n+1) (t/2 + 1/2) = rademacherReal n t := by
  unfold rademacherReal
  have heq : (2 : ℝ) ^ (n+1+1) * Real.pi * (t/2 + 1/2) =
      (2 : ℝ) ^ (n+1) * Real.pi * t + (2^n : ℕ) * (2 * Real.pi) := by
    push_cast
    rw [pow_succ, pow_succ]
    ring
  rw [heq, Real.sin_add_nat_mul_two_pi]

lemma rademacherReal_zero_half {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    rademacherReal 0 (t/2) = 1 := by
  have hs : 0 < Real.sin (Real.pi * t) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1) (by nlinarith [Real.pi_pos, ht.2])
  have heq : (2 : ℝ) ^ (0+1) * Real.pi * (t/2) = Real.pi * t := by norm_num; ring
  unfold rademacherReal
  rw [heq]
  simp [hs]

lemma rademacherReal_zero_half_add {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    rademacherReal 0 (t/2+1/2) = -1 := by
  have hs : 0 < Real.sin (Real.pi * t) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1) (by nlinarith [Real.pi_pos, ht.2])
  have heq : (2 : ℝ) ^ (0+1) * Real.pi * (t/2+1/2) = Real.pi * t + Real.pi := by
    norm_num; ring
  unfold rademacherReal
  rw [heq, Real.sin_add_pi]
  simp [hs, not_lt_of_ge hs.le]

lemma intervalIntegrable_of_measurable_bounded {f : ℝ → ℝ}
    (hf : Measurable f) (hb : ∀ t, ‖f t‖ ≤ 1) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b).mono_fun'
    hf.aestronglyMeasurable
  exact Eventually.of_forall hb

/-- Split an integral into two copies of the unit interval. -/
lemma integral_halves (f : ℝ → ℝ)
    (hf : ∀ a b, IntervalIntegrable f volume a b) :
    (∫ t in (0 : ℝ)..1, f t) =
      (1/2 : ℝ) * (∫ t in (0 : ℝ)..1, f (t/2)) +
      (1/2 : ℝ) * (∫ t in (0 : ℝ)..1, f (t/2+1/2)) := by
  have hl := intervalIntegral.inv_smul_integral_comp_div_add (a := 0) (b := 1) f 2 0
  have hr := intervalIntegral.inv_smul_integral_comp_div_add (a := 0) (b := 1) f 2 (1/2)
  norm_num only [zero_div, zero_add, add_zero, one_div, one_div_add_one_div,
    Real.norm_eq_abs, smul_eq_mul] at hl hr
  have hh := intervalIntegral.integral_add_adjacent_intervals (hf 0 (1/2)) (hf (1/2) 1)
  rw [← hh, ← hl, ← hr]

lemma rademacherReal_product_integrable (m n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => rademacherReal m t * rademacherReal n t) volume a b := by
  apply intervalIntegrable_of_measurable_bounded
    ((rademacherReal_measurable m).mul (rademacherReal_measurable n))
  intro t
  change ‖rademacherReal m t * rademacherReal n t‖ ≤ 1
  rw [norm_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul (rademacherReal_norm_le m t)
      (rademacherReal_norm_le n t) (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

lemma integral_rademacherReal_zero_zero :
    (∫ t in (0 : ℝ)..1, rademacherReal 0 t * rademacherReal 0 t) = 1 := by
  rw [integral_halves _ (rademacherReal_product_integrable 0 0)]
  have hl : (∫ t in (0 : ℝ)..1, rademacherReal 0 (t/2) * rademacherReal 0 (t/2)) = 1 := by
    calc
      _ = ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
        intro t ht
        dsimp only
        rw [rademacherReal_zero_half ht]
        norm_num
      _ = 1 := by norm_num
  have hr : (∫ t in (0 : ℝ)..1,
      rademacherReal 0 (t/2+1/2) * rademacherReal 0 (t/2+1/2)) = 1 := by
    calc
      _ = ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
        intro t ht
        dsimp only
        rw [rademacherReal_zero_half_add ht]
        norm_num
      _ = 1 := by norm_num
  rw [hl, hr]
  norm_num

lemma integral_rademacherReal_zero_succ (n : ℕ) :
    (∫ t in (0 : ℝ)..1, rademacherReal 0 t * rademacherReal (n+1) t) = 0 := by
  rw [integral_halves _ (rademacherReal_product_integrable 0 (n+1))]
  have hl : (∫ t in (0 : ℝ)..1, rademacherReal 0 (t/2) * rademacherReal (n+1) (t/2)) =
      ∫ t in (0 : ℝ)..1, rademacherReal n t := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro t ht
    dsimp only
    rw [rademacherReal_zero_half ht, rademacherReal_succ_half, one_mul]
  have hr : (∫ t in (0 : ℝ)..1,
      rademacherReal 0 (t/2+1/2) * rademacherReal (n+1) (t/2+1/2)) =
      -(∫ t in (0 : ℝ)..1, rademacherReal n t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro t ht
    dsimp only
    rw [rademacherReal_zero_half_add ht, rademacherReal_succ_half_add, neg_one_mul]
  rw [hl, hr]
  ring

lemma integral_rademacherReal_succ_succ (m n : ℕ) :
    (∫ t in (0 : ℝ)..1, rademacherReal (m+1) t * rademacherReal (n+1) t) =
      ∫ t in (0 : ℝ)..1, rademacherReal m t * rademacherReal n t := by
  rw [integral_halves _ (rademacherReal_product_integrable (m+1) (n+1))]
  simp_rw [rademacherReal_succ_half, rademacherReal_succ_half_add]
  ring

/-- Orthogonality follows by stripping one common binary digit at a time. -/
lemma integral_rademacherReal_mul (m n : ℕ) :
    (∫ t in (0 : ℝ)..1, rademacherReal m t * rademacherReal n t) =
      if m = n then 1 else 0 := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => simpa using integral_rademacherReal_zero_zero
    | succ n => simpa using integral_rademacherReal_zero_succ n
  | succ m ih =>
    cases n with
    | zero => simpa only [mul_comm, Nat.succ_ne_zero, ite_false] using
        integral_rademacherReal_zero_succ m
    | succ n => simpa only [integral_rademacherReal_succ_succ, Nat.succ.injEq] using ih n

/-- The prescribed real-valued functions are orthonormal over either scalar field. -/
theorem rademacher_orthonormal (𝕜 : Type u) [RCLike 𝕜] :
    Orthonormal 𝕜 (rademacherLp 𝕜 2) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [L2.inner_def]
  calc
    _ = ∫ t, (RCLike.ofReal (rademacherReal m t * rademacherReal n t) : 𝕜)
        ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [(rademacher_memLp 𝕜 2 m).coeFn_toLp,
        (rademacher_memLp 𝕜 2 n).coeFn_toLp] with t hm hn
      change inner 𝕜 ((rademacher_memLp 𝕜 2 m).toLp (rademacher 𝕜 m) t)
        ((rademacher_memLp 𝕜 2 n).toLp (rademacher 𝕜 n) t) = _
      rw [hm, hn]
      simp only [rademacher, RCLike.inner_apply', RCLike.conj_ofReal, RCLike.ofReal_mul]
    _ = RCLike.ofReal (∫ t, rademacherReal m t * rademacherReal n t ∂intervalMeasure) :=
      integral_ofReal
    _ = RCLike.ofReal (∫ t in (0 : ℝ)..1, rademacherReal m t * rademacherReal n t) := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      rfl
    _ = if m = n then (1 : 𝕜) else 0 := by
      rw [integral_rademacherReal_mul]
      split_ifs <;> simp

/-- Bessel's inequality makes every continuous scalar-linear test of an
orthonormal sequence tend to zero. -/
theorem orthonormal_weakNull {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (v : ℕ → E) (hv : Orthonormal 𝕜 v) :
    ExpandedFA.P1.Schur.WeakConverges 𝕜 v 0 := by
  intro f
  let y := (InnerProductSpace.toDual 𝕜 E).symm f
  have hsquare : Tendsto (fun n => ‖f (v n)‖ ^ 2) atTop (𝓝 0) := by
    have hs := (hv.inner_products_summable y).tendsto_atTop_zero
    have heq (n : ℕ) : ‖inner 𝕜 (v n) y‖ = ‖f (v n)‖ := by
      rw [norm_inner_symm]
      exact congrArg norm (InnerProductSpace.toDual_symm_apply (𝕜 := 𝕜))
    simpa only [heq] using hs
  rw [map_zero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hsquare (ε^2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hs : ‖f (v n)‖ ^ 2 < ε ^ 2 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg ‖f (v n)‖)] using hN n hn
  rw [dist_zero_right]
  nlinarith [norm_nonneg (f (v n))]

/-- The ordinary inclusion keeps exactly the same a.e. class. -/
def l2ToL1Linear (𝕜 : Type u) [RCLike 𝕜] :
    Lp 𝕜 2 intervalMeasure →ₗ[𝕜] Lp 𝕜 1 intervalMeasure where
  toFun f := ⟨f.val, (Lp.antitone (by norm_num : (1 : ℝ≥0∞) ≤ 2)) f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma l2ToL1Linear_norm_le (𝕜 : Type u) [RCLike 𝕜] (f : Lp 𝕜 2 intervalMeasure) :
    ‖l2ToL1Linear 𝕜 f‖ ≤ ‖f‖ := by
  change (eLpNorm f 1 intervalMeasure).toReal ≤ (eLpNorm f 2 intervalMeasure).toReal
  apply ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
  exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

/-- L²→L¹ is continuous because the interval has total measure one. -/
def l2ToL1 (𝕜 : Type u) [RCLike 𝕜] :
    Lp 𝕜 2 intervalMeasure →L[𝕜] Lp 𝕜 1 intervalMeasure :=
  (l2ToL1Linear 𝕜).mkContinuous 1 (fun f => by
    simpa only [one_mul] using l2ToL1Linear_norm_le 𝕜 f)

@[simp] lemma l2ToL1_rademacher (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    l2ToL1 𝕜 (rademacherLp 𝕜 2 n) = rademacherLp 𝕜 1 n := by
  apply Lp.ext
  exact (rademacher_memLp 𝕜 2 n).coeFn_toLp.trans
    (rademacher_memLp 𝕜 1 n).coeFn_toLp.symm

theorem rademacher_weak_null : Spec.RademacherWeakNull.{u} := by
  intro 𝕜 _ f
  have hw := orthonormal_weakNull (rademacherLp 𝕜 2) (rademacher_orthonormal 𝕜)
    (f.comp (l2ToL1 𝕜))
  simpa only [ContinuousLinearMap.comp_apply, l2ToL1_rademacher, map_zero] using hw

theorem l1_weak_null_unit_sequence : Spec.L1WeakNullUnitSequence.{u} := by
  intro 𝕜 _
  exact ⟨rademacherLp 𝕜 1, rademacher_weak_null 𝕜, rademacher_norm_one 𝕜⟩

end ExpandedFA.WeakVariants.SchurWeakCauchy
