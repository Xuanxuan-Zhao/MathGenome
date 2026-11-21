import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaDerivativeBounds
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.GammaDefinition
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.UniformComparison
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Bounds for all logarithmic Gamma kernels. Near zero we dominate the
logarithmic power by a small negative power, and use the power-integral test.
At infinity the positive exponential series bounds a sufficiently large
integer power. Measure integrability is transferred to proper Darboux limits
on each endpoint, and the upstream uniform comparison theorem supplies
uniform signed and absolute convergence and bounds on the actual tails. -/
noncomputable section
namespace SingleVariableAnalysis
open Set Filter MeasureTheory
open scoped Topology
open Riemann Riemann.Improper
namespace GBSpec
export Specs.SingleVariableAnalysis.Ch18.GammaDerivativeBounds
  (kernelValue zeroMajorantValue infinityMajorant zeroBound infinityBound
    majorantConvergence absoluteConvergence uniformAtOrder uniformConvergence tailBounds uniformlySmallTails orderAndNext)
end GBSpec

def gammaLogKernel : ℕ → ℝ → ℝ → ℝ := GBSpec.kernelValue
def gammaZeroMajorant : ℝ → ℕ → ℝ → ℝ := GBSpec.zeroMajorantValue

namespace GammaBounds

theorem kernel_abs (k : ℕ) (s t : ℝ) (ht : 0 < t) :
    |gammaLogKernel k s t| = t ^ (s - 1) * |Real.log t| ^ k * Real.exp (-t) := by
  simp only [gammaLogKernel, GBSpec.kernelValue,
    Specs.SingleVariableAnalysis.Ch18.GammaDefinition.gammaKernelValue,
    abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _), abs_of_pos (Real.exp_pos _), abs_pow]
  ring

theorem kernel_continuous (k : ℕ) (s t : ℝ) (ht : 0 < t) :
    ContinuousAt (gammaLogKernel k s) t :=
  (gammaKernel_continuousAt s t ht).mul ((Real.continuousAt_log ht.ne').pow k)

theorem zero_continuous (α : ℝ) (k : ℕ) (t : ℝ) (ht : 0 < t) :
    ContinuousAt (gammaZeroMajorant α k) t :=
  (Real.continuousAt_rpow_const t (α - 1) (Or.inl ht.ne')).mul
    ((Real.continuousAt_log ht.ne').abs.pow k)

theorem zero_nonneg (α : ℝ) (k : ℕ) (t : ℝ) (ht : 0 < t) :
    0 ≤ gammaZeroMajorant α k t :=
  mul_nonneg (Real.rpow_nonneg ht.le _) (pow_nonneg (abs_nonneg _) _)

end GammaBounds

theorem gamma_log_zero_bound : GBSpec.zeroBound := by
  intro k α s t has ht ht1
  rw [← show gammaLogKernel k s t = GBSpec.kernelValue k s t from rfl,
    GammaBounds.kernel_abs k s t ht]
  change _ ≤ t ^ (α - 1) * |Real.log t| ^ k
  calc
    _ ≤ t ^ (α - 1) * |Real.log t| ^ k * 1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge ht ht1 (sub_le_sub_right has 1))
          (pow_nonneg (abs_nonneg _) k))
        (Real.exp_le_one_iff.mpr (by linarith)) (Real.exp_pos _).le
        (mul_nonneg (Real.rpow_nonneg ht.le _) (pow_nonneg (abs_nonneg _) k))
    _ = _ := mul_one _

namespace GammaBounds

/-- A positive exponential bounds every integer power, with an explicit constant. -/
theorem pow_exp_bound (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    t ^ m * Real.exp (-t) ≤ ((2 : ℝ) ^ m * (m.factorial : ℝ)) * Real.exp (-t / 2) := by
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (t / 2) (by positivity : 0 ≤ t / 2) m)
  have hp : t ^ m ≤ (2 : ℝ) ^ m * ((m.factorial : ℝ) * Real.exp (t / 2)) := by
    rw [div_pow] at h
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    have h' := (div_le_iff₀ h2).mp h
    nlinarith [h']
  have he : Real.exp (t / 2) * Real.exp (-t) = Real.exp (-t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (2 : ℝ) ^ m * ((m.factorial : ℝ) * Real.exp (t / 2)) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, mul_assoc, he]; ring

end GammaBounds

theorem gamma_log_infinity_bound : GBSpec.infinityBound := by
  intro k β
  obtain ⟨m, hm⟩ := exists_nat_gt (β - 1 + (k : ℝ))
  refine ⟨(2 : ℝ) ^ m * (m.factorial : ℝ), by positivity, ?_⟩
  intro s t hs ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [← show gammaLogKernel k s t = GBSpec.kernelValue k s t from rfl,
    GammaBounds.kernel_abs k s t ht0]
  have hl : |Real.log t| ≤ t := by
    rw [abs_of_nonneg (Real.log_nonneg ht)]
    exact (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  calc
    _ ≤ t ^ (s - 1) * t ^ k * Real.exp (-t) := by gcongr
    _ = t ^ (s - 1 + (k : ℝ)) * Real.exp (-t) := by
      rw [Real.rpow_add ht0, Real.rpow_natCast]
    _ ≤ t ^ (m : ℝ) * Real.exp (-t) := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le ht (by linarith)) (Real.exp_pos _).le
    _ = t ^ m * Real.exp (-t) := by rw [Real.rpow_natCast]
    _ ≤ _ := GammaBounds.pow_exp_bound m t ht0.le

namespace GammaBounds

/-- Convert continuity on regular positive intervals to the proper Darboux
regularity used by the endpoint predicates. -/
theorem left_regular {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, 0 < t → ContinuousAt f t) :
    LeftRegular .real f (0 : WithBot ℝ) 1 :=
  ⟨WithBot.coe_lt_coe.mpr zero_lt_one, fun t =>
    (positive_continuous_darboux hf
      (WithBot.coe_lt_coe.mp t.property.1) t.property.2.le).choose⟩

theorem right_regular {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, 0 < t → ContinuousAt f t) :
    RightRegular .real f 1 ⊤ :=
  ⟨WithTop.coe_lt_top _, fun t =>
    (positive_continuous_darboux hf zero_lt_one t.property.1.le).choose⟩

/-- Only integrability at the left endpoint is needed for this bridge. -/
theorem left_converges {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, 0 < t → ContinuousAt f t)
    (hi : IntegrableOn f (Ioc 0 1)) :
    LeftConverges .real f (0 : WithBot ℝ) 1 := by
  have h01 : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hi
  have h01' : IntegrableOn f (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp h01
  have hl : Tendsto (fun t : ℝ => ∫ x in t..1, f x)
      (𝓝[>] 0) (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
    have hc := (intervalIntegral.continuousOn_primitive_interval_left h01') 0
      (show (0 : ℝ) ∈ uIcc (0 : ℝ) 1 from left_mem_uIcc)
    change Tendsto _ (𝓝[uIcc (0 : ℝ) 1] 0) _ at hc
    rw [uIcc_of_le zero_le_one, nhdsWithin_Icc_eq_nhdsGE zero_lt_one] at hc
    exact hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  refine ⟨_, PTest.left_has_of_tendsto (left_regular hf) ?_ hl⟩
  intro t
  exact (positive_continuous_darboux hf
    (WithBot.coe_lt_coe.mp t.property.1) t.property.2.le).choose_spec

/-- The right endpoint bridge is independent of behavior at zero. -/
theorem right_converges {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, 0 < t → ContinuousAt f t)
    (hi : IntegrableOn f (Ioi 1)) : RightConverges .real f 1 ⊤ := by
  refine ⟨_, PTest.right_has_of_tendsto (right_regular hf) ?_
    (intervalIntegral_tendsto_integral_Ioi 1 hi tendsto_id)⟩
  intro t
  exact (positive_continuous_darboux hf zero_lt_one t.property.1.le).choose_spec

theorem zero_integrable (α : ℝ) (k : ℕ) (hα : 0 < α) :
    IntegrableOn (gammaZeroMajorant α k) (Ioc 0 1) := by
  change IntegrableOn (fun t : ℝ => t ^ (α - 1) * |Real.log t| ^ k) (Ioc 0 1)
  let ε : ℝ := α / (2 * ((k : ℝ) + 1))
  have hε : 0 < ε := div_pos hα (by positivity)
  have hk : ε * (k : ℝ) < α := by
    dsimp [ε]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2 * ((k : ℝ) + 1))]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hp : -1 < α - 1 + -ε * (k : ℝ) := by linarith
  have hi : IntegrableOn (fun t : ℝ => (ε ^ k)⁻¹ * t ^ (α - 1 + -ε * (k : ℝ))) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' hp)).const_mul _
  have hc : ContinuousOn (fun t : ℝ => t ^ (α - 1) * |Real.log t| ^ k) (Ioc 0 1) := by
    intro t ht
    exact ((Real.continuousAt_rpow_const t (α - 1) (Or.inl ht.1.ne')).mul
      ((Real.continuousAt_log ht.1.ne').abs.pow k)).continuousWithinAt
  apply hi.mono' (hc.aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hl : |Real.log t| ≤ t ^ (-ε) / ε := by
    rw [abs_of_nonpos (Real.log_nonpos ht.1.le ht.2)]
    simpa only [neg_div, neg_neg] using neg_le_neg (Real.neg_rpow_div_le_log ht.1.le hε)
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (pow_nonneg (abs_nonneg _) k))]
  calc
    _ ≤ t ^ (α - 1) * (t ^ (-ε) / ε) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hl k) (Real.rpow_nonneg ht.1.le _)
    _ = (ε ^ k)⁻¹ * t ^ (α - 1 + -ε * (k : ℝ)) := by
      rw [div_pow, div_eq_mul_inv, ← Real.rpow_mul_natCast ht.1.le, mul_left_comm,
        ← mul_assoc, ← Real.rpow_add ht.1]
      rw [add_comm (-ε * (k : ℝ))]
      exact mul_comm _ _


theorem infinity_continuous (C t : ℝ) : ContinuousAt (GBSpec.infinityMajorant C) t :=
  (Real.continuous_exp.comp (continuous_neg.div_const 2)).continuousAt.const_mul C

theorem infinity_integrable (C : ℝ) : IntegrableOn (GBSpec.infinityMajorant C) (Ioi 1) := by
  have h : IntegrableOn (fun t : ℝ => C * Real.exp ((-1 / 2 : ℝ) * t)) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) (1 : ℝ)).const_mul C
  apply h.congr_fun _ measurableSet_Ioi
  intro t _
  dsimp [GBSpec.infinityMajorant]
  congr 2
  ring

end GammaBounds

theorem gamma_log_majorants_converge : GBSpec.majorantConvergence := by
  constructor
  · intro α k hα
    exact GammaBounds.left_converges (GammaBounds.zero_continuous α k)
      (GammaBounds.zero_integrable α k hα)
  · intro C
    exact GammaBounds.right_converges (fun t _ => GammaBounds.infinity_continuous C t)
      (GammaBounds.infinity_integrable C)

namespace GammaBounds

theorem left_family_regular {T : Type*} (f : ℝ → T → ℝ)
    (hf : ∀ s t, 0 < t → ContinuousAt (fun x => f x s) t) :
    LeftFamilyRegular .real T f (0 : WithBot ℝ) 1 :=
  ⟨WithBot.coe_lt_coe.mpr zero_lt_one, fun s => left_regular (hf s)⟩

theorem right_family_regular {T : Type*} (f : ℝ → T → ℝ)
    (hf : ∀ s t, 0 < t → ContinuousAt (fun x => f x s) t) :
    RightFamilyRegular .real T f 1 ⊤ :=
  ⟨WithTop.coe_lt_top _, fun s => right_regular (hf s)⟩

end GammaBounds

theorem gamma_log_uniform_convergence : GBSpec.uniformConvergence := by
  intro k α β hα _hαβ
  have hzg := gamma_log_majorants_converge.1 α k hα
  obtain ⟨C, _hC, hCdom⟩ := gamma_log_infinity_bound k β
  have hig := gamma_log_majorants_converge.2 C
  have hl : ∀ t : ℝ, (0 : WithBot ℝ) < (t : WithBot ℝ) → t ≤ 1 →
      ∀ s : Icc α β, ‖gammaLogKernel k s.val t‖ ≤ gammaZeroMajorant α k t := by
    intro t ht ht1 s
    exact gamma_log_zero_bound k α s.val t s.property.1 (WithBot.coe_lt_coe.mp ht) ht1
  have hr : ∀ t : ℝ, 1 ≤ t → (t : WithTop ℝ) < ⊤ →
      ∀ s : Icc α β, ‖gammaLogKernel k s.val t‖ ≤ GBSpec.infinityMajorant C t := by
    intro t ht _ s
    exact hCdom s.val t s.property.2 ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact left_uniform_converges_of_majorant .real (Icc α β)
      (fun t s => gammaLogKernel k s.val t) (gammaZeroMajorant α k) le_rfl
      (GammaBounds.left_family_regular _ (fun s => GammaBounds.kernel_continuous k s.val)) hzg hl
  · exact right_uniform_converges_of_majorant .real (Icc α β)
      (fun t s => gammaLogKernel k s.val t) (GBSpec.infinityMajorant C) le_rfl
      (GammaBounds.right_family_regular _ (fun s => GammaBounds.kernel_continuous k s.val)) hig hr
  · apply left_uniform_converges_of_majorant .real (Icc α β)
      (fun t s => (|gammaLogKernel k s.val t| : ℝ)) (gammaZeroMajorant α k) le_rfl
      (GammaBounds.left_family_regular _ (fun s t ht => (GammaBounds.kernel_continuous k s.val t ht).abs)) hzg
    intro t ht ht1 s
    change |(|gammaLogKernel k s.val t| : ℝ)| ≤ gammaZeroMajorant α k t
    rw [abs_abs]
    exact hl t ht ht1 s
  · apply right_uniform_converges_of_majorant .real (Icc α β)
      (fun t s => (|gammaLogKernel k s.val t| : ℝ)) (GBSpec.infinityMajorant C) le_rfl
      (GammaBounds.right_family_regular _ (fun s t ht => (GammaBounds.kernel_continuous k s.val t ht).abs)) hig
    intro t ht htTop s
    change |(|gammaLogKernel k s.val t| : ℝ)| ≤ GBSpec.infinityMajorant C t
    rw [abs_abs]
    exact hr t ht htTop s

theorem gamma_log_absolute_convergence : GBSpec.absoluteConvergence := by
  intro k s hs
  obtain ⟨_, _, ⟨L, hL⟩, ⟨R, hR⟩⟩ := gamma_log_uniform_convergence k s s hs le_rfl
  let s' : Icc s s := ⟨s, le_rfl, le_rfl⟩
  exact ⟨⟨L s', left_uniform_pointwise .real (Icc s s) _ _ _ _ hL s'⟩,
    ⟨R s', right_uniform_pointwise .real (Icc s s) _ _ _ _ hR s'⟩⟩

theorem gamma_log_order_and_next : GBSpec.orderAndNext := by
  intro k α β hα hαβ
  exact ⟨gamma_log_uniform_convergence k α β hα hαβ,
    gamma_log_uniform_convergence (k + 1) α β hα hαβ⟩

theorem gamma_log_tail_bounds : GBSpec.tailBounds := by
  intro k α β hα _hαβ
  obtain ⟨C, hC, hCdom⟩ := gamma_log_infinity_bound k β
  let f : ℝ → Icc α β → ℝ := fun t s => |gammaLogKernel k s.val t|
  have hfL : LeftFamilyRegular .real (Icc α β) f (0 : WithBot ℝ) 1 :=
    GammaBounds.left_family_regular f (fun s t ht => (GammaBounds.kernel_continuous k s.val t ht).abs)
  have hfR : RightFamilyRegular .real (Icc α β) f 1 ⊤ :=
    GammaBounds.right_family_regular f (fun s t ht => (GammaBounds.kernel_continuous k s.val t ht).abs)
  have hdomL : ∀ x : ℝ, (0 : WithBot ℝ) < (x : WithBot ℝ) → x ≤ 1 →
      ∀ s : Icc α β, ‖f x s‖ ≤ gammaZeroMajorant α k x := by
    intro x hx hx1 s
    change |(|gammaLogKernel k s.val x| : ℝ)| ≤ gammaZeroMajorant α k x
    rw [abs_abs]
    exact gamma_log_zero_bound k α s.val x s.property.1 (WithBot.coe_lt_coe.mp hx) hx1
  have hdomR : ∀ x : ℝ, 1 ≤ x → (x : WithTop ℝ) < ⊤ →
      ∀ s : Icc α β, ‖f x s‖ ≤ GBSpec.infinityMajorant C x := by
    intro x hx _ s
    change |(|gammaLogKernel k s.val x| : ℝ)| ≤ GBSpec.infinityMajorant C x
    rw [abs_abs]
    exact hCdom s.val x s.property.2 hx
  obtain ⟨_, _, hL⟩ := left_uniform_comparison .real (Icc α β) f
    (gammaZeroMajorant α k) (0 : WithBot ℝ) 1 1 le_rfl
    (WithBot.coe_lt_coe.mpr zero_lt_one) hfL (gamma_log_majorants_converge.1 α k hα)
    (fun x hx _ => GammaBounds.zero_nonneg α k x (WithBot.coe_lt_coe.mp hx)) hdomL
  obtain ⟨_, _, hR⟩ := right_uniform_comparison .real (Icc α β) f
    (GBSpec.infinityMajorant C) 1 1 ⊤ le_rfl (WithTop.coe_lt_top _) hfR
    (gamma_log_majorants_converge.2 C)
    (fun x _ _ => mul_nonneg hC.le (Real.exp_pos _).le) hdomR
  refine ⟨C, hC, ?_, ?_⟩
  · intro η hη hη1
    obtain ⟨G, H, hG, hG0, hH, _⟩ := hL η (WithBot.coe_lt_coe.mpr hη) hη1
    refine ⟨G, hG0, hG, fun s hs => ?_⟩
    let s' : Icc α β := ⟨s, hs⟩
    refine ⟨H s', (hH s').1, ?_, ?_⟩
    · exact left_hasIntegral_nonneg (fun t => f t s') (hH s').1
        (fun x _ _ => (show (0 : ℝ) ≤ |gammaLogKernel k s x| from abs_nonneg _))
    · change (show ℝ from H s') ≤ G
      have hb : |(show ℝ from H s')| ≤ G := (hH s').2
      exact (le_abs_self (show ℝ from H s')).trans hb
  · intro R hR1
    obtain ⟨G, H, hG, hG0, hH, _⟩ := hR R hR1 (WithTop.coe_lt_top _)
    refine ⟨G, hG0, hG, fun s hs => ?_⟩
    let s' : Icc α β := ⟨s, hs⟩
    refine ⟨H s', (hH s').1, ?_, ?_⟩
    · exact right_hasIntegral_nonneg (fun t => f t s') (hH s').1
        (fun x _ _ => (show (0 : ℝ) ≤ |gammaLogKernel k s x| from abs_nonneg _))
    · change (show ℝ from H s') ≤ G
      have hb : |(show ℝ from H s')| ≤ G := (hH s').2
      exact (le_abs_self (show ℝ from H s')).trans hb

namespace GammaBounds

/-- A convergent left improper integral has small actual tails; the proof
uses only the proper Cauchy criterion and one approximation to each tail limit. -/
theorem left_small_tails {g : ℝ → ℝ}
    (hg : LeftConverges .real g (0 : WithBot ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ η : ℝ, 0 < η → η < δ →
      ∀ G : ℝ, LeftHasIntegral .real g (0 : WithBot ℝ) η G → |G| < ε := by
  obtain ⟨A, hA⟩ := hg
  obtain ⟨r, hr⟩ := (left_cauchy_criterion .real g (0 : WithBot ℝ) 1 hA.1).mp ⟨A, hA⟩
    (ε / 2) (by positivity)
  refine ⟨r.val, WithBot.coe_lt_coe.mp r.property.1, r.property.2, ?_⟩
  intro η hη hηr G hG
  obtain ⟨u, hu⟩ := hG.2 (ε / 2) (by positivity)
  obtain ⟨t, htu, _⟩ := left_earlier u u
  let t' : LeftIndex (0 : WithBot ℝ) 1 :=
    ⟨t.val, t.property.1, t.property.2.trans (hηr.trans r.property.2)⟩
  let η' : LeftIndex (0 : WithBot ℝ) 1 :=
    ⟨η, WithBot.coe_lt_coe.mpr hη, hηr.trans r.property.2⟩
  obtain ⟨htη, hsmall⟩ := hr t' η' t.property.2 hηr
  let I : ℝ := realIntegral g htη
  have hI : |I| < ε / 2 := hsmall
  have happ : |I - G| < ε / 2 := by
    have hh := hu t htu
    change |(show ℝ from LeftTruncation .real g (0 : WithBot ℝ) η hG.1 t) - G| < ε / 2 at hh
    exact hh
  have htri := norm_sub_norm_le G I
  simp only [Real.norm_eq_abs, abs_sub_comm G I] at htri
  linarith

/-- The large-endpoint version has its own cutoff and does not use the
behavior at zero. -/
theorem right_small_tails {g : ℝ → ℝ}
    (hg : RightConverges .real g 1 ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 1 < R₀ ∧ ∀ R : ℝ, R₀ < R →
      ∀ G : ℝ, RightHasIntegral .real g R ⊤ G → |G| < ε := by
  obtain ⟨A, hA⟩ := hg
  obtain ⟨r, hr⟩ := (right_cauchy_criterion .real g 1 ⊤ hA.1).mp ⟨A, hA⟩
    (ε / 2) (by positivity)
  refine ⟨r.val, r.property.1, ?_⟩
  intro R hrR G hG
  obtain ⟨u, hu⟩ := hG.2 (ε / 2) (by positivity)
  obtain ⟨t, hut, _⟩ := right_later u u
  let R' : RightIndex 1 ⊤ := ⟨R, r.property.1.trans hrR, WithTop.coe_lt_top _⟩
  let t' : RightIndex 1 ⊤ := ⟨t.val, R'.property.1.trans t.property.1, WithTop.coe_lt_top _⟩
  obtain ⟨hRt, hsmall⟩ := hr R' t' hrR t.property.1
  let I : ℝ := realIntegral g hRt
  have hI : |I| < ε / 2 := hsmall
  have happ : |I - G| < ε / 2 := by
    have hh := hu t hut
    change |(show ℝ from RightTruncation .real g R ⊤ hG.1 t) - G| < ε / 2 at hh
    exact hh
  have htri := norm_sub_norm_le G I
  simp only [Real.norm_eq_abs, abs_sub_comm G I] at htri
  linarith

end GammaBounds

theorem gamma_log_uniformly_small_tails : GBSpec.uniformlySmallTails := by
  intro k α β hα hαβ ε hε
  obtain ⟨C, _hC, hL, hR⟩ := gamma_log_tail_bounds k α β hα hαβ
  obtain ⟨δ, hδ, hδ1, hδsmall⟩ := GammaBounds.left_small_tails
    (gamma_log_majorants_converge.1 α k hα) ε hε
  obtain ⟨R₀, hR₀, hRsmall⟩ := GammaBounds.right_small_tails
    (gamma_log_majorants_converge.2 C) ε hε
  constructor
  · refine ⟨δ, hδ, hδ1.le, ?_⟩
    intro η hη hηδ s hs
    obtain ⟨G, _hG0, hG, hdom⟩ := hL η hη (hηδ.trans hδ1).le
    obtain ⟨L, hLval, hL0, hLG⟩ := hdom s hs
    exact ⟨L, hLval, hL0, hLG.trans_lt ((le_abs_self G).trans_lt (hδsmall η hη hηδ G hG))⟩
  · refine ⟨R₀, hR₀.le, ?_⟩
    intro R hR₀R s hs
    obtain ⟨G, _hG0, hG, hdom⟩ := hR R (hR₀.trans hR₀R).le
    obtain ⟨L, hLval, hL0, hLG⟩ := hdom s hs
    exact ⟨L, hLval, hL0, hLG.trans_lt ((le_abs_self G).trans_lt (hRsmall R hR₀R G hG))⟩

end SingleVariableAnalysis
