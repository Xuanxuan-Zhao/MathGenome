import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeakVolterraResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.WeakVolterraBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace ExpandedFA.PartV.WeakVolterraResolvent
open ExpandedFA.PartV.FractionalIntegrals.Spec
open ExpandedFA.PartV.WeakVolterraBounds.Spec

/-- Gamma summability with the unshifted denominator required by kernel bounds.
The finitely many indices below order one do not affect summability. -/
lemma summable_pow_div_gamma_shift {α c : ℝ} (hα : 0 < α) (hc : 0 ≤ c) :
    Summable (fun n : ℕ => c^n / Real.Gamma (((n+1 : ℕ) : ℝ)*α)) := by
  obtain ⟨R₀, hR₀⟩ := (tendsto_atTop_atTop.mp (tendsto_rpow_atTop hα)) (c+1)
  let R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hRc : c < R^α := lt_of_lt_of_le (by linarith : c < c+1)
    (hR₀ R (le_max_left _ _))
  have hq : c/R^α < 1 := (div_lt_one (Real.rpow_pos_of_pos hR _)).mpr hRc
  have hs := (summable_geometric_of_lt_one
    (div_nonneg hc (Real.rpow_nonneg hR.le _)) hq).mul_left
      (1 / (Real.exp (-(R+1)) * R^(α-1)))
  apply Summable.of_norm_bounded_eventually_nat hs
  have hn : ∀ᶠ n : ℕ in atTop, (1-α)/α ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hn] with n hn
  have hx : 0 ≤ ((n+1 : ℕ) : ℝ)*α-1 := by
    have hh := (div_le_iff₀ hα).mp hn
    push_cast
    nlinarith
  have hg := WeakVolterraBounds.gamma_lower_bound hx hR
  rw [sub_add_cancel] at hg
  have he : R^(((n+1 : ℕ) : ℝ)*α-1) = R^(α-1) * (R^α)^n := by
    have hh : ((n+1 : ℕ) : ℝ)*α-1 = (α-1)+α*(n : ℝ) := by push_cast; ring
    rw [hh, Real.rpow_add hR, Real.rpow_mul_natCast hR.le]
  rw [he] at hg
  rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg hc _)
    (Real.Gamma_pos_of_pos (by positivity)).le)]
  calc
    c^n / Real.Gamma (((n+1 : ℕ) : ℝ)*α) ≤
        c^n / (Real.exp (-(R+1)) * (R^(α-1) * (R^α)^n)) :=
      div_le_div_of_nonneg_left (pow_nonneg hc _) (by positivity) hg
    _ = 1 / (Real.exp (-(R+1)) * R^(α-1)) * (c/R^α)^n := by
      rw [div_pow]
      ring

/-- The diagonal convention does not affect the off-diagonal kernel. -/
lemma iteratedKernel_factor {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    (α : ℝ) (k : C(triangle T, 𝕜)) (n : ℕ) (z : triangle T)
    (hz : z.val.2 < z.val.1) :
    Spec.iteratedKernel α k n z.val.1 z.val.2 =
      (z.val.1-z.val.2)^(α-1) • Spec.normalizedAmplitude α k n z := by
  cases n with
  | zero =>
    simp [Spec.iteratedKernel, Spec.normalizedAmplitude, amplitudeValue, z.property]
  | succ n =>
    simp only [Spec.normalizedAmplitude, ite_eq_left hz, smul_smul]
    rw [← Real.rpow_add (sub_pos.mpr hz), show α-1+(1-α) = 0 by ring,
      Real.rpow_zero, one_smul]

lemma normalizedAmplitude_diagonal {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    (α : ℝ) (k : C(triangle T, 𝕜)) (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    Spec.normalizedAmplitude α k (n+1) ⟨(t,t), ht.1, le_rfl, ht.2⟩ = 0 := by
  simp [Spec.normalizedAmplitude]

/-- A summable uniform majorant for the entire normalized kernel series,
valid also at T=0. -/
lemma summable_amplitude_majorant {α T M : ℝ} (hα : 0 < α)
    (hT : 0 ≤ T) (hM : 0 ≤ M) (b : ℝ) (hb : 0 ≤ b) :
    Summable (fun n : ℕ => b^(n+1) * Spec.amplitudeBound α T M n) := by
  have hs := (summable_pow_div_gamma_shift hα
    (show 0 ≤ b*M*Real.Gamma α*T^α by positivity)).mul_left (b*M*Real.Gamma α)
  convert hs using 1
  ext n
  simp only [Spec.amplitudeBound, mul_pow, pow_succ]
  rw [mul_comm (n : ℝ) α, Real.rpow_mul_natCast hT]
  ring

set_option maxHeartbeats 1000000 in
/-- Constructing the common amplitude needs only the independently stated
regularity and iterate estimates, not any function-space inverse. -/
lemma kernel_series_of_regularity {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hM : 0 ≤ M) (k : C(triangle T, 𝕜))
    (hc : ∀ n, Continuous (Spec.normalizedAmplitude α k n))
    (hb : ∀ n z, ‖Spec.normalizedAmplitude α k n z‖ ≤ Spec.amplitudeBound α T M n)
    (ζ : 𝕜) : ∃ q : C(triangle T, 𝕜), Spec.KernelSeries α k ζ q := by
  let A (n : ℕ) : C(triangle T, 𝕜) := ⟨Spec.normalizedAmplitude α k n, hc n⟩
  let F (n : ℕ) : C(triangle T, 𝕜) := ζ^(n+1) • A n
  have hs := summable_amplitude_majorant hα hT hM ‖ζ‖ (norm_nonneg _)
  have hbound (n : ℕ) (z : triangle T) :
      ‖F n z‖ ≤ ‖ζ‖^(n+1) * Spec.amplitudeBound α T M n := by
    change ‖ζ^(n+1) * Spec.normalizedAmplitude α k n z‖ ≤ _
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hb n z) (by positivity)
  have hsF : Summable F := by
    apply Summable.of_norm_bounded hs
    intro n
    apply (ContinuousMap.norm_le _ (by
      unfold Spec.amplitudeBound
      positivity [Real.Gamma_pos_of_pos (show 0 < ((n+1 : ℕ) : ℝ)*α by positivity)])).mpr
    exact hbound n
  let q := ∑' n, F n
  have hq (z : triangle T) : HasSum (fun n => F n z) (q z) :=
    (ContinuousMap.evalCLM 𝕜 z).hasSum hsF.hasSum
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact hq
  · have he : (fun z => ∑' n, F n z) = q :=
      funext fun z => (hq z).tsum_eq
    rw [← he]
    exact tendstoUniformly_tsum_nat hs hbound
  · intro t ht
    let z : triangle T := ⟨(t,t), ht.1, le_rfl, ht.2⟩
    have hz (n : ℕ) : F (n+1) z = 0 := by
      change ζ^(n+1+1) • Spec.normalizedAmplitude α k (n+1) _ = 0
      rw [normalizedAmplitude_diagonal α k n t ht, smul_zero]
    have htail : HasSum (fun n => F (n+1) z) 0 := by
      simpa only [hz] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : 𝕜)) 0)
    have hh := (hasSum_nat_add_iff (f := fun n => F n z) 1).mp htail
    have he : q z = F 0 z := by
      simpa only [Finset.sum_range_one, zero_add] using (hq z).unique hh
    simpa [F, A, Spec.normalizedAmplitude, z] using he
  · intro t s hs hst ht
    let z : triangle T := ⟨(t,s), hs, hst.le, ht⟩
    have hh := (hq z).const_smul ((t-s)^(α-1))
    have he (n : ℕ) : ζ^(n+1) * Spec.iteratedKernel α k n t s =
        (t-s)^(α-1) • F n z := by
      change ζ^(n+1) • Spec.iteratedKernel α k n z.val.1 z.val.2 = _
      rw [iteratedKernel_factor α k n z hst]
      exact smul_comm (ζ^(n+1)) ((t-s)^(α-1)) _
    simpa only [← he] using hh

/-- The integrable weight in Euler's Beta integral. -/
def betaWeight (α β u : ℝ) : ℝ := (1-u)^(α-1) * u^(β-1)

lemma betaWeight_integrable {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IntegrableOn (betaWeight α β) (Ioc 0 1) := by
  convert (ExpandedFA.PartV.BetaSemigroup.beta_convolution α β 0 1 hα hβ zero_lt_one).1 using 1
  ext u
  simp only [betaWeight, sub_zero]

lemma integral_betaWeight {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫ u in Ioc 0 1, betaWeight α β u) =
      Real.Gamma α * Real.Gamma β / Real.Gamma (α+β) := by
  simpa only [betaWeight, sub_zero, Real.one_rpow, mul_one] using
    (ExpandedFA.PartV.BetaSemigroup.beta_convolution α β 0 1 hα hβ zero_lt_one).2

lemma betaWeight_nonneg {α β u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) :
    0 ≤ betaWeight α β u :=
  mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hu.2) _)
    (Real.rpow_nonneg hu.1.le _)

/-- The two continuous amplitudes evaluated along the rescaled segment.
Retraction is only used outside the segment's natural domain. -/
def betaProduct {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (k a : C(triangle T, 𝕜)) (z : triangle T) (u : ℝ) : 𝕜 :=
  WeakVolterraBounds.extendedAmplitude hT k
      (z.val.1, z.val.2+(z.val.1-z.val.2)*u) *
    WeakVolterraBounds.extendedAmplitude hT a
      (z.val.2+(z.val.1-z.val.2)*u, z.val.2)

lemma continuous_betaProduct {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (k a : C(triangle T, 𝕜)) :
    Continuous (fun zu : triangle T × ℝ => betaProduct hT k a zu.1 zu.2) := by
  have ht : Continuous (fun zu : triangle T × ℝ => zu.1.val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
  have hs : Continuous (fun zu : triangle T × ℝ => zu.1.val.2) :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
  have hv := hs.add ((ht.sub hs).mul continuous_snd)
  exact ((WeakVolterraBounds.continuous_extendedAmplitude hT k).comp (ht.prodMk hv)).mul
    ((WeakVolterraBounds.continuous_extendedAmplitude hT a).comp (hv.prodMk hs))

lemma betaProduct_bound {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (k a : C(triangle T, 𝕜)) (z : triangle T) (u : ℝ) :
    ‖betaProduct hT k a z u‖ ≤ ‖k‖ * ‖a‖ := by
  exact (norm_mul_le _ _).trans (mul_le_mul (k.norm_coe_le_norm _)
    (a.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _))

/-- Rescaled convolution, with the full power factored out. -/
def betaAmplitude {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k a : C(triangle T, 𝕜)) :
    C(triangle T, 𝕜) where
  toFun z := ∫ u in Ioc 0 1, betaWeight α β u • betaProduct hT k a z u
  continuous_toFun := by
    apply continuous_of_dominated
      (bound := fun u => betaWeight α β u * (‖k‖ * ‖a‖))
    · intro z
      exact (betaWeight_integrable hα hβ).aestronglyMeasurable.smul
        (((continuous_betaProduct hT k a).comp
          (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    · intro z
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      rw [norm_smul, Real.norm_of_nonneg (betaWeight_nonneg hu)]
      exact mul_le_mul_of_nonneg_left (betaProduct_bound hT k a z u) (betaWeight_nonneg hu)
    · exact (betaWeight_integrable hα hβ).mul_const _
    · exact Eventually.of_forall fun u => continuous_const.smul
        ((continuous_betaProduct hT k a).comp (continuous_id.prodMk continuous_const))

lemma betaAmplitude_bound {𝕜 : Type} [RCLike 𝕜] {T M A α β : ℝ}
    (hT : 0 ≤ T) (hα : 0 < α) (hβ : 0 < β)
    (k a : C(triangle T, 𝕜)) (hM : 0 ≤ M) (_hA : 0 ≤ A)
    (hk : ∀ z, ‖k z‖ ≤ M) (ha : ∀ z, ‖a z‖ ≤ A) (z : triangle T) :
    ‖betaAmplitude hT α β hα hβ k a z‖ ≤
      M*A * (Real.Gamma α * Real.Gamma β / Real.Gamma (α+β)) := by
  have hb (u : ℝ) : ‖betaProduct hT k a z u‖ ≤ M*A :=
    (norm_mul_le _ _).trans (mul_le_mul (hk _) (ha _) (norm_nonneg _) hM)
  calc
    _ ≤ ∫ u in Ioc 0 1, betaWeight α β u * (M*A) := by
      apply norm_integral_le_of_norm_le ((betaWeight_integrable hα hβ).mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      rw [norm_smul, Real.norm_of_nonneg (betaWeight_nonneg hu)]
      exact mul_le_mul_of_nonneg_left (hb u) (betaWeight_nonneg hu)
    _ = _ := by rw [integral_mul_const, integral_betaWeight hα hβ, mul_comm]

/-- Absolute existence of the convolution of two power kernels with continuous amplitudes. -/
lemma amplitude_convolution_integrable {𝕜 : Type} [RCLike 𝕜] {T α β t s : ℝ}
    (hT : 0 ≤ T) (hα : 0 < α) (hβ : 0 < β)
    (k a : C(triangle T, 𝕜)) (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) :
    IntegrableOn (fun v => (t-v)^(α-1) •
      (amplitudeValue k t v * ((v-s)^(β-1) • amplitudeValue a v s))) (Ioc s t) := by
  have hi := (ExpandedFA.PartV.BetaSemigroup.beta_convolution α β s t hα hβ hst).1
  have hg : Continuous (fun v =>
      WeakVolterraBounds.extendedAmplitude hT k (t,v) *
        WeakVolterraBounds.extendedAmplitude hT a (v,s)) :=
    ((WeakVolterraBounds.continuous_extendedAmplitude hT k).comp
      (continuous_const.prodMk continuous_id)).mul
      ((WeakVolterraBounds.continuous_extendedAmplitude hT a).comp
        (continuous_id.prodMk continuous_const))
  apply (hi.smul_bdd (‖k‖*‖a‖) hg.aestronglyMeasurable
    (Eventually.of_forall fun v => (norm_mul_le _ _).trans
      (mul_le_mul (k.norm_coe_le_norm _) (a.norm_coe_le_norm _)
        (norm_nonneg _) (norm_nonneg _)))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  change ((t-v)^(α-1) * (v-s)^(β-1)) •
    (WeakVolterraBounds.extendedAmplitude hT k (t,v) *
      WeakVolterraBounds.extendedAmplitude hT a (v,s)) = _
  rw [WeakVolterraBounds.extendedAmplitude_eq hT k ⟨hs.trans hv.1.le, hv.2, ht⟩,
    WeakVolterraBounds.extendedAmplitude_eq hT a ⟨hs, hv.1.le, hv.2.trans ht⟩]
  rw [mul_smul_comm, smul_smul]

/-- Beta rescaling of a convolution retains a continuous amplitude on the
closed triangle, for arbitrary positive orders. -/
lemma amplitude_convolution {𝕜 : Type} [RCLike 𝕜] {T α β t s : ℝ}
    (hT : 0 ≤ T) (hα : 0 < α) (hβ : 0 < β)
    (k a : C(triangle T, 𝕜)) (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) :
    (∫ v in Ioc s t, (t-v)^(α-1) •
      (amplitudeValue k t v * ((v-s)^(β-1) • amplitudeValue a v s))) =
      (t-s)^(α+β-1) • betaAmplitude hT α β hα hβ k a ⟨(t,s), hs, hst.le, ht⟩ := by
  let F : ℝ → 𝕜 := fun v => (t-v)^(α-1) •
    (amplitudeValue k t v * ((v-s)^(β-1) • amplitudeValue a v s))
  let z : triangle T := ⟨(t,s), hs, hst.le, ht⟩
  have hr : 0 < t-s := sub_pos.mpr hst
  have he : ∀ᵐ u ∂volume.restrict (Ioc (0 : ℝ) 1),
      F ((t-s)*u+s) =
        (t-s)^(α+β-2) • (betaWeight α β u • betaProduct hT k a z u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hv1 : s ≤ (t-s)*u+s := by nlinarith [hr.le, hu.1.le]
    have hv2 : (t-s)*u+s ≤ t := by nlinarith [hr.le, hu.2]
    have hp : betaProduct hT k a z u =
        amplitudeValue k t ((t-s)*u+s) * amplitudeValue a ((t-s)*u+s) s := by
      dsimp [betaProduct, z]
      rw [add_comm s,
        WeakVolterraBounds.extendedAmplitude_eq hT k ⟨hs.trans hv1, hv2, ht⟩,
        WeakVolterraBounds.extendedAmplitude_eq hT a ⟨hs, hv1, hv2.trans ht⟩]
    dsimp [F]
    rw [mul_smul_comm, ← hp, show t-((t-s)*u+s) = (t-s)*(1-u) by ring,
      show (t-s)*u+s-s = (t-s)*u by ring,
      Real.mul_rpow hr.le (sub_nonneg.mpr hu.2), Real.mul_rpow hr.le hu.1.le]
    simp only [smul_smul, betaWeight]
    rw [show α+β-2 = (α-1)+(β-1) by ring, Real.rpow_add hr]
    congr 1
    ring
  have hsub := intervalIntegral.smul_integral_comp_mul_add F (t-s) s (a := 0) (b := 1)
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at hsub
  rw [intervalIntegral.integral_of_le hst.le,
    intervalIntegral.integral_of_le zero_le_one, integral_congr_ae he,
    integral_smul, smul_smul] at hsub
  change (∫ v in Ioc s t, F v) = _
  rw [← hsub]
  have hp : (t-s) * (t-s)^(α+β-2) = (t-s)^(α+β-1) := by
    calc
      _ = (t-s)^(1 : ℝ) * (t-s)^(α+β-2) := by rw [Real.rpow_one]
      _ = (t-s)^(1+(α+β-2)) := (Real.rpow_add hr _ _).symm
      _ = _ := by congr 1; ring
  rw [hp]
  rfl

/-- Amplitude after removing the full power of the lag from each iterate. -/
def orderAmplitude {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (α : ℝ)
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(triangle T, 𝕜)) : ℕ → C(triangle T, 𝕜)
  | 0 => k
  | n+1 => betaAmplitude hT α (((n+1 : ℕ) : ℝ)*α) hα (by positivity)
      k (orderAmplitude α hα hT k n)

lemma iteratedKernel_orderAmplitude {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(triangle T, 𝕜)) (n : ℕ) :
    ∀ (t s : ℝ) (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T),
      Spec.iteratedKernel α k n t s =
        (t-s)^(((n+1 : ℕ) : ℝ)*α-1) •
          orderAmplitude α hα hT k n ⟨(t,s), hs, hst.le, ht⟩ := by
  induction n with
  | zero =>
    intro t s hs hst ht
    simp [Spec.iteratedKernel, orderAmplitude, amplitudeValue,
      show (t,s) ∈ triangle T from ⟨hs, hst.le, ht⟩]
  | succ n ih =>
    intro t s hs hst ht
    rw [Spec.iteratedKernel]
    have he : ∀ᵐ v ∂volume.restrict (Ioc s t),
        (t-v)^(α-1) • (amplitudeValue k t v * Spec.iteratedKernel α k n v s) =
          (t-v)^(α-1) • (amplitudeValue k t v *
            ((v-s)^(((n+1 : ℕ) : ℝ)*α-1) •
              amplitudeValue (orderAmplitude α hα hT k n) v s)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      rw [ih v s hs hv.1 (hv.2.trans ht)]
      simp only [amplitudeValue, dite_eq_left (show (v,s) ∈ triangle T from
        ⟨hs, hv.1.le, hv.2.trans ht⟩)]
    rw [integral_congr_ae he,
      amplitude_convolution hT hα (show 0 < ((n+1 : ℕ) : ℝ)*α by positivity)
        k (orderAmplitude α hα hT k n) hs hst ht]
    have heq : α+((n+1 : ℕ) : ℝ)*α-1 = ((n+1+1 : ℕ) : ℝ)*α-1 := by
      push_cast; ring
    rw [heq]
    rfl

lemma orderAmplitude_bound {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (k : C(triangle T, 𝕜)) (hk : ∀ z, ‖k z‖ ≤ M) (n : ℕ) (z : triangle T) :
    ‖orderAmplitude α hα hT k n z‖ ≤
      M^(n+1) * Real.Gamma α^(n+1) / Real.Gamma (((n+1 : ℕ) : ℝ)*α) := by
  induction n generalizing z with
  | zero => simpa [orderAmplitude, (Real.Gamma_pos_of_pos hα).ne'] using hk z
  | succ n ih =>
    have hg : 0 < Real.Gamma (((n+1 : ℕ) : ℝ)*α) :=
      Real.Gamma_pos_of_pos (by positivity)
    have hb := betaAmplitude_bound hT hα (show 0 < ((n+1 : ℕ) : ℝ)*α by positivity)
      k (orderAmplitude α hα hT k n) hM
      (show 0 ≤ M^(n+1) * Real.Gamma α^(n+1) / Real.Gamma (((n+1 : ℕ) : ℝ)*α) by
        positivity [Real.Gamma_pos_of_pos hα]) hk ih z
    change ‖betaAmplitude hT α (((n+1 : ℕ) : ℝ)*α) hα _ k
      (orderAmplitude α hα hT k n) z‖ ≤ _
    apply hb.trans_eq
    have heq : α+((n+1 : ℕ) : ℝ)*α = ((n+1+1 : ℕ) : ℝ)*α := by push_cast; ring
    rw [heq, pow_succ, pow_succ]
    field_simp
    ring

lemma normalizedAmplitude_orderAmplitude {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(triangle T, 𝕜)) (n : ℕ) (z : triangle T) :
    Spec.normalizedAmplitude α k n z =
      (z.val.1-z.val.2)^((n : ℝ)*α) • orderAmplitude α hα hT k n z := by
  cases n with
  | zero => simp [Spec.normalizedAmplitude, orderAmplitude]
  | succ n =>
    by_cases hz : z.val.2 < z.val.1
    · rw [Spec.normalizedAmplitude, ite_eq_left hz,
        iteratedKernel_orderAmplitude hα hT k (n+1) _ _ z.property.1 hz z.property.2.2,
        smul_smul, ← Real.rpow_add (sub_pos.mpr hz)]
      congr 2
      push_cast; ring
    · have he : z.val.1-z.val.2 = 0 := sub_eq_zero.mpr
        (le_antisymm (not_lt.mp hz) z.property.2.1)
      simp only [Spec.normalizedAmplitude, ite_eq_right hz, he, Nat.cast_add, Nat.cast_one]
      rw [Real.zero_rpow (show ((n : ℝ)+1)*α ≠ 0 by positivity), zero_smul]

/-- Each normalized iterated kernel is continuous on the entire closed triangle. -/
lemma continuous_normalizedAmplitude {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(triangle T, 𝕜)) (n : ℕ) :
    Continuous (Spec.normalizedAmplitude α k n) := by
  have he := funext (normalizedAmplitude_orderAmplitude hα hT k n)
  rw [he]
  exact (((continuous_fst.comp continuous_subtype_val).sub
    (continuous_snd.comp continuous_subtype_val)).rpow_const
      (fun z => Or.inr (by positivity))).smul (orderAmplitude α hα hT k n).continuous

lemma normalizedAmplitude_bound {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (k : C(triangle T, 𝕜)) (hk : ∀ z, ‖k z‖ ≤ M) (n : ℕ) (z : triangle T) :
    ‖Spec.normalizedAmplitude α k n z‖ ≤ Spec.amplitudeBound α T M n := by
  have hr : 0 ≤ z.val.1-z.val.2 := sub_nonneg.mpr z.property.2.1
  have hrT : z.val.1-z.val.2 ≤ T := by linarith [z.property.1, z.property.2.2]
  rw [normalizedAmplitude_orderAmplitude hα hT k n z, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg hr _)]
  calc
    _ ≤ T^((n : ℝ)*α) *
        (M^(n+1)*Real.Gamma α^(n+1)/Real.Gamma (((n+1 : ℕ) : ℝ)*α)) :=
      mul_le_mul (Real.rpow_le_rpow hr hrT (by positivity))
        (orderAmplitude_bound hα hT hM k hk n z) (norm_nonneg _)
        (Real.rpow_nonneg hT _)
    _ = _ := by unfold Spec.amplitudeBound; ring

lemma iteratedKernel_bound {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (k : C(triangle T, 𝕜)) (hk : ∀ z, ‖k z‖ ≤ M) (n : ℕ)
    (t s : ℝ) (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) :
    ‖Spec.iteratedKernel α k n t s‖ ≤ Spec.kernelBound α M n (t-s) := by
  rw [iteratedKernel_orderAmplitude hα hT k n t s hs hst ht, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hst.le) _)]
  calc
    _ ≤ (t-s)^(((n+1 : ℕ) : ℝ)*α-1) *
        (M^(n+1)*Real.Gamma α^(n+1)/Real.Gamma (((n+1 : ℕ) : ℝ)*α)) :=
      mul_le_mul_of_nonneg_left (orderAmplitude_bound hα hT hM k hk n _)
        (Real.rpow_nonneg (sub_nonneg.mpr hst.le) _)
    _ = _ := by unfold Spec.kernelBound; ring

lemma iteratedKernel_recursion_integrable {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(triangle T, 𝕜)) (n : ℕ)
    (t s : ℝ) (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) :
    IntegrableOn (fun v => (t-v)^(α-1) •
      (amplitudeValue k t v * Spec.iteratedKernel α k n v s)) (Ioc s t) := by
  apply (amplitude_convolution_integrable hT hα
    (show 0 < ((n+1 : ℕ) : ℝ)*α by positivity)
    k (orderAmplitude α hα hT k n) hs hst ht).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  rw [iteratedKernel_orderAmplitude hα hT k n v s hs hv.1 (hv.2.trans ht)]
  simp only [amplitudeValue, dite_eq_left (show (v,s) ∈ triangle T from
    ⟨hs, hv.1.le, hv.2.trans ht⟩)]

/-- Beta rescaling proves the complete regularity and exact majorants,
without any restriction on the positive order or on the interval length. -/
theorem kernel_regularity : Spec.KernelRegularity := by
  intro 𝕜 _ α T hα hT k M hM hk
  exact ⟨continuous_normalizedAmplitude hα hT k,
    normalizedAmplitude_bound hα hT hM k hk,
    iteratedKernel_bound hα hT hM k hk,
    iteratedKernel_recursion_integrable hα hT k⟩

/-- The continuous common resolvent-kernel series, prior to its operator realization. -/
theorem kernel_series {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (k : C(triangle T, 𝕜)) (hk : ∀ z, ‖k z‖ ≤ M) (ζ : 𝕜) :
    ∃ q : C(triangle T, 𝕜), Spec.KernelSeries α k ζ q :=
  kernel_series_of_regularity hα hT hM k
    (continuous_normalizedAmplitude hα hT k) (normalizedAmplitude_bound hα hT hM k hk) ζ

/-- Absolute Fubini for continuous amplitudes follows from the positive
power-kernel majorant. This statement retains every Lp representative. -/
lemma weak_double_integrable_ae {𝕜 : Type} [RCLike 𝕜] {α β T : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hT : 0 ≤ T)
    (k a : C(triangle T, 𝕜)) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)) :
    ∀ᵐ t ∂intervalMeasure T, Integrable (fun vs : ℝ × ℝ =>
      WeakVolterraBounds.weakSchurKernel hT α k (t,vs.1) *
        WeakVolterraBounds.weakSchurKernel hT β a (vs.1,vs.2) * f vs.2)
      ((intervalMeasure T).prod (intervalMeasure T)) := by
  let f₀ := (Ioc (0 : ℝ) T).indicator f
  filter_upwards [ExpandedFA.PartV.BetaSemigroup.absolute_fubini α β T hα hβ hT p hp f hf]
    with t hit
  let L : ℝ × ℝ → ℝ × ℝ := fun vs => (t-vs.2, t-vs.1)
  have hL : MeasurePreserving L (volume.prod volume) (volume.prod volume) := by
    exact ((volume.measurePreserving_sub_left t).prod
      (volume.measurePreserving_sub_left t)).comp Measure.measurePreserving_swap
  have hi := (hL.integrable_comp hit.aestronglyMeasurable).mpr hit
  let G : ℝ × ℝ → 𝕜 := fun vs =>
    WeakVolterraBounds.extendedAmplitude hT k (t,vs.1) *
      WeakVolterraBounds.extendedAmplitude hT a vs
  have hGc : Continuous G :=
    ((WeakVolterraBounds.continuous_extendedAmplitude hT k).comp
      (continuous_const.prodMk continuous_fst)).mul
      (WeakVolterraBounds.continuous_extendedAmplitude hT a)
  have hGb (vs : ℝ × ℝ) : ‖G vs‖ ≤ ‖k‖*‖a‖ :=
    (norm_mul_le _ _).trans (mul_le_mul (k.norm_coe_le_norm _)
      (a.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _))
  have hj := (hi.bdd_smul (‖k‖*‖a‖) hGc.aestronglyMeasurable
    (Eventually.of_forall hGb)).restrict (s := Ioc (0 : ℝ) T ×ˢ Ioc (0 : ℝ) T)
  rw [← Measure.prod_restrict] at hj
  apply hj.congr
  change ∀ᵐ vs ∂(volume.restrict (Ioc (0 : ℝ) T)).prod
      (volume.restrict (Ioc (0 : ℝ) T)), _
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with vs hvs
  change G vs • (powerKernel α T (t-vs.1) •
    (powerKernel β T ((t-vs.2)-(t-vs.1)) •
      (Ioc (0 : ℝ) T).indicator f (t-(t-vs.2)))) = _
  rw [show (t-vs.2)-(t-vs.1) = vs.1-vs.2 by ring,
    sub_sub_cancel, indicator_of_mem hvs.2]
  simp only [G, WeakVolterraBounds.weakSchurKernel, smul_eq_mul,
    RCLike.real_smul_eq_coe_mul]
  ring

/-- A composed Schur kernel is exactly the Beta-rescaled continuous amplitude. -/
lemma weakSchurKernel_composition {𝕜 : Type} [RCLike 𝕜] {α β T t s : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hT : 0 ≤ T)
    (k a : C(triangle T, 𝕜)) (ht : t ∈ Icc (0 : ℝ) T) (hs : s ∈ Icc (0 : ℝ) T) :
    (∫ v, WeakVolterraBounds.weakSchurKernel hT α k (t,v) *
      WeakVolterraBounds.weakSchurKernel hT β a (v,s) ∂intervalMeasure T) =
      WeakVolterraBounds.weakSchurKernel hT (α+β)
        (betaAmplitude hT α β hα hβ k a) (t,s) := by
  let F : ℝ → 𝕜 := fun v => (t-v)^(α-1) •
    (amplitudeValue k t v * ((v-s)^(β-1) • amplitudeValue a v s))
  have he : (fun v => WeakVolterraBounds.weakSchurKernel hT α k (t,v) *
        WeakVolterraBounds.weakSchurKernel hT β a (v,s)) =ᵐ[intervalMeasure T]
      (Ioo s t).indicator F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    by_cases hvs : v ∈ Ioo s t
    · have htv : t-v ∈ Ioc (0 : ℝ) T := ⟨sub_pos.mpr hvs.2, by linarith [ht.2, hv.1]⟩
      have hvs' : v-s ∈ Ioc (0 : ℝ) T := ⟨sub_pos.mpr hvs.1, by linarith [hv.2, hs.1]⟩
      simp only [WeakVolterraBounds.weakSchurKernel, powerKernel,
        indicator_of_mem htv, indicator_of_mem hvs', indicator_of_mem hvs, F]
      rw [WeakVolterraBounds.extendedAmplitude_eq hT k ⟨hv.1.le, hvs.2.le, ht.2⟩,
        WeakVolterraBounds.extendedAmplitude_eq hT a ⟨hs.1, hvs.1.le, hv.2⟩,
        smul_mul_assoc]
    · have hz : t-v ∉ Ioc (0 : ℝ) T ∨ v-s ∉ Ioc (0 : ℝ) T := by
        by_contra! h
        exact hvs ⟨sub_pos.mp h.2.1, sub_pos.mp h.1.1⟩
      rcases hz with hz | hz <;>
        simp [WeakVolterraBounds.weakSchurKernel, powerKernel, hz, hvs]
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioo]
  have hsub : Ioo s t ⊆ Ioc (0 : ℝ) T :=
    fun v hv => ⟨hs.1.trans_lt hv.1, hv.2.le.trans ht.2⟩
  have hμ : (intervalMeasure T).restrict (Ioo s t) = volume.restrict (Ioo s t) := by
    rw [intervalMeasure, Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hsub]
  rw [hμ, ← integral_Ioc_eq_integral_Ioo]
  by_cases hst : s < t
  · rw [show (∫ v in Ioc s t, F v) = _ from amplitude_convolution hT hα hβ k a hs.1 hst ht.2]
    have hlag : t-s ∈ Ioc (0 : ℝ) T := ⟨sub_pos.mpr hst, by linarith [hs.1, ht.2]⟩
    rw [WeakVolterraBounds.weakSchurKernel, powerKernel, indicator_of_mem hlag,
      WeakVolterraBounds.extendedAmplitude_eq hT _ ⟨hs.1, hst.le, ht.2⟩]
    simp only [amplitudeValue, dite_eq_left (show (t,s) ∈ triangle T from ⟨hs.1, hst.le, ht.2⟩)]
  · have hlag : t-s ∉ Ioc (0 : ℝ) T := by intro h; exact hst (sub_pos.mp h.1)
    simp [Ioc_eq_empty hst, WeakVolterraBounds.weakSchurKernel, powerKernel, hlag]

/-- Fubini identifies the composed integral, including all representative choices. -/
lemma weakValue_composition_ae {𝕜 : Type} [RCLike 𝕜] {α β T : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hT : 0 ≤ T)
    (k a : C(triangle T, 𝕜)) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)) :
    weakValue α k (weakValue β a f) =ᵐ[intervalMeasure T]
      weakValue (α+β) (betaAmplitude hT α β hα hβ k a) f := by
  let : IsFiniteMeasure (intervalMeasure T) := by unfold intervalMeasure; infer_instance
  filter_upwards [weak_double_integrable_ae hα hβ hT k a p hp f hf,
    ae_restrict_mem measurableSet_Ioc] with t hit ht
  rw [← (WeakVolterraBounds.weakSchurKernel_bridge hT α k _ ⟨ht.1.le, ht.2⟩).2,
    ← (WeakVolterraBounds.weakSchurKernel_bridge hT (α+β)
      (betaAmplitude hT α β hα hβ k a) f ⟨ht.1.le, ht.2⟩).2]
  unfold SchurLp.kernelValue
  have he : (fun v => WeakVolterraBounds.weakSchurKernel hT α k (t,v) * weakValue β a f v)
      =ᵐ[intervalMeasure T] fun v => ∫ s,
        WeakVolterraBounds.weakSchurKernel hT α k (t,v) *
          WeakVolterraBounds.weakSchurKernel hT β a (v,s) * f s ∂intervalMeasure T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    rw [← (WeakVolterraBounds.weakSchurKernel_bridge hT β a f ⟨hv.1.le, hv.2⟩).2]
    simp only [SchurLp.kernelValue, ← integral_const_mul, mul_assoc]
  rw [integral_congr_ae he, integral_integral_swap hit]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [integral_mul_const,
    weakSchurKernel_composition hα hβ hT k a ⟨ht.1.le, ht.2⟩ ⟨hs.1.le, hs.2⟩]

lemma weakValue_composition_continuous {𝕜 : Type} [RCLike 𝕜] {α β T : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hT : 0 ≤ T)
    (k a : C(triangle T, 𝕜))
    (B : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜))
    (hB : Spec.ContinuousRealizes hT β a B)
    (f : C(Icc (0 : ℝ) T, 𝕜)) (t : Icc (0 : ℝ) T) :
    weakValue α k (continuousExtension hT (B f)) t =
      weakValue (α+β) (betaAmplitude hT α β hα hβ k a) (continuousExtension hT f) t := by
  by_cases hzero : T = 0
  · have ht : (t : ℝ) = 0 := by linarith [t.property.1, t.property.2]
    simp [ht, weakValue]
  have hpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
  have hf : MemLp (continuousExtension hT f) ∞ (intervalMeasure T) :=
    memLp_top_of_bound (ExpandedFA.PartV.FractionalIntegrals.continuous_extension hT f).aestronglyMeasurable
      ‖f‖ (Eventually.of_forall (ExpandedFA.PartV.FractionalIntegrals.extension_norm_le hT f))
  have hBF : continuousExtension hT (B f) =ᵐ[intervalMeasure T]
      weakValue β a (continuousExtension hT f) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
    rw [continuousExtension, projIcc_of_mem hT hs']
    exact hB f ⟨s, hs'⟩
  have he : weakValue α k (continuousExtension hT (B f)) =ᵐ[intervalMeasure T]
      weakValue (α+β) (betaAmplitude hT α β hα hβ k a) (continuousExtension hT f) := by
    have he' : weakValue α k (continuousExtension hT (B f)) =ᵐ[intervalMeasure T]
        weakValue α k (weakValue β a (continuousExtension hT f)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact (WeakVolterraBounds.representative_independence α k _ _ hBF s ⟨hs.1.le, hs.2⟩).2
    exact he'.trans (weakValue_composition_ae hα hβ hT k a ∞ le_top _ hf)
  change _ =ᵐ[volume.restrict (Ioc (0 : ℝ) T)] _ at he
  rw [restrict_Ioc_eq_restrict_Icc] at he
  exact Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hpos) he
    (WeakVolterraBounds.continuous_weakValue hα hT k (B f))
    (WeakVolterraBounds.continuous_weakValue (add_pos hα hβ) hT _ f) t.property

/-- Bridge from the actual recursively convolved kernel to its full-order amplitude. -/
lemma iteratedKernel_integral_bridge {𝕜 : Type} [RCLike 𝕜] {α T t : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(triangle T, 𝕜)) (n : ℕ)
    (f : ℝ → 𝕜) (ht : t ∈ Icc (0 : ℝ) T) :
    (IntegrableOn (fun s => Spec.iteratedKernel α k n t s * f s) (Ioc 0 t) ↔
      IntegrableOn (weakIntegrand (((n+1 : ℕ) : ℝ)*α)
        (orderAmplitude α hα hT k n) f t) (Ioc 0 t)) ∧
    (∫ s in Ioc 0 t, Spec.iteratedKernel α k n t s * f s) =
      weakValue (((n+1 : ℕ) : ℝ)*α) (orderAmplitude α hα hT k n) f t := by
  have he : (fun s => Spec.iteratedKernel α k n t s * f s) =ᵐ[volume.restrict (Ioc 0 t)]
      weakIntegrand (((n+1 : ℕ) : ℝ)*α) (orderAmplitude α hα hT k n) f t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne t)] with s hs hne
    have hst : s < t := lt_of_le_of_ne hs.2 hne
    rw [iteratedKernel_orderAmplitude hα hT k n t s hs.1.le hst ht.2,
      weakIntegrand, amplitudeValue,
      dite_eq_left (show (t,s) ∈ triangle T from ⟨hs.1.le, hs.2, ht.2⟩), smul_mul_assoc]
  exact ⟨integrable_congr he, integral_congr_ae he⟩

lemma continuous_iterates_realize {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(triangle T, 𝕜))
    (V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜))
    (hV : Spec.ContinuousRealizes hT α k V) (n : ℕ) :
    Spec.ContinuousRealizes hT (((n+1 : ℕ) : ℝ)*α) (orderAmplitude α hα hT k n) (V^(n+1)) := by
  induction n with
  | zero => simpa only [zero_add, Nat.cast_one, one_mul, orderAmplitude, pow_one] using hV
  | succ n ih =>
    intro f t
    have he : α+((n+1 : ℕ) : ℝ)*α = ((n+1+1 : ℕ) : ℝ)*α := by push_cast; ring
    have hc := weakValue_composition_continuous hα
      (show 0 < ((n+1 : ℕ) : ℝ)*α by positivity) hT k (orderAmplitude α hα hT k n)
      (V^(n+1)) ih f t
    rw [he] at hc
    change (V^(n+1+1)) f t = _
    rw [pow_succ']
    change V ((V^(n+1)) f) t = _
    rw [hV]
    exact hc

lemma lp_iterates_realize {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(triangle T, 𝕜))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (V : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T))
    (hV : Spec.LpRealizes α k p V) (n : ℕ) :
    Spec.LpRealizes (((n+1 : ℕ) : ℝ)*α) (orderAmplitude α hα hT k n) p (V^(n+1)) := by
  induction n with
  | zero => simpa only [zero_add, Nat.cast_one, one_mul, orderAmplitude, pow_one] using hV
  | succ n ih =>
    intro f hf
    let g := (V^(n+1)) (hf.toLp f)
    have hg := hV g (Lp.memLp g)
    rw [Lp.toLp_coeFn] at hg
    have hi := ih f hf
    have hr : weakValue α k g =ᵐ[intervalMeasure T]
        weakValue α k (weakValue (((n+1 : ℕ) : ℝ)*α) (orderAmplitude α hα hT k n) f) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (WeakVolterraBounds.representative_independence α k _ _ hi t ⟨ht.1.le, ht.2⟩).2
    have hc := weakValue_composition_ae hα
      (show 0 < ((n+1 : ℕ) : ℝ)*α by positivity) hT k (orderAmplitude α hα hT k n)
      p Fact.out f hf
    have he : α+((n+1 : ℕ) : ℝ)*α = ((n+1+1 : ℕ) : ℝ)*α := by push_cast; ring
    rw [he] at hc
    have hfinal := hg.trans (hr.trans hc)
    simpa only [pow_succ', mul_apply_eq_comp, g, orderAmplitude] using hfinal

/-- The recursively specified kernels represent the actual operator powers,
pointwise on continuous functions and for every Lp representative a.e. -/
theorem iterate_representation : Spec.IterateRepresentation := by
  intro 𝕜 _ α T hα hT k
  constructor
  · intro V hV n f t
    have hi := WeakVolterraBounds.weak_continuous_input_integrable
      (show 0 < ((n+1 : ℕ) : ℝ)*α by positivity) hT (orderAmplitude α hα hT k n) f t
    have hb := iteratedKernel_integral_bridge hα hT k n (continuousExtension hT f) t.property
    exact ⟨hb.1.mpr hi, (continuous_iterates_realize hα hT k V hV n f t).trans hb.2.symm⟩
  · intro p _ V hV n f hf
    let a := orderAmplitude α hα hT k n
    obtain ⟨U, hU, _⟩ := WeakVolterraBounds.weak_lp_construction (((n+1 : ℕ) : ℝ)*α) T
      (by positivity) hT a ‖a‖ (norm_nonneg _) (fun z => a.norm_coe_le_norm z) p
    have hi := (hU f hf).1
    have hr := lp_iterates_realize hα hT k p V hV n f hf
    constructor
    · filter_upwards [hi, ae_restrict_mem measurableSet_Ioc] with t hit ht
      exact (iteratedKernel_integral_bridge hα hT k n f ⟨ht.1.le, ht.2⟩).1.mpr hit
    · filter_upwards [hr, ae_restrict_mem measurableSet_Ioc] with t hrt ht
      exact hrt.trans (iteratedKernel_integral_bridge hα hT k n f ⟨ht.1.le, ht.2⟩).2.symm

/-- Termwise integration of the common kernel series. The single positive
power majorant suffices for every datum for which its norm integral exists. -/
lemma kernel_integral_hasSum {𝕜 : Type} [RCLike 𝕜] {α T M t : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (k : C(triangle T, 𝕜)) (hk : ∀ z, ‖k z‖ ≤ M)
    (ζ : 𝕜) (q : C(triangle T, 𝕜)) (hq : Spec.KernelSeries α k ζ q)
    (f : ℝ → 𝕜) (ht : t ∈ Icc (0 : ℝ) T)
    (hi : ∀ n, IntegrableOn (fun s => Spec.iteratedKernel α k n t s * f s) (Ioc 0 t))
    (hw : IntegrableOn (fun s => (t-s)^(α-1) * ‖f s‖) (Ioc 0 t)) :
    HasSum (fun n : ℕ => ζ^(n+1) *
      ∫ s in Ioc 0 t, Spec.iteratedKernel α k n t s * f s) (weakValue α q f t) := by
  let b : ℕ → ℝ := fun n => ‖ζ‖^(n+1) * Spec.amplitudeBound α T M n
  let w : ℝ → ℝ := fun s => (t-s)^(α-1) * ‖f s‖
  have hb : Summable b := summable_amplitude_majorant hα hT hM _ (norm_nonneg _)
  have hall : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) t), 0 ≤ s ∧ s < t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne t)] with s hs hne
    exact ⟨hs.1.le, lt_of_le_of_ne hs.2 hne⟩
  have hsum := hasSum_integral_of_dominated_convergence
    (F := fun n s => ζ^(n+1) * (Spec.iteratedKernel α k n t s * f s))
    (f := weakIntegrand α q f t) (fun n s => b n * w s)
    (fun n => ((hi n).const_mul _).aestronglyMeasurable) ?_ ?_ ?_ ?_
  · simpa only [integral_const_mul, weakValue] using hsum
  · intro n
    filter_upwards [hall] with s hs
    let z : triangle T := ⟨(t,s), hs.1, hs.2.le, ht.2⟩
    have hr : 0 ≤ t-s := sub_nonneg.mpr hs.2.le
    rw [norm_mul, norm_pow, norm_mul, iteratedKernel_factor α k n z hs.2,
      norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hr _)]
    calc
      _ = ‖ζ‖^(n+1) * ‖Spec.normalizedAmplitude α k n z‖ * w s := by dsimp [w]; ring
      _ ≤ b n * w s := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (normalizedAmplitude_bound hα hT hM k hk n z)
          (by positivity)) (mul_nonneg (Real.rpow_nonneg hr _) (norm_nonneg _))
  · exact Eventually.of_forall fun s => hb.mul_right (w s)
  · have he : (fun s => ∑' n, b n * w s) = fun s => (∑' n, b n) * w s := by
      ext s
      exact tsum_mul_right
    rw [he]
    exact hw.const_mul _
  · filter_upwards [hall] with s hs
    have hh := (hq.2.2.2 t s hs.1 hs.2 ht.2).mul_right (f s)
    simpa only [mul_assoc, weakIntegrand, amplitudeValue,
      dite_eq_left (show (t,s) ∈ triangle T from ⟨hs.1, hs.2.le, ht.2⟩), smul_mul_assoc] using hh

lemma norm_power_input_integrable {𝕜 : Type} [RCLike 𝕜] {α t : ℝ}
    (f : ℝ → 𝕜)
    (hi : IntegrableOn (fun s => (t-s)^(α-1) • f s) (Ioc 0 t)) :
    IntegrableOn (fun s => (t-s)^(α-1) * ‖f s‖) (Ioc 0 t) := by
  apply hi.norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)]

lemma continuous_bounds_of_realizes {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (k : C(triangle T, 𝕜)) (hk : ∀ z, ‖k z‖ ≤ M)
    (V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜))
    (hV : Spec.ContinuousRealizes hT α k V) :
    ∀ n, ‖V^n‖ ≤ iterateBound α T M n := by
  obtain ⟨U, hU, _, hb, _⟩ := WeakVolterraBounds.continuous_theorem α T hα hT k M hM hk
  have he : V = U := by ext f t; rw [hV, (hU f t).2]
  simpa only [he] using hb

lemma lp_bounds_of_realizes {𝕜 : Type} [RCLike 𝕜] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (k : C(triangle T, 𝕜)) (hk : ∀ z, ‖k z‖ ≤ M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (V : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T))
    (hV : Spec.LpRealizes α k p V) :
    ∀ n, ‖V^n‖ ≤ iterateBound α T M n := by
  obtain ⟨U, hU, _, hb, _⟩ := WeakVolterraBounds.lp_theorem α T hα hT k M hM hk p
  have he : V = U := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    have h1 := hV f (Lp.memLp f)
    have h2 := (hU f (Lp.memLp f)).2
    rw [Lp.toLp_coeFn] at h1 h2
    exact h1.trans h2.symm
  simpa only [he] using hb

lemma summable_norm_neumann {𝕜 : Type} [RCLike 𝕜]
    {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {α T M : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hM : 0 ≤ M) (V : E →L[𝕜] E)
    (hV : ∀ n, ‖V^n‖ ≤ iterateBound α T M n) (ζ : 𝕜) :
    Summable (fun n : ℕ => ‖ζ^n • V^n‖) := by
  have hs := WeakVolterraBounds.summable_pow_div_gamma hα
    (show 0 ≤ ‖ζ‖ * M * Real.Gamma α * T^α by positivity)
  apply Summable.of_norm_bounded hs
  intro n
  rw [norm_norm, norm_smul, norm_pow]
  calc
    _ ≤ ‖ζ‖^n * iterateBound α T M n :=
      mul_le_mul_of_nonneg_left (hV n) (by positivity)
    _ = _ := by
      simp only [iterateBound, mul_pow]
      rw [mul_comm (n : ℝ) α, Real.rpow_mul_natCast hT]
      ring

lemma hasSum_operator_apply {𝕜 : Type} [RCLike 𝕜]
    {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {A : ℕ → E →L[𝕜] E} {B : E →L[𝕜] E} (h : HasSum A B) (f : E) :
    HasSum (fun n => A n f) (B f) := by
  let ev : (E →L[𝕜] E) →+ E :=
    { toFun := fun A => A f
      map_zero' := rfl
      map_add' := fun A B => rfl }
  exact h.map ev (continuous_id.clm_apply continuous_const)

set_option maxHeartbeats 1200000 in
/-- Assembly of the complete resolvent from the actual iterate representation.
The hypothesis is precisely the remaining Fubini bridge; kernel regularity and
all exchanges of the resolvent series have been proved independently above. -/
lemma resolvent_representation_of_iterates (hiter : Spec.IterateRepresentation) :
    Spec.ResolventRepresentation := by
  intro 𝕜 _ α T hα hT k M hM hk ζ
  obtain ⟨q, hq⟩ := kernel_series hα hT hM k hk ζ
  obtain ⟨hiterC, hiterLp⟩ := hiter α T hα hT k
  refine ⟨q, hq, ?_, ?_⟩
  · intro V hV
    have hb := continuous_bounds_of_realizes hα hT hM k hk V hV
    have hN := WeakVolterraBounds.neumann_of_iterate_bound hα hT hM V hb ζ
    let R := ∑' n : ℕ, ζ^n • V^n
    refine ⟨R, hN.2.1, hN.2.2.1, ?_⟩
    intro f t
    refine ⟨WeakVolterraBounds.weak_continuous_input_integrable hα hT q f t, ?_⟩
    have hsum : HasSum (fun n : ℕ => ((ζ^n • V^n) f) t) (R f t) :=
      (ContinuousMap.evalCLM 𝕜 t).hasSum
        ((ContinuousLinearMap.apply 𝕜 C(Icc (0 : ℝ) T, 𝕜) f).hasSum hN.1.hasSum)
    have htail : HasSum (fun n : ℕ => ζ^(n+1) * ((V^(n+1)) f t)) (R f t - f t) := by
      simpa only [Finset.sum_range_one, pow_zero, one_smul,
        one_apply_eq_self, smul_apply,
        ContinuousMap.smul_apply, smul_eq_mul, one_mul] using (hasSum_nat_add_iff' 1).mpr hsum
    have hint := kernel_integral_hasSum hα hT hM k hk ζ q hq
      (continuousExtension hT f) t.property
      (fun n => (hiterC V hV n f t).1)
      (norm_power_input_integrable _
        (ExpandedFA.PartV.FractionalIntegrals.continuous_input_integrable hα hT f t))
    have he (n : ℕ) : ζ^(n+1) * ((V^(n+1)) f t) = ζ^(n+1) *
        ∫ s in Ioc 0 (t : ℝ), Spec.iteratedKernel α k n t s * continuousExtension hT f s := by
      rw [(hiterC V hV n f t).2]
    simp_rw [he] at htail
    exact (sub_eq_iff_eq_add.mp (htail.unique hint)).trans (add_comm _ _)
  · intro p _ V hV
    have hb := lp_bounds_of_realizes hα hT hM k hk p V hV
    have hN := WeakVolterraBounds.neumann_of_iterate_bound hα hT hM V hb ζ
    let R := ∑' n : ℕ, ζ^n • V^n
    refine ⟨R, hN.2.1, hN.2.2.1, ?_⟩
    intro f hf
    obtain ⟨Q, hQ, _⟩ := WeakVolterraBounds.weak_lp_construction α T hα hT q ‖q‖
      (norm_nonneg _) (fun z => q.norm_coe_le_norm z) p
    refine ⟨(hQ f hf).1, ?_⟩
    let g := hf.toLp f
    let F : ℕ → Lp 𝕜 p (intervalMeasure T) := fun n => (ζ^n • V^n) g
    have hsF : Summable (fun n => ‖F n‖) := by
      apply ((summable_norm_neumann hα hT hM V hb ζ).mul_right ‖g‖).of_norm_bounded
      intro n
      rw [norm_norm]
      exact ContinuousLinearMap.le_opNorm _ _
    have hsumF : HasSum F (R g) := hasSum_operator_apply hN.1.hasSum g
    have hae : ∀ᵐ t ∂intervalMeasure T,
        HasSum (fun n => F n t) ((∑' n, F n) t) :=
      Lp.hasSum_coeFn_tsum (f := F) (tsum_enorm_ne_top_iff_summable_norm.mpr hsF)
    rw [hsumF.tsum_eq] at hae
    have hF (n : ℕ) : (F (n+1) : ℝ → 𝕜) =ᵐ[intervalMeasure T]
        fun t => ζ^(n+1) *
          ∫ s in Ioc 0 t, Spec.iteratedKernel α k n t s * f s := by
      have he := (hiterLp p V hV n f hf).2
      filter_upwards [Lp.coeFn_smul (ζ^(n+1)) ((V^(n+1)) g), he] with t ht hrep
      change (ζ^(n+1) • (V^(n+1)) g : Lp 𝕜 p (intervalMeasure T)) t = _
      rw [ht, Pi.smul_apply, smul_eq_mul, hrep]
    have hF0 : (F 0 : ℝ → 𝕜) =ᵐ[intervalMeasure T] f := by
      simpa only [F, pow_zero, one_smul, one_apply_eq_self] using hf.coeFn_toLp
    have hallF := ae_all_iff.mpr hF
    have hallI := ae_all_iff.mpr (fun n => (hiterLp p V hV n f hf).1)
    have hw : ∀ᵐ t ∂intervalMeasure T,
        IntegrableOn (fun s => (t-s)^(α-1) * ‖f s‖) (Ioc 0 t) := by
      rcases hT.eq_or_lt with hzero | hpos
      · simp [← hzero, intervalMeasure]
      · filter_upwards [(ExpandedFA.PartV.FractionalIntegrals.fractional_memLp
          hα hpos p Fact.out f hf).1] with t ht
        exact norm_power_input_integrable f ht
    filter_upwards [hae, hallF, hallI, hF0, hw,
      ae_restrict_mem measurableSet_Ioc] with t hsum htF htI ht0 htw ht
    have htail := (hasSum_nat_add_iff' 1).mpr hsum
    simp only [Finset.sum_range_one, ht0, htF] at htail
    have hint := kernel_integral_hasSum hα hT hM k hk ζ q hq f ⟨ht.1.le, ht.2⟩ htI htw
    exact (sub_eq_iff_eq_add.mp (htail.unique hint)).trans (add_comm _ _)

/-- The common resolvent kernel represents the two-sided inverse on C and all Lp spaces. -/
theorem resolvent_representation : Spec.ResolventRepresentation :=
  resolvent_representation_of_iterates iterate_representation

/-- Continuous monomials whose scalar multiples are the Mittag--Leffler terms. -/
def mittagMonomial {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    (α : ℝ) (hα : 0 < α) (n : ℕ) : C(Icc (0 : ℝ) T, 𝕜) where
  toFun t := (t.val ^ ((n : ℝ)*α) / Real.Gamma ((n : ℝ)*α+1)) • (1 : 𝕜)
  continuous_toFun := by
    apply Continuous.smul _ continuous_const
    apply Continuous.div_const
    exact continuous_subtype_val.rpow_const (fun t => Or.inr (by positivity))

lemma fractional_monomial {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (n : ℕ) (t : Icc (0 : ℝ) T) :
    fractionalValue α (continuousExtension hT (mittagMonomial (𝕜 := 𝕜) α hα n)) t =
      mittagMonomial (𝕜 := 𝕜) α hα (n+1) t := by
  have hb : 0 < (n : ℝ)*α+1 := by positivity
  by_cases ht : (t : ℝ) = 0
  · simp [ht, fractionalValue, powerValue, mittagMonomial,
      Nat.cast_add, Nat.cast_one, Real.zero_rpow (show ((n : ℝ)+1)*α ≠ 0 by positivity)]
  have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
  have hi := ExpandedFA.PartV.BetaSemigroup.beta_convolution α ((n : ℝ)*α+1) 0 t
    hα hb htpos
  have he : (fun s => ((t : ℝ)-s) ^ (α-1) •
      continuousExtension hT (mittagMonomial (𝕜 := 𝕜) α hα n) s) =ᵐ[
      volume.restrict (Ioc 0 (t : ℝ))]
      fun s => (((t : ℝ)-s) ^ (α-1) * s ^ ((n : ℝ)*α)) •
        ((Real.Gamma ((n : ℝ)*α+1))⁻¹ • (1 : 𝕜)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans t.property.2⟩
    simp only [continuousExtension, projIcc_of_mem hT hs', mittagMonomial,
      ContinuousMap.coe_mk, div_eq_mul_inv, smul_smul]
    congr 1
    ring
  unfold fractionalValue powerValue
  rw [integral_congr_ae he, integral_smul_const]
  have hv : (∫ s in Ioc 0 (t : ℝ), ((t : ℝ)-s) ^ (α-1) * s ^ ((n : ℝ)*α)) =
      (Real.Gamma α * Real.Gamma ((n : ℝ)*α+1) /
        Real.Gamma (α+((n : ℝ)*α+1))) * (t : ℝ) ^ (α+(n : ℝ)*α) := by
    have he : α+((n : ℝ)*α+1)-1 = α+(n : ℝ)*α := by ring
    simpa only [sub_zero, add_sub_cancel_right, he] using hi.2
  rw [hv]
  simp only [mittagMonomial, ContinuousMap.coe_mk, smul_smul]
  have he1 : α+((n : ℝ)*α+1) = ((n+1 : ℕ) : ℝ)*α+1 := by push_cast; ring
  have he2 : α+(n : ℝ)*α = ((n+1 : ℕ) : ℝ)*α := by push_cast; ring
  rw [he1, he2]
  congr 1
  field_simp [(Real.Gamma_pos_of_pos hα).ne', (Real.Gamma_pos_of_pos hb).ne']

lemma mittagTerm_bound {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (ζ : 𝕜) (n : ℕ) (t : Icc (0 : ℝ) T) :
    ‖Spec.mittagTerm α ζ n t‖ ≤
      (‖ζ‖ * T ^ α)^n / Real.Gamma ((n : ℝ)*α+1) := by
  have hg : 0 < Real.Gamma ((n : ℝ)*α+1) := Real.Gamma_pos_of_pos (by positivity)
  rw [Spec.mittagTerm, norm_smul, norm_pow,
    Real.norm_of_nonneg (div_nonneg (Real.rpow_nonneg t.property.1 _) hg.le)]
  calc
    (t : ℝ)^((n : ℝ)*α) / Real.Gamma ((n : ℝ)*α+1) * ‖ζ‖^n ≤
        T^((n : ℝ)*α) / Real.Gamma ((n : ℝ)*α+1) * ‖ζ‖^n := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (Real.rpow_le_rpow t.property.1 t.property.2 (by positivity)) hg.le)
        (pow_nonneg (norm_nonneg ζ) n)
    _ = (‖ζ‖ * T^α)^n / Real.Gamma ((n : ℝ)*α+1) := by
      rw [mul_comm (n : ℝ) α, Real.rpow_mul_natCast hT, mul_pow]
      ring

lemma mittagTerm_eq {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (ζ : 𝕜) (n : ℕ) (t : Icc (0 : ℝ) T) :
    (ζ^n • mittagMonomial α hα n) t = Spec.mittagTerm α ζ n t := by
  simp only [ContinuousMap.smul_apply, mittagMonomial, ContinuousMap.coe_mk, Spec.mittagTerm]
  rw [smul_comm, smul_eq_mul, mul_one]

lemma mittag_series {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (ζ : 𝕜) :
    ∃ u : C(Icc (0 : ℝ) T, 𝕜),
      HasSum (fun n => ζ^n • mittagMonomial α hα n) u ∧
      (∀ t : Icc (0 : ℝ) T, HasSum (fun n => Spec.mittagTerm α ζ n t) (u t)) ∧
      TendstoUniformly
        (fun N (t : Icc (0 : ℝ) T) => ∑ n ∈ Finset.range N, Spec.mittagTerm α ζ n t)
        u atTop := by
  have hs := WeakVolterraBounds.summable_pow_div_gamma hα
    (show 0 ≤ ‖ζ‖ * T ^ α by positivity)
  have hb := mittagTerm_bound hα hT ζ
  have hsC : Summable (fun n => ζ^n • mittagMonomial (𝕜 := 𝕜) (T := T) α hα n) := by
    apply Summable.of_norm_bounded hs
    intro n
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    rw [mittagTerm_eq]
    exact hb n t
  refine ⟨∑' n, ζ^n • mittagMonomial α hα n, hsC.hasSum, ?_, ?_⟩
  · intro t
    simpa only [ContinuousMap.evalCLM_apply, mittagTerm_eq] using
      (ContinuousMap.evalCLM 𝕜 t).hasSum hsC.hasSum
  · have he (t : Icc (0 : ℝ) T) :
        (∑' n, ζ^n • mittagMonomial α hα n) t = ∑' n, Spec.mittagTerm α ζ n t := by
      have h : HasSum (fun n => Spec.mittagTerm α ζ n t)
          ((∑' n, ζ^n • mittagMonomial α hα n) t) := by
        simpa only [ContinuousMap.evalCLM_apply, mittagTerm_eq] using
          (ContinuousMap.evalCLM 𝕜 t).hasSum hsC.hasSum
      exact h.tsum_eq.symm
    convert tendstoUniformly_tsum_nat hs hb using 1
    exact funext he

/-- The normalized constant-amplitude equation, including the singleton interval. -/
theorem mittag_leffler : Spec.MittagLeffler := by
  intro 𝕜 _ α T hα hT ζ
  let k : C(triangle T, 𝕜) := ContinuousMap.const _ 1
  obtain ⟨V, hV, _, hb, _⟩ := WeakVolterraBounds.continuous_theorem α T hα hT k 1
    zero_le_one (fun z => by simp [k])
  let c : 𝕜 := ((Real.Gamma α)⁻¹ : ℝ)
  let J := c • V
  have hJ (f : C(Icc (0 : ℝ) T, 𝕜)) (t : Icc (0 : ℝ) T) :
      J f t = fractionalValue α (continuousExtension hT f) t := by
    change c * V f t = _
    rw [(hV f t).2, WeakVolterraBounds.constant_amplitude α 1 _ t t.property, one_mul]
    rw [fractionalValue, RCLike.real_smul_eq_coe_mul]
  obtain ⟨u, hu, hseries, hunif⟩ := mittag_series hα hT ζ
  let F : ℕ → C(Icc (0 : ℝ) T, 𝕜) := fun n => ζ^n • mittagMonomial α hα n
  have hF0 : F 0 = 1 := by
    ext t
    simp [F, mittagMonomial]
  have hshift (n : ℕ) : (ζ • J) (F n) = F (n+1) := by
    have hm : J (mittagMonomial α hα n) = mittagMonomial α hα (n+1) := by
      ext t
      rw [hJ, fractional_monomial hα hT]
    change ζ • J (ζ^n • mittagMonomial α hα n) = _
    rw [map_smul, hm, smul_smul]
    simp [F, pow_succ, mul_comm]
  have huF : HasSum F u := hu
  have htail : HasSum (fun n => F (n+1)) (u-1) := by
    simpa only [Finset.sum_range_one, hF0] using (hasSum_nat_add_iff' 1).mpr huF
  have hsum : HasSum (fun n => F (n+1)) ((ζ • J) u) := by
    simpa only [hshift] using (ζ • J).hasSum huF
  have heq : u - 1 = (ζ • J) u := htail.unique hsum
  have huEq (t : Icc (0 : ℝ) T) :
      u t = 1 + ζ * fractionalValue α (continuousExtension hT u) t := by
    have he := congrArg (fun f : C(Icc (0 : ℝ) T, 𝕜) => f t) heq
    change u t - 1 = ζ * J u t at he
    rw [hJ] at he
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  have hN := WeakVolterraBounds.neumann_of_iterate_bound hα hT zero_le_one V hb (ζ*c)
  let R := ∑' n : ℕ, (ζ*c)^n • V^n
  have hRJ : R * (1-ζ • J) = 1 := by
    simpa only [J, smul_smul, R] using hN.2.2.1
  have hsol (v : C(Icc (0 : ℝ) T, 𝕜))
      (hv : ∀ t, v t = 1 + ζ * fractionalValue α (continuousExtension hT v) t) :
      (1-ζ • J) v = 1 := by
    ext t
    change v t - ζ * J v t = 1
    rw [hJ, hv t]
    ring
  refine ⟨u, hseries, hunif, huEq, ?_, ?_⟩
  · intro v hv
    have hv' := congrArg (fun A : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜) => A v) hRJ
    have hu' := congrArg (fun A : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜) => A u) hRJ
    change R ((1-ζ • J) v) = v at hv'
    change R ((1-ζ • J) u) = u at hu'
    rw [hsol v hv] at hv'
    rw [hsol u huEq] at hu'
    exact hv'.symm.trans hu'
  · intro t ht
    rw [huEq, ht, ExpandedFA.PartV.FractionalIntegrals.fractional_zero_time, mul_zero, add_zero]

end ExpandedFA.PartV.WeakVolterraResolvent
