import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.FractionalGronwall
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.BetaSemigroup
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.WeakVolterraResolvent

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ExpandedFA.PartV.FractionalGronwall
open ExpandedFA.PartV.FractionalIntegrals.Spec
open ExpandedFA.PartV.WeakVolterraResolvent.Spec
open ExpandedFA.PartV.WeakVolterraResolvent

/-- Positive kernels preserve the pointwise order on continuous functions. -/
lemma fractional_monotone {α T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    {f g : C(Icc (0 : ℝ) T, ℝ)} (hfg : f ≤ g) (t : Icc (0 : ℝ) T) :
    fractionalValue α (continuousExtension hT f) t ≤
      fractionalValue α (continuousExtension hT g) t := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.Gamma_pos_of_pos hα).le)
  apply integral_mono_ae
    (ExpandedFA.PartV.FractionalIntegrals.continuous_input_integrable hα hT f t)
    (ExpandedFA.PartV.FractionalIntegrals.continuous_input_integrable hα hT g t)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact mul_le_mul_of_nonneg_left (hfg _) (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)

lemma monotone_powers {T : ℝ}
    (A : C(Icc (0 : ℝ) T, ℝ) →L[ℝ] C(Icc (0 : ℝ) T, ℝ))
    (hA : Monotone A) (n : ℕ) : Monotone (A^n) := by
  induction n with
  | zero => simpa using (monotone_id : Monotone (id : C(Icc (0 : ℝ) T, ℝ) → _))
  | succ n ih =>
    intro f g hfg
    simpa only [pow_succ', mul_apply_eq_comp] using hA (ih hfg)

/-- Finite positive-operator iteration, without a norm-smallness assumption. -/
lemma finite_iteration {T : ℝ}
    (A : C(Icc (0 : ℝ) T, ℝ) →L[ℝ] C(Icc (0 : ℝ) T, ℝ))
    (hA : Monotone A) (z c : C(Icc (0 : ℝ) T, ℝ))
    (hz : z ≤ c + A z) (n : ℕ) :
    z ≤ (∑ j ∈ Finset.range n, (A^j) c) + (A^n) z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := monotone_powers A hA n hz
    rw [map_add] at h
    have he : (A^n) (A z) = (A^(n+1)) z := by
      rw [pow_succ, mul_apply_eq_comp]
    rw [he] at h
    calc
      z ≤ (∑ j ∈ Finset.range n, (A^j) c) + (A^n) z := ih
      _ ≤ (∑ j ∈ Finset.range n, (A^j) c) + ((A^n) c + (A^(n+1)) z) :=
        add_le_add le_rfl h
      _ = (∑ j ∈ Finset.range (n+1), (A^j) c) + (A^(n+1)) z := by
        rw [Finset.sum_range_succ, add_assoc]

lemma fractional_power_one {α T b : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (J : C(Icc (0 : ℝ) T, ℝ) →L[ℝ] C(Icc (0 : ℝ) T, ℝ))
    (hJ : ∀ f t, J f t = fractionalValue α (continuousExtension hT f) t)
    (n : ℕ) :
    ((b • J)^n) 1 = b^n • mittagMonomial α hα n := by
  induction n with
  | zero =>
    ext t
    simp [mittagMonomial]
  | succ n ih =>
    have hm : J (mittagMonomial α hα n) = mittagMonomial α hα (n+1) := by
      ext t
      rw [hJ, fractional_monomial hα hT]
    rw [pow_succ', mul_apply_eq_comp, ih]
    change b • J (b^n • mittagMonomial α hα n) = _
    rw [map_smul, hm, smul_smul]
    congr 1
    simp [pow_succ, mul_comm]

lemma mittagTerm_real (α b : ℝ) (n : ℕ) (t : ℝ) :
    mittagTerm α b n t = b^n * t^((n : ℝ)*α) / Real.Gamma ((n : ℝ)*α+1) := by
  simp only [mittagTerm, smul_eq_mul]
  ring

/-- Each comparison remainder is bounded by the manuscript's Gamma term. -/
theorem iteration_bound : Spec.IterationBound := by
  intro α b T a hα hb hT ha J hJ z hz hineq n t
  let A := b • J
  have hA : Monotone A := by
    intro f g hfg t
    change b * J f t ≤ b * J g t
    rw [hJ, hJ]
    exact mul_le_mul_of_nonneg_left (fractional_monotone hα hT hfg t) hb
  have hpow := fractional_power_one (b := b) hα hT J hJ
  have hvalue (j : ℕ) (s : Icc (0 : ℝ) T) :
      (A^j) 1 s = mittagTerm α b j s := by
    rw [hpow]
    exact mittagTerm_eq hα b j s
  have hconst (j : ℕ) : (A^j) (ContinuousMap.const _ a) = a • (A^j) 1 := by
    have hc : ContinuousMap.const (Icc (0 : ℝ) T) a = a • (1 : C(Icc (0 : ℝ) T, ℝ)) := by
      ext s
      simp
    rw [hc, map_smul]
  have hiter := finite_iteration A hA z (ContinuousMap.const _ a)
    (fun s => by simpa [A, hJ] using hineq s) n t
  have hsum : (∑ j ∈ Finset.range n, (A^j) (ContinuousMap.const _ a)) t =
      a * ∑ j ∈ Finset.range n, mittagTerm α b j (t : ℝ) := by
    simp only [ContinuousMap.sum_apply, hconst, ContinuousMap.smul_apply, smul_eq_mul, hvalue]
    rw [Finset.mul_sum]
  change z t ≤ _ + (A^n) z t at hiter
  rw [hsum] at hiter
  refine ⟨hiter, ?_, ?_⟩
  · have h := monotone_powers A hA n (show (0 : C(Icc (0 : ℝ) T, ℝ)) ≤ z from hz)
    have hzero : (A^n) (0 : C(Icc (0 : ℝ) T, ℝ)) = 0 := map_zero _
    rw [hzero] at h
    exact h t
  · have hzbound : z ≤ ‖z‖ • (1 : C(Icc (0 : ℝ) T, ℝ)) := by
      intro s
      change z s ≤ ‖z‖ * 1
      simpa only [mul_one] using (le_abs_self (z s)).trans (ContinuousMap.norm_coe_le_norm z s)
    have h := monotone_powers A hA n hzbound
    have ht := h t
    rw [map_smul] at ht
    change (A^n) z t ≤ ‖z‖ * (A^n) 1 t at ht
    rw [hvalue, mittagTerm_real] at ht
    exact ht

/-- Summability of every geometric numerator forces the entire Gamma
remainder to zero, uniformly even at the zero endpoint. -/
theorem gamma_remainder : Spec.GammaRemainder := by
  intro α b T C hα hb hT
  have hc : 0 ≤ b * T^α := mul_nonneg hb (Real.rpow_nonneg hT _)
  have hs := WeakVolterraBounds.summable_pow_div_gamma hα hc
  have hlim : Tendsto
      (fun n : ℕ => ‖C‖ * ((b * T^α)^n / Real.Gamma ((n : ℝ)*α+1)))
      atTop (𝓝 0) := by
    simpa using hs.tendsto_atTop_zero.const_mul ‖C‖
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn t
  rw [dist_comm, dist_eq_norm, sub_zero, norm_mul]
  apply lt_of_le_of_lt _ hn
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg C)
  rw [← mittagTerm_real]
  simpa only [Real.norm_of_nonneg hb] using mittagTerm_bound hα hT b n t

lemma mittagTerm_as_power {t : ℝ} (ht : 0 ≤ t) (α b : ℝ) (n : ℕ) :
    mittagTerm α b n t = (b * t^α)^n / Real.Gamma ((n : ℝ)*α+1) := by
  rw [mittagTerm_real, mul_comm (n : ℝ) α, Real.rpow_mul_natCast ht, mul_pow]

/-- Fractional Gronwall on the entire interval, with the explicit iteration
remainder above and no restriction on b*T^α. -/
theorem fractional_gronwall : Spec.ComparisonBound := by
  intro α T a b hα hT ha hb z hz hineq t
  obtain ⟨J, hJ⟩ := BetaSemigroup.continuous_realization (𝕜 := ℝ) hα hT
  have hiter := iteration_bound α b T a hα hb hT ha J hJ z hz hineq
  have hseries : HasSum (fun j : ℕ => mittagTerm α b j (t : ℝ))
      (Spec.mittagLeffler α (b * (t : ℝ)^α)) := by
    simpa only [mittagTerm_as_power t.property.1, Spec.mittagLeffler] using
      (WeakVolterraBounds.summable_pow_div_gamma hα
        (mul_nonneg hb (Real.rpow_nonneg t.property.1 α))).hasSum
  have hrem := (gamma_remainder α b T ‖z‖ hα hb hT).tendsto_at t
  have hlim := (hseries.tendsto_sum_nat.const_mul a).add hrem
  simp only [add_zero] at hlim
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun n =>
    (hiter n t).1.trans (add_le_add le_rfl (hiter n t).2.2)

end ExpandedFA.PartV.FractionalGronwall
