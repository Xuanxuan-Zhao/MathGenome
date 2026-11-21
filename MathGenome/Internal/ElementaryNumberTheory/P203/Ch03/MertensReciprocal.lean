import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.MertensReciprocal
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.MertensWeighted
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.PartialSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Filter Set
open scoped Topology

namespace P203.MertensReciprocal
open P203Specs.MertensReciprocal
open P203Specs.MertensWeighted (M)

/-- The integrable logarithmic kernel. -/
noncomputable def kernel (t : ℝ) : ℝ := t⁻¹ / Real.log t ^ 2

/-- The bounded error of the first Mertens estimate, multiplied by the kernel. -/
noncomputable def remainder (t : ℝ) : ℝ := (M t - Real.log t) * kernel t

lemma measurable_M : Measurable M := by
  exact (measurable_from_nat (f := fun N : ℕ =>
    ∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) / (p : ℝ))).comp Nat.measurable_floor

lemma measurable_remainder : Measurable remainder := by
  exact (measurable_M.sub Real.measurable_log).mul
    (measurable_id.inv.div (Real.measurable_log.pow_const 2))

lemma kernel_nonneg {t : ℝ} (ht : 2 ≤ t) : 0 ≤ kernel t := by
  unfold kernel
  positivity

lemma integrable_remainder {C : ℝ} (hC : ∀ t : ℝ, 2 ≤ t → |M t - Real.log t| ≤ C) :
    IntegrableOn remainder (Ioi 2) := by
  apply ((integrableOn_inv_div_log_sq_Ioi (by norm_num : (1 : ℝ) < 2)).const_mul C).mono'
    measurable_remainder.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change |(M t - Real.log t) * kernel t| ≤ C * kernel t
  rw [abs_mul, abs_of_nonneg (kernel_nonneg ht.le)]
  exact mul_le_mul_of_nonneg_right (hC t ht.le) (kernel_nonneg ht.le)

lemma remainder_tail_bound {C x : ℝ} (hx : 2 ≤ x)
    (hC : ∀ t : ℝ, 2 ≤ t → |M t - Real.log t| ≤ C) :
    |∫ t in Ioi x, remainder t| ≤ C / Real.log x := by
  have hk := integrableOn_inv_div_log_sq_Ioi (show 1 < x by linarith)
  have h := norm_integral_le_of_norm_le (hk.const_mul C) (f := remainder) ?_
  · rw [integral_const_mul, integral_inv_div_log_sq_Ioi (show 1 < x by linarith)] at h
    simpa only [Real.norm_eq_abs, div_eq_mul_inv] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change |(M t - Real.log t) * kernel t| ≤ C * kernel t
    have ht2 : 2 ≤ t := hx.trans ht.le
    rw [abs_mul, abs_of_nonneg (kernel_nonneg ht2)]
    exact mul_le_mul_of_nonneg_right (hC t ht2) (kernel_nonneg ht2)

/-- Prime sums as positive-index partial sums, in the common real-cutoff convention. -/
lemma primeSum_eq_partialSum (f : ℕ → ℝ) (x : ℝ) :
    (∑ p ∈ P203Specs.PrimeProduct.primes x, f p) =
      P203.PartialSummation.partialSum (fun n => if n.Prime then f n else 0) x := by
  classical
  unfold P203Specs.PrimeProduct.primes P203.PartialSummation.partialSum
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨fun h => ⟨⟨h.2.one_le, h.1⟩, h.2⟩,
    fun h => ⟨h.1.2, h.2⟩⟩

lemma inv_log_weight {x : ℝ} (_hx : 2 ≤ x) :
    P203.PartialSummation.C1Weight (fun t => (Real.log t)⁻¹)
      (fun t => -kernel t) 2 x := by
  have h0 : ∀ t ∈ Icc (2 : ℝ) x, t ≠ 0 := by
    intro t ht; linarith [ht.1]
  have hl : ∀ t ∈ Icc (2 : ℝ) x, Real.log t ≠ 0 := by
    intro t ht
    exact (Real.log_pos (by linarith [ht.1] : 1 < t)).ne'
  have hc : ContinuousOn Real.log (Icc (2 : ℝ) x) := continuousOn_id.log h0
  refine ⟨hc.inv₀ hl, ?_, ?_⟩
  · exact ((continuousOn_id.inv₀ h0).div (hc.pow 2)
      (fun t ht => pow_ne_zero 2 (hl t ht))).neg
  · intro t ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have h1 : t ≠ 1 := by linarith [ht.1]
    have hn1 : t ≠ -1 := by linarith [ht.1]
    simpa only [kernel, neg_div] using
      (Real.hasDerivAt_inv_log h0 h1 hn1).hasDerivWithinAt

/-- Abel summation with the reciprocal logarithm weight. The lower endpoint is
kept explicitly, avoiding any change of the half-open interval convention. -/
lemma reciprocal_abel {x : ℝ} (hx : 2 ≤ x) :
    R x = M x / Real.log x +
      (∫ t in (2 : ℝ)..x, M t * kernel t) +
      (R 2 - M 2 / Real.log 2) := by
  classical
  let c : ℕ → ℝ := fun n => if n.Prime then Real.log (n : ℝ) / n else 0
  let r : ℕ → ℝ := fun n => if n.Prime then 1 / (n : ℝ) else 0
  have hM (t : ℝ) : P203.PartialSummation.partialSum c t = M t :=
    (primeSum_eq_partialSum (fun n => Real.log (n : ℝ) / n) t).symm
  have hR (t : ℝ) : P203.PartialSummation.partialSum r t = R t :=
    (primeSum_eq_partialSum (fun n => 1 / (n : ℝ)) t).symm
  have hterm (n : ℕ) : c n * (Real.log (n : ℝ))⁻¹ = r n := by
    dsimp [c, r]
    split_ifs with hp
    · have hl : Real.log (n : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      field_simp
    · simp
  have hab := P203.PartialSummation.abel ℝ c (fun t => (Real.log t)⁻¹)
    (fun t => -kernel t) 2 x hx (inv_log_weight hx)
  simp_rw [hM, hterm] at hab
  have hr := P203.PartialSummation.partialSum_decomposition_top r hx
  rw [hR, hR] at hr
  have hi : (∫ t in (2 : ℝ)..x, M t * -kernel t) =
      -(∫ t in (2 : ℝ)..x, M t * kernel t) := by
    simp only [mul_neg, intervalIntegral.integral_neg]
  rw [hi] at hab
  simp only [div_eq_mul_inv]
  linarith

/-- Separate the elementary log-log integral from the integrable remainder. -/
lemma integral_decomposition {C x : ℝ} (hx : 2 ≤ x)
    (hC : ∀ t : ℝ, 2 ≤ t → |M t - Real.log t| ≤ C) :
    (∫ t in (2 : ℝ)..x, M t * kernel t) =
      Real.log (Real.log x) - Real.log (Real.log 2) +
        ∫ t in (2 : ℝ)..x, remainder t := by
  have h0 : ∀ t ∈ uIcc (2 : ℝ) x, t ≠ 0 := by
    rw [uIcc_of_le hx]
    intro t ht; linarith [ht.1]
  have hl : ∀ t ∈ uIcc (2 : ℝ) x, Real.log t ≠ 0 := by
    rw [uIcc_of_le hx]
    intro t ht
    exact (Real.log_pos (by linarith [ht.1] : 1 < t)).ne'
  have hi : IntervalIntegrable (fun t => t⁻¹ / Real.log t) volume 2 x :=
    ((continuousOn_id.inv₀ h0).div (continuousOn_id.log h0) hl).intervalIntegrable
  have hF : IntervalIntegrable remainder volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
      ((integrable_remainder hC).mono_set Ioc_subset_Ioi_self)
  calc
    _ = ∫ t in (2 : ℝ)..x, (t⁻¹ / Real.log t + remainder t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htz := h0 t ht
      have htl := hl t ht
      dsimp [remainder, kernel]
      field_simp
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add hi hF,
        integral_inv_div_log (by norm_num : (1 : ℝ) < 2) (by linarith : 1 < x)]

/-- A convergent-integral choice of the constant term. The explicit endpoint
correction uses exactly the lower-endpoint convention of Abel summation. -/
noncomputable def mertensConstant : ℝ :=
  1 - Real.log (Real.log 2) + (R 2 - M 2 / Real.log 2) +
    ∫ t in Ioi (2 : ℝ), remainder t

lemma error_identity {C x : ℝ} (hx : 2 ≤ x)
    (hC : ∀ t : ℝ, 2 ≤ t → |M t - Real.log t| ≤ C) :
    R x - Real.log (Real.log x) - mertensConstant =
      (M x - Real.log x) / Real.log x - ∫ t in Ioi x, remainder t := by
  have hab := reciprocal_abel hx
  rw [integral_decomposition hx hC] at hab
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (integrable_remainder hC) hx
  have hl : Real.log x ≠ 0 := (Real.log_pos (by linarith : 1 < x)).ne'
  have hdiv : M x / Real.log x = 1 + (M x - Real.log x) / Real.log x := by
    field_simp
    ring
  rw [hdiv] at hab
  unfold mertensConstant
  linarith

/-- The second elementary Mertens estimate, with the constant term and the
reciprocal-logarithm error, uniformly for all real x ≥ 2. -/
theorem mertensReciprocal : Estimate := by
  obtain ⟨C, hC, hb⟩ := P203.MertensWeighted.weightedPrimeSum_bound
  refine ⟨mertensConstant, 2 * C, by positivity, 2, le_rfl, ?_⟩
  intro x hx
  rw [error_identity hx hb]
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    _ ≤ |(M x - Real.log x) / Real.log x| + |∫ t in Ioi x, remainder t| := abs_sub _ _
    _ ≤ C / Real.log x + C / Real.log x := by
      apply add_le_add
      · rw [abs_div, abs_of_pos hlog]
        exact div_le_div_of_nonneg_right (hb x hx) hlog.le
      · exact remainder_tail_bound hx hb
    _ = (2 * C) / Real.log x := by ring

/-- The quantitative estimate implies divergence of real-cutoff partial sums. -/
theorem reciprocalPrimes_diverge : Divergence := by
  obtain ⟨B, C, hC, X, hX, hb⟩ := mertensReciprocal
  have hl : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlower : Tendsto (fun x : ℝ => Real.log (Real.log x) + B - C) atTop atTop :=
    by simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-C) (tendsto_atTop_add_const_right atTop B hl)
  apply tendsto_atTop_mono' atTop _ hlower
  filter_upwards [eventually_ge_atTop X, Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with x hx hlog
  have he := (abs_le.mp (hb x hx)).1
  have hdiv : C / Real.log x ≤ C := div_le_self hC hlog
  linarith

end P203.MertensReciprocal
