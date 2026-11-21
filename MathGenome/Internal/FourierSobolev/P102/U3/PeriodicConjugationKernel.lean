import MathGenome.Internal.FourierSobolev.Specs.P102.U3.PeriodicConjugationKernel
import MathGenome.Internal.FourierSobolev.P102.Periodic.Foundation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Polynomial periodic principal values (paper.tex:1186–1197).

The elementary cotangent/exponential identity gives the difference of the
cancelled integrands for adjacent Fourier modes as a finite smooth sum.
Induction and mode orthogonality evaluate its integral; complex conjugation
handles negative frequencies. Finite linearity handles all polynomials.
Oddness and dominated convergence then give ordinary symmetric principal values
along all positive real radii. All integrals retain the shared dt/T convention.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace P102.Periodic.Conjugation
open P102.Periodic.Expected

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The only zero of the kernel's sine denominator in a period is the origin. -/
lemma kernel_sin_ne_zero {t : ℝ} (ht : t ∈ Icc (-T / 2) (T / 2)) (ht0 : t ≠ 0) :
    Real.sin (Real.pi * t / T) ≠ 0 := by
  have hTpos : 0 < T := hT.out
  have hlo : -Real.pi < Real.pi * t / T := by
    apply (lt_div_iff₀ hTpos).2
    nlinarith [ht.1, ht.2, mul_pos Real.pi_pos hTpos]
  have hhi : Real.pi * t / T < Real.pi := by
    apply (div_lt_iff₀ hTpos).2
    nlinarith [ht.1, ht.2, mul_pos Real.pi_pos hTpos]
  rw [ne_eq, Real.sin_eq_zero_iff_of_lt_of_lt hlo hhi]
  exact div_ne_zero (mul_ne_zero Real.pi_ne_zero ht0) hTpos.ne'

/-- The elementary cancellation identity behind the finite-mode proof. -/
lemma cot_exp_identity (a : ℝ) (ha : Real.sin a ≠ 0) :
    (Real.cot a : ℂ) * (Complex.exp ((-2 * a : ℂ) * Complex.I) - 1) =
      -Complex.I * (Complex.exp ((-2 * a : ℂ) * Complex.I) + 1) := by
  rw [Real.cot_eq_cos_div_sin]
  have hs : (Real.sin a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hexp : Complex.exp ((-2 * a : ℂ) * Complex.I) =
      (Real.cos a : ℂ) ^ 2 - (Real.sin a : ℂ) ^ 2 -
        2 * (Real.sin a : ℂ) * (Real.cos a : ℂ) * Complex.I := by
    rw [show (-2 * (a : ℂ)) = ((-(2 * a) : ℝ) : ℂ) by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
      Complex.ofReal_pow, Complex.ofReal_one]
    have hsc : (Real.sin a : ℂ) ^ 2 + (Real.cos a : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq a
    linear_combination hsc
  rw [hexp]
  simp only [Complex.ofReal_div]
  field_simp [hs]
  have hsc : (Real.sin a : ℂ) ^ 2 + (Real.cos a : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq a
  linear_combination (norm := ring_nf) ((Real.cos a : ℂ) - Complex.I * (Real.sin a : ℂ)) * hsc
  simp [Complex.I_sq]

/-- A single frequency step removes the singularity. -/
lemma kernel_mode_step {t : ℝ} (ht : t ∈ Icc (-T / 2) (T / 2)) (ht0 : t ≠ 0) :
    coordinateKernel T t * (mode T 1 (-(t : Circle T)) - 1) =
      -(Complex.I / T) * (mode T 1 (-(t : Circle T)) + 1) := by
  have he : mode T 1 (-(t : Circle T)) =
      Complex.exp ((-2 * (Real.pi * t / T) : ℂ) * Complex.I) := by
    rw [← QuotientAddGroup.mk_neg, mode, fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [he, coordinateKernel]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv]
  have hc := cot_exp_identity _ (kernel_sin_ne_zero ht ht0)
  simp only [Complex.ofReal_div, Complex.ofReal_mul] at hc
  rw [mul_assoc, hc]
  ring

/-- Modes in the integration variable, with the convolution sign. -/
def backwardMode (T : ℝ) (n : ℤ) (t : ℝ) : ℂ := mode T n (-(t : Circle T))

omit hT in
lemma continuous_backwardMode (n : ℤ) : Continuous (backwardMode T n) :=
  (mode T n).continuous.comp ((AddCircle.continuous_mk' T).neg)

omit hT in
lemma integrableOn_backwardMode (n : ℤ) :
    IntegrableOn (backwardMode T n) (Ioo (-T / 2) (T / 2)) volume :=
  (continuous_backwardMode n).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self

lemma integral_backwardMode (n : ℤ) :
    (∫ t in Ioo (-T / 2) (T / 2), backwardMode T n t) =
      (T : ℂ) * if n = 0 then 1 else 0 := by
  have hn : (fun t : ℝ => backwardMode T n t) =
      (fun t : ℝ => mode T (-n) (t : Circle T)) := by
    funext t
    simp [backwardMode, mode, fourier_apply, smul_neg, neg_smul]
  rw [hn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [hT.out] : -T / 2 ≤ T / 2)]
  have hc := congrFun (fourierCoeff_fourier (T := T) (-n)) 0
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul] at hc
  have hi := P102.Periodic.haar_integral_interval T (mode T (-n)) (-T / 2)
  rw [show -T / 2 + T = T / 2 by ring] at hi
  change (∫ x, mode T (-n) x ∂haar T) = _ at hc
  rw [hi] at hc
  simp only [Pi.single_apply] at hc
  change (T⁻¹ : ℝ) • _ = _ at hc
  rw [Complex.real_smul] at hc
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.out.ne'
  rw [Complex.ofReal_inv] at hc
  simpa [hTc] using congrArg (fun z : ℂ => (T : ℂ) * z) hc

/-- Successive frequencies have a smooth, explicitly integrable difference. -/
lemma cancelled_mode_succ {t : ℝ} (ht : t ∈ Ioo (-T / 2) (T / 2)) (ht0 : t ≠ 0)
    (n : ℤ) :
    coordinateKernel T t * (backwardMode T (n + 1) t - 1) =
      coordinateKernel T t * (backwardMode T n t - 1) +
        -(Complex.I / T) * (backwardMode T (n + 1) t + backwardMode T n t) := by
  have hs := kernel_mode_step (Ioo_subset_Icc_self ht) ht0
  change coordinateKernel T t * (backwardMode T 1 t - 1) =
    -(Complex.I / T) * (backwardMode T 1 t + 1) at hs
  have hm : backwardMode T (n + 1) t = backwardMode T n t * backwardMode T 1 t :=
    fourier_add
  rw [hm]
  linear_combination backwardMode T n t * hs

/-- Absolute integrability and the multiplier value for each nonnegative frequency. -/
lemma cancelled_mode_nat (n : ℕ) :
    IntegrableOn (fun t => coordinateKernel T t * (backwardMode T (n : ℤ) t - 1))
      (Ioo (-T / 2) (T / 2)) volume ∧
    (∫ t in Ioo (-T / 2) (T / 2),
      coordinateKernel T t * (backwardMode T (n : ℤ) t - 1)) = symbol (n : ℤ) := by
  induction n with
  | zero => simp [backwardMode, mode, symbol]
  | succ n ih =>
    have hi := ((integrableOn_backwardMode (T := T) ((n : ℤ) + 1)).add
      (integrableOn_backwardMode (T := T) (n : ℤ))).const_mul (-(Complex.I / T))
    have he : (fun t => coordinateKernel T t * (backwardMode T ((n + 1 : ℕ) : ℤ) t - 1))
        =ᵐ[volume.restrict (Ioo (-T / 2) (T / 2))]
        (fun t => coordinateKernel T t * (backwardMode T (n : ℤ) t - 1) +
          -(Complex.I / T) * (backwardMode T ((n : ℤ) + 1) t + backwardMode T (n : ℤ) t)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo,
        ae_restrict_of_ae (show ∀ᵐ t : ℝ ∂volume, t ≠ 0 from by rw [ae_iff]; simp)] with t ht ht0
      simpa only [Nat.cast_add, Nat.cast_one] using cancelled_mode_succ ht ht0 (n : ℤ)
    refine ⟨(ih.1.add hi).congr he.symm, ?_⟩
    simp only [Pi.add_apply] at hi
    rw [integral_congr_ae he, integral_add ih.1 hi, ih.2,
      integral_const_mul, integral_add (integrableOn_backwardMode _) (integrableOn_backwardMode _),
      integral_backwardMode, integral_backwardMode]
    by_cases hn : n = 0
    · subst n
      simp [symbol, hT.out.ne', div_eq_mul_inv]
    · have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
      have hn1 : (n : ℤ) + 1 ≠ 0 := by omega
      simp [symbol, hn, hn1, Int.sign_eq_one_of_pos (show 0 < (n : ℤ) by omega)]

/-- Both signs of the frequency have the manuscript's multiplier. -/
lemma cancelled_mode (n : ℤ) :
    IntegrableOn (fun t => coordinateKernel T t * (backwardMode T n t - 1))
      (Ioo (-T / 2) (T / 2)) volume ∧
    (∫ t in Ioo (-T / 2) (T / 2),
      coordinateKernel T t * (backwardMode T n t - 1)) = symbol n := by
  cases n with
  | ofNat n => exact cancelled_mode_nat n
  | negSucc n =>
    have hi := cancelled_mode_nat (T := T) (n + 1)
    have he : (fun t => coordinateKernel T t * (backwardMode T (Int.negSucc n) t - 1)) =
        (fun t => conj (coordinateKernel T t * (backwardMode T ((n + 1 : ℕ) : ℤ) t - 1))) := by
      funext t
      rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega]
      simp only [backwardMode, mode, fourier_neg, map_mul, map_sub, map_one]
      rw [show conj (coordinateKernel T t) = coordinateKernel T t from Complex.conj_ofReal _]
    rw [he]
    refine ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp hi.1, ?_⟩
    change (∫ t in Ioo (-T / 2) (T / 2),
      Complex.conjCLE (coordinateKernel T t * (backwardMode T ((n + 1 : ℕ) : ℤ) t - 1))) = _
    rw [Complex.conjCLE.integral_comp_comm, hi.2]
    simp [symbol, Int.sign_negSucc]

omit hT in
lemma mode_shift (n : ℤ) (x : Circle T) (t : ℝ) :
    mode T n (x - (t : Circle T)) = mode T n x * backwardMode T n t := by
  simp [backwardMode, mode, fourier_apply, sub_eq_add_neg, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul]

omit hT in
lemma cancelled_synthesis_sum (c : ℤ →₀ ℂ) (x : Circle T) (t : ℝ) :
    coordinateKernel T t * (synthesis T c (x - (t : Circle T)) - synthesis T c x) =
      ∑ n ∈ c.support, (c n * mode T n x) *
        (coordinateKernel T t * (backwardMode T n t - 1)) := by
  simp only [synthesis, Finsupp.linearCombination_apply, Finsupp.sum,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mode_shift]
  ring

/-- The cancelled integral of every polynomial exists and is the finite multiplier action. -/
lemma cancelled_polynomial (c : ℤ →₀ ℂ) (x : Circle T) :
    IntegrableOn (fun t => coordinateKernel T t *
      (synthesis T c (x - (t : Circle T)) - synthesis T c x))
      (Ioo (-T / 2) (T / 2)) volume ∧
    cancelledValue T (synthesis T c) x = polynomialAction T c x := by
  have hi : ∀ n ∈ c.support, Integrable
      (fun t => (c n * mode T n x) * (coordinateKernel T t * (backwardMode T n t - 1)))
      (volume.restrict (Ioo (-T / 2) (T / 2))) := by
    intro n hn
    exact (cancelled_mode n).1.const_mul _
  constructor
  · simp_rw [cancelled_synthesis_sum]
    exact integrable_finsetSum _ hi
  · unfold cancelledValue
    simp_rw [cancelled_synthesis_sum]
    rw [integral_finsetSum _ hi]
    simp_rw [integral_const_mul, (cancelled_mode _).2]
    simp only [polynomialAction, Finsupp.linearCombination_apply, Finsupp.sum,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro n hn
    ring

lemma continuousAt_coordinateKernel {t : ℝ} (ht : t ∈ Icc (-T / 2) (T / 2))
    (ht0 : t ≠ 0) : ContinuousAt (coordinateKernel T) t := by
  have hs := kernel_sin_ne_zero ht ht0
  change ContinuousAt (fun s : ℝ => ((T⁻¹ * Real.cot (Real.pi * s / T) : ℝ) : ℂ)) t
  simp_rw [Real.cot_eq_cos_div_sin]
  fun_prop (disch := assumption)

/-- Every positive-radius truncation of a continuous function exists absolutely. -/
lemma integrableOn_truncation (f : C(Circle T, ℂ)) (x : Circle T) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t => coordinateKernel T t * f (x - (t : Circle T)))
      (Ioo (-T / 2) (T / 2) ∩ {t : ℝ | ε < |t|}) volume := by
  let K : Set ℝ := Icc (-T / 2) (T / 2) ∩ {t : ℝ | ε ≤ |t|}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hc : ContinuousOn (fun t => coordinateKernel T t * f (x - (t : Circle T))) K := by
    intro t ht
    have ht0 : t ≠ 0 := by intro hz; simpa [hz, not_le_of_gt hε] using ht.2
    exact (continuousAt_coordinateKernel ht.1 ht0).continuousWithinAt.mul
      (f.continuous.comp (continuous_const.sub (AddCircle.continuous_mk' T))).continuousAt.continuousWithinAt
  exact (hc.integrableOn_compact hK).mono_set (fun t ht => ⟨Ioo_subset_Icc_self ht.1, (show ε < |t| from ht.2).le⟩)

lemma coordinateKernel_neg (T t : ℝ) : coordinateKernel T (-t) = -coordinateKernel T t := by
  simp only [coordinateKernel, mul_neg, neg_div, Real.cot_eq_cos_div_sin,
    Real.cos_neg, Real.sin_neg, div_neg, Complex.ofReal_neg]

/-- Oddness cancels the constant term on every symmetric truncation. -/
lemma integral_kernel_truncation_zero (T ε : ℝ) :
    (∫ t in Ioo (-T / 2) (T / 2) ∩ {t : ℝ | ε < |t|}, coordinateKernel T t) = 0 := by
  let S : Set ℝ := Ioo (-T / 2) (T / 2) ∩ {t : ℝ | ε < |t|}
  have hS : MeasurableSet S := measurableSet_Ioo.inter (measurableSet_lt measurable_const continuous_abs.measurable)
  have hmem : ∀ t : ℝ, -t ∈ S ↔ t ∈ S := by
    intro t
    simp only [S, mem_inter_iff, mem_Ioo, mem_ofPred_eq, abs_neg]
    constructor <;> rintro ⟨⟨ha, hb⟩, hc⟩ <;> exact ⟨⟨by linarith, by linarith⟩, hc⟩
  have hodd : (fun t => S.indicator (coordinateKernel T) (-t)) =
      (fun t => -S.indicator (coordinateKernel T) t) := by
    funext t
    by_cases ht : t ∈ S
    · simp [ht, (hmem t).2 ht, coordinateKernel_neg]
    · simp [ht, mt (hmem t).1 ht]
  have hi := integral_neg_eq_self (S.indicator (coordinateKernel T)) volume
  rw [hodd, integral_neg, integral_indicator hS] at hi
  linear_combination -(1 / 2 : ℂ) * hi

lemma integrableOn_kernel_truncation {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (coordinateKernel T)
      (Ioo (-T / 2) (T / 2) ∩ {t : ℝ | ε < |t|}) volume := by
  simpa using integrableOn_truncation (T := T) (1 : C(Circle T, ℂ)) 0 hε

/-- The ordinary physical truncation equals the cancelled truncation. -/
lemma truncation_eq_cancelled_truncation (f : C(Circle T, ℂ)) (x : Circle T)
    {ε : ℝ} (hε : 0 < ε) :
    truncation T ε f x = ∫ t in Ioo (-T / 2) (T / 2) ∩ {t : ℝ | ε < |t|},
      coordinateKernel T t * (f (x - (t : Circle T)) - f x) := by
  simp_rw [mul_sub]
  rw [integral_sub (integrableOn_truncation f x hε)
    ((integrableOn_kernel_truncation hε).mul_const (f x)), integral_mul_const,
    integral_kernel_truncation_zero, zero_mul, sub_zero]
  rfl

omit hT in
/-- Removing symmetric neighborhoods of a null singleton recovers any integrable function. -/
lemma tendsto_cancelled_truncations {g : ℝ → ℂ}
    (hg : IntegrableOn g (Ioo (-T / 2) (T / 2)) volume) :
    Tendsto (fun ε : ℝ => ∫ t in Ioo (-T / 2) (T / 2) ∩ {t : ℝ | ε < |t|}, g t)
      (𝓝[>] 0) (𝓝 (∫ t in Ioo (-T / 2) (T / 2), g t)) := by
  let S : ℝ → Set ℝ := fun ε => {t | ε < |t|}
  have hS : ∀ ε, MeasurableSet (S ε) := fun ε =>
    measurableSet_lt measurable_const continuous_abs.measurable
  have heq : ∀ ε, (∫ t in Ioo (-T / 2) (T / 2), (S ε).indicator g t) =
      ∫ t in Ioo (-T / 2) (T / 2) ∩ {t : ℝ | ε < |t|}, g t := by
    intro ε
    rw [integral_indicator (hS ε), Measure.restrict_restrict (hS ε), inter_comm]
  simp_rw [← heq]
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun t => ‖g t‖)
  · exact Eventually.of_forall (fun ε => hg.aestronglyMeasurable.indicator (hS ε))
  · apply Eventually.of_forall
    intro ε
    exact ae_of_all _ (fun t => by
      by_cases ht : t ∈ S ε <;> simp [ht])
  · exact hg.norm
  · filter_upwards [ae_restrict_of_ae
      (show ∀ᵐ t : ℝ ∂volume, t ≠ 0 from by rw [ae_iff]; simp)] with t ht
    have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < |t| :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (abs_pos.mpr ht))
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with ε hε
    exact (indicator_of_mem (show t ∈ S ε from hε) g).symm

/-- Polynomial principal values with the original dt/T normalization, at every point. -/
theorem polynomial_principal_values : Expected.PolynomialPrincipalValuesStatement := by
  intro T hT c x
  have hc := cancelled_polynomial (T := T) c x
  refine ⟨fun ε hε => integrableOn_truncation (synthesis T c) x hε, hc.1, hc.2, ?_⟩
  rw [← hc.2]
  apply (tendsto_cancelled_truncations hc.1).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (truncation_eq_cancelled_truncation (synthesis T c) x hε).symm

end P102.Periodic.Conjugation
