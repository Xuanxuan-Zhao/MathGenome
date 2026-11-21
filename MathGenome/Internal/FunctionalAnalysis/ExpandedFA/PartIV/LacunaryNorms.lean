import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.LacunaryNorms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Perm

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped Real ENNReal
namespace ExpandedFA.PartIV.LacunaryNorms
open LacunaryNormsSpec

@[simp] theorem frequency_zero : frequency 0 = 2 := by simp [frequency]

theorem frequency_succ (j : ℕ) : frequency (j + 1) = frequency j ^ 2 := by
  change 2 ^ (2 ^ (j + 1)) = (2 ^ (2 ^ j)) ^ 2
  rw [pow_succ, pow_mul]

theorem frequency_two_le (j : ℕ) : 2 ≤ frequency j := by
  exact Nat.le_pow (by positivity : 0 < 2 ^ j)

theorem frequency_doubling (j : ℕ) : 2 * frequency j ≤ frequency (j + 1) := by
  rw [frequency_succ]
  nlinarith [frequency_two_le j]

theorem increasing : Increasing := by
  apply strictMono_nat_of_lt_succ
  intro j
  have h := frequency_doubling j
  have hp := frequency_two_le j
  omega

theorem frequency_linear (j : ℕ) : 2 * (j + 1) ≤ frequency j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hd := frequency_doubling j
    omega

theorem frequency_sum_bound (j : ℕ) :
    (∑ k ∈ Finset.range (j + 1), frequency k) < 2 * frequency j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have hd := frequency_doubling j
    omega

/-- An explicit cutoff J=m works; it is independent of the coefficients. -/
theorem frequency_dominates (m j : ℕ) (hj : m ≤ j) :
    m * (∑ k ∈ Finset.range j, frequency k) < frequency j := by
  cases j with
  | zero => simp
  | succ j =>
    have hs := frequency_sum_bound j
    have hl := frequency_linear j
    have hp := frequency_two_le j
    have hb : (j + 1) * (∑ k ∈ Finset.range (j + 1), frequency k) <
        (j + 1) * (2 * frequency j) := Nat.mul_lt_mul_of_pos_left hs (by omega)
    have hc : (j + 1) * (2 * frequency j) ≤ frequency j ^ 2 := by nlinarith
    rw [frequency_succ]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hj) (hb.trans_le hc)

theorem tail_dominance : TailDominance := fun m => ⟨m, fun j hj => frequency_dominates m j hj⟩

/-- Base-expansion uniqueness on the tail, with bounded digits. -/
theorem tail_multiplicity : TailMultiplicity := by
  intro m
  refine ⟨m, ?_⟩
  intro N r q hsmall hbound hsum
  induction N with
  | zero => simp
  | succ N ih =>
    have hr : (∑ j ∈ Finset.range N, r j * frequency j) ≤
        m * (∑ j ∈ Finset.range N, frequency j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (hbound j).1
    have hq : (∑ j ∈ Finset.range N, q j * frequency j) ≤
        m * (∑ j ∈ Finset.range N, frequency j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (hbound j).2
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hsum
    have heq : r N = q N := by
      by_cases hN : N < m
      · exact (hsmall N hN).1.trans (hsmall N hN).2.symm
      · have hd := frequency_dominates m N (by omega)
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hmul := Nat.mul_le_mul_right (frequency N) (Nat.succ_le_of_lt hlt)
          simp only [Nat.succ_mul] at hmul
          omega
        · have hmul := Nat.mul_le_mul_right (frequency N) (Nat.succ_le_of_lt hgt)
          simp only [Nat.succ_mul] at hmul
          omega
    have hprev : (∑ j ∈ Finset.range N, r j * frequency j) =
        (∑ j ∈ Finset.range N, q j * frequency j) := by
      rw [heq] at hsum
      omega
    intro j hj
    by_cases hjN : j = N
    · simpa [hjN] using heq
    · exact ih hprev j (by omega)

theorem norm_polynomial_le_sum (s : Finset ℕ) (a : ℕ → ℂ) (t : LacunaryNormsSpec.Circle) :
    ‖polynomial s a t‖ ≤ ∑ j ∈ s, ‖a j‖ := by
  classical
  simp only [polynomial, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro j hj
  rw [norm_mul, fourier_apply, _root_.Circle.norm_coe, mul_one]

theorem head_bound : HeadBound := by
  intro J a t
  apply (norm_polynomial_le_sum _ _ _).trans
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range J)
    (fun _ => (1 : ℝ)) (fun j => ‖a j‖)
  simpa [coefficientNorm, coefficientSq] using h

theorem modes_orthonormal : Orthonormal ℂ
    (fun j : ℕ => fourierLp (T := 2 * π) 2 (frequency j : ℤ)) := by
  apply orthonormal_fourier.comp
  intro i j hij
  change (frequency i : ℤ) = (frequency j : ℤ) at hij
  exact increasing.injective (Int.natCast_inj.mp hij)

theorem polynomial_l2_sq (s : Finset ℕ) (a : ℕ → ℂ) :
    ‖ContinuousMap.toLp 2 μ ℂ (polynomial s a)‖ ^ 2 = coefficientSq s a := by
  classical
  rw [polynomial, map_sum]
  simp only [map_smul]
  exact modes_orthonormal.orthogonalFamily.norm_sum a s

theorem integral_norm_sq_toLp (f : C(LacunaryNormsSpec.Circle, ℂ)) :
    (∫ t, ‖f t‖ ^ 2 ∂μ) = ‖ContinuousMap.toLp 2 μ ℂ f‖ ^ 2 := by
  have h := ContinuousMap.inner_toLp (𝕜 := ℂ) μ f f
  rw [inner_self_eq_norm_sq_to_K] at h
  have he : (∫ t, f t * (starRingEnd ℂ) (f t) ∂μ) =
      ((∫ t, ‖f t‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      convert RCLike.mul_conj (f t) using 1; simp
  rw [he] at h
  have hh := congrArg RCLike.re h.symm
  simpa only [← RCLike.ofReal_pow, RCLike.ofReal_re, RCLike.re_to_complex,
    Complex.ofReal_re] using hh

theorem parseval : Parseval := by
  intro s a
  rw [integral_norm_sq_toLp, polynomial_l2_sq]

theorem polynomial_memLp (p : ℝ≥0∞) (s : Finset ℕ) (a : ℕ → ℂ) :
    MemLp (polynomial s a) p μ := by
  apply MemLp.of_bound (polynomial s a).continuous.aestronglyMeasurable ‖polynomial s a‖
  exact Filter.Eventually.of_forall fun t => ContinuousMap.norm_coe_le_norm _ t

theorem polynomialNorm_mono {p q : ℝ≥0∞} (hpq : p ≤ q)
    (s : Finset ℕ) (a : ℕ → ℂ) : polynomialNorm p s a ≤ polynomialNorm q s a := by
  exact ENNReal.toReal_mono (polynomial_memLp q s a).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le hpq)

theorem polynomialNorm_nonneg (p : ℝ≥0∞) (s : Finset ℕ) (a : ℕ → ℂ) :
    0 ≤ polynomialNorm p s a := ENNReal.toReal_nonneg

theorem coefficientSq_nonneg (s : Finset ℕ) (a : ℕ → ℂ) :
    0 ≤ coefficientSq s a := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem coefficientNorm_nonneg (s : Finset ℕ) (a : ℕ → ℂ) :
    0 ≤ coefficientNorm s a := Real.sqrt_nonneg _

theorem coefficientNorm_sq (s : Finset ℕ) (a : ℕ → ℂ) :
    coefficientNorm s a ^ 2 = coefficientSq s a := Real.sq_sqrt (coefficientSq_nonneg s a)

theorem polynomialNorm_pow (n : ℕ) (hn : 0 < n) (s : Finset ℕ) (a : ℕ → ℂ) :
    polynomialNorm (n : ℝ≥0∞) s a ^ n =
      ∫ t : LacunaryNormsSpec.Circle, ‖polynomial s a t‖ ^ n ∂μ := by
  have h := (polynomial_memLp (n : ℝ≥0∞) s a).eLpNorm_eq_integral_rpow_norm
    (by exact_mod_cast hn.ne') (by simp)
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast] at h
  unfold polynomialNorm
  rw [h, ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), inv_mul_cancel₀ (by positivity), Real.rpow_one]

theorem polynomialNorm_two (s : Finset ℕ) (a : ℕ → ℂ) :
    polynomialNorm 2 s a = coefficientNorm s a := by
  have h := polynomialNorm_pow 2 (by omega) s a
  change polynomialNorm 2 s a ^ 2 = _ at h
  rw [parseval] at h
  have hc := coefficientNorm_sq s a
  nlinarith [polynomialNorm_nonneg 2 s a, coefficientNorm_nonneg s a]

/-- Cauchy–Schwarz in a form with no fractional powers. -/
theorem continuous_cauchy_schwarz (f g : C(LacunaryNormsSpec.Circle, ℝ)) :
    (∫ t, f t * g t ∂μ) ^ 2 ≤
      (∫ t, f t ^ 2 ∂μ) * (∫ t, g t ^ 2 ∂μ) := by
  have h := real_inner_mul_inner_self_le (ContinuousMap.toLp 2 μ ℝ f)
    (ContinuousMap.toLp 2 μ ℝ g)
  rw [ContinuousMap.inner_toLp, ContinuousMap.inner_toLp, ContinuousMap.inner_toLp] at h
  simpa only [RCLike.conj_to_real, ← sq, mul_comm] using h

/-- The L¹/L²/L⁴ interpolation used for the reverse coefficient bound. -/
theorem continuous_moment_interpolation (f : C(LacunaryNormsSpec.Circle, ℝ))
    (hf : ∀ t, 0 ≤ f t) :
    (∫ t, f t ^ 2 ∂μ) ^ 3 ≤ (∫ t, f t ∂μ) ^ 2 * (∫ t, f t ^ 4 ∂μ) := by
  let g : C(LacunaryNormsSpec.Circle, ℝ) := ⟨fun t => Real.sqrt (f t), f.continuous.sqrt⟩
  have hg (t) : g t ^ 2 = f t := Real.sq_sqrt (hf t)
  have hA := continuous_cauchy_schwarz g (f * g)
  have heA : (fun t => g t * (f * g) t) = fun t => f t ^ 2 := by
    funext t
    change g t * (f t * g t) = _
    nlinarith only [hg t]
  have heB : (fun t => (f * g) t ^ 2) = fun t => f t ^ 3 := by
    funext t
    change (f t * g t) ^ 2 = _
    rw [mul_pow, hg]
    ring
  simp only [heA, hg, heB] at hA
  have hB := continuous_cauchy_schwarz f (f ^ 2)
  have heC : (fun t => f t * (f ^ 2) t) = fun t => f t ^ 3 := by
    funext t
    simp only [ContinuousMap.pow_apply]
    ring
  have heD : (fun t => (f ^ 2) t ^ 2) = fun t => f t ^ 4 := by
    funext t
    simp only [ContinuousMap.pow_apply, ← pow_mul]
  simp only [heC, heD] at hB
  have h1 : 0 ≤ ∫ t, f t ∂μ := integral_nonneg hf
  have h2 : 0 ≤ ∫ t, f t ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have h3 : 0 ≤ ∫ t, f t ^ 3 ∂μ := integral_nonneg fun t => pow_nonneg (hf t) _
  have h4 : 0 ≤ ∫ t, f t ^ 4 ∂μ := integral_nonneg fun t => pow_nonneg (hf t) _
  have hA2 := (sq_le_sq₀ (sq_nonneg _) (mul_nonneg h1 h3)).mpr hA
  have hB2 := mul_le_mul_of_nonneg_left hB (sq_nonneg (∫ t, f t ∂μ))
  rcases h2.eq_or_lt with hz | hp
  · calc
      (∫ t, f t ^ 2 ∂μ) ^ 3 = 0 := by rw [← hz]; norm_num
      _ ≤ _ := mul_nonneg (sq_nonneg _) h4
  · apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [hA2, hB2]

theorem polynomialNorm_one (s : Finset ℕ) (a : ℕ → ℂ) :
    polynomialNorm 1 s a = ∫ t : LacunaryNormsSpec.Circle, ‖polynomial s a t‖ ∂μ := by
  simpa only [Nat.cast_one, pow_one] using polynomialNorm_pow 1 (by omega) s a

/-- A uniform fourth-moment upper bound gives a uniform L¹ lower bound. -/
theorem lower_bound_of_fourth (C : ℝ) (hC : 0 < C)
    (hupper : ∀ (s : Finset ℕ) (a : ℕ → ℂ),
      polynomialNorm 4 s a ≤ C * coefficientNorm s a)
    (s : Finset ℕ) (a : ℕ → ℂ) :
    (C ^ 2)⁻¹ * coefficientNorm s a ≤ polynomialNorm 1 s a := by
  let A := coefficientNorm s a
  let B := polynomialNorm 1 s a
  let D := polynomialNorm 4 s a
  have hA : 0 ≤ A := coefficientNorm_nonneg s a
  have hB : 0 ≤ B := polynomialNorm_nonneg 1 s a
  have hD : 0 ≤ D := polynomialNorm_nonneg 4 s a
  have hinter := continuous_moment_interpolation
    (⟨fun t => ‖polynomial s a t‖, (polynomial s a).continuous.norm⟩)
    (by intro t; change 0 ≤ ‖polynomial s a t‖; exact norm_nonneg _)
  change (∫ t : LacunaryNormsSpec.Circle, ‖polynomial s a t‖ ^ 2 ∂μ) ^ 3 ≤
    (∫ t : LacunaryNormsSpec.Circle, ‖polynomial s a t‖ ∂μ) ^ 2 *
      (∫ t : LacunaryNormsSpec.Circle, ‖polynomial s a t‖ ^ 4 ∂μ) at hinter
  rw [parseval, ← coefficientNorm_sq, ← polynomialNorm_one,
    ← polynomialNorm_pow 4 (by omega)] at hinter
  change (A ^ 2) ^ 3 ≤ B ^ 2 * D ^ 4 at hinter
  have hd : D ≤ C * A := hupper s a
  have hd4 := pow_le_pow_left₀ hD hd 4
  have hh := hinter.trans (mul_le_mul_of_nonneg_left hd4 (sq_nonneg B))
  rcases hA.eq_or_lt with hz | hp
  · change (C ^ 2)⁻¹ * A ≤ B
    rw [← hz, mul_zero]
    exact hB
  · have hsq : A ^ 2 ≤ (C ^ 2 * B) ^ 2 := by
      apply (mul_le_mul_iff_right₀ (pow_pos hp 4)).mp
      nlinarith only [hh]
    have hle : A ≤ C ^ 2 * B :=
      (sq_le_sq₀ hA (mul_nonneg (sq_nonneg C) hB)).mp hsq
    change (C ^ 2)⁻¹ * A ≤ B
    calc
      (C ^ 2)⁻¹ * A ≤ (C ^ 2)⁻¹ * (C ^ 2 * B) :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (sq_nonneg C))
      _ = B := by rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hC.ne'), one_mul]

/-- All analytic norm comparisons follow from the even upper estimates. -/
theorem norm_equivalence_of_even_upper (hEven : EvenNormUpper) : NormEquivalence := by
  intro p hp hpfin
  obtain ⟨D, hD, hDupper⟩ := hEven 2 (by omega)
  have hfour : ∀ (s : Finset ℕ) (a : ℕ → ℂ),
      polynomialNorm 4 s a ≤ D * coefficientNorm s a := by simpa using hDupper
  obtain ⟨m, hm⟩ := exists_nat_gt p.toReal
  have hmpos : 0 < m := by
    have := ENNReal.toReal_nonneg (a := p)
    by_contra h
    have : m = 0 := by omega
    simp [this] at hm
    linarith
  have hpq : p ≤ ((2 * m : ℕ) : ℝ≥0∞) := by
    apply (ENNReal.toReal_le_toReal hpfin (by finiteness)).mp
    simp only [ENNReal.toReal_natCast]
    push_cast
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨C, hC, hupper⟩ := hEven m hmpos
  refine ⟨(D ^ 2)⁻¹, C, inv_pos.mpr (pow_pos hD _), hC, ?_⟩
  intro s a
  exact ⟨(lower_bound_of_fourth D hD hfour s a).trans (polynomialNorm_mono hp s a),
    (polynomialNorm_mono hpq s a).trans (hupper s a)⟩

theorem coefficientNorm_mono {s t : Finset ℕ} (hst : s ⊆ t) (a : ℕ → ℂ) :
    coefficientNorm s a ≤ coefficientNorm t a := by
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun _ _ _ => sq_nonneg _)

theorem polynomialNorm_toLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (s : Finset ℕ) (a : ℕ → ℂ) :
    polynomialNorm p s a = ‖ContinuousMap.toLp p μ ℂ (polynomial s a)‖ := by
  rw [Lp.norm_def]
  exact congrArg ENNReal.toReal
    (eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (p := p) (𝕜 := ℂ) μ _)).symm

theorem polynomialNorm_le_bound (p : ℝ≥0∞) (s : Finset ℕ) (a : ℕ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ t : LacunaryNormsSpec.Circle, ‖polynomial s a t‖ ≤ C) :
    polynomialNorm p s a ≤ C := by
  have hb := eLpNorm_le_of_ae_bound (μ := μ) (p := p)
    (polynomial s a).continuous.aestronglyMeasurable (Filter.Eventually.of_forall h)
  simp only [measure_univ, ENNReal.one_rpow, one_mul] at hb
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal hC)

theorem norm_polynomial_le_card (s : Finset ℕ) (a : ℕ → ℂ) (t : LacunaryNormsSpec.Circle) :
    ‖polynomial s a t‖ ≤ Real.sqrt (s.card : ℝ) * coefficientNorm s a := by
  apply (norm_polynomial_le_sum s a t).trans
  have h := Real.sum_mul_le_sqrt_mul_sqrt s (fun _ => (1 : ℝ)) (fun j => ‖a j‖)
  simpa [coefficientNorm, coefficientSq] using h

/-- Finite heads can be adjoined to the exact tail-moment estimate.
A deliberately nonoptimal positive constant avoids a choice of roots. -/
theorem even_upper_of_tail (htail : TailEvenMoment) : EvenNormUpper := by
  classical
  intro m hm
  obtain ⟨J, hJ⟩ := htail m hm
  let M : ℝ := m.factorial
  have hM : 1 ≤ M := by
    change (1 : ℝ) ≤ (m.factorial : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos m)
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hC : 0 < Real.sqrt (J : ℝ) + M := by
    have := Real.sqrt_nonneg (J : ℝ)
    linarith
  refine ⟨Real.sqrt (J : ℝ) + M, hC, ?_⟩
  intro s a
  let sh := s.filter (fun j => j < J)
  let st := s.filter (fun j => ¬j < J)
  have hsh : sh ⊆ s := Finset.filter_subset _ _
  have hst : st ⊆ s := Finset.filter_subset _ _
  have hcard : sh.card ≤ J := by
    calc sh.card ≤ (Finset.range J).card := Finset.card_le_card (by
            intro j hj
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
         _ = J := Finset.card_range _
  have hhead : polynomialNorm ((2 * m : ℕ) : ℝ≥0∞) sh a ≤
      Real.sqrt (J : ℝ) * coefficientNorm s a := by
    apply polynomialNorm_le_bound _ _ _ _
      (mul_nonneg (Real.sqrt_nonneg _) (coefficientNorm_nonneg s a))
    intro t
    exact (norm_polynomial_le_card sh a t).trans
      (mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hcard))
        (coefficientNorm_mono hsh a) (coefficientNorm_nonneg sh a) (by positivity))
  have hmoment := hJ st a (by
    intro j hj
    exact Nat.le_of_not_gt (Finset.mem_filter.mp hj).2)
  have htailnorm : polynomialNorm ((2 * m : ℕ) : ℝ≥0∞) st a ≤
      M * coefficientNorm s a := by
    apply le_of_pow_le_pow_left₀ (by omega : 2 * m ≠ 0) (mul_nonneg hM0 (coefficientNorm_nonneg s a))
    rw [polynomialNorm_pow _ (by omega)]
    calc
      _ ≤ M * coefficientSq st a ^ m := hmoment
      _ ≤ M * (coefficientNorm s a ^ 2) ^ m := by
        rw [← coefficientNorm_sq]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity)
            (pow_le_pow_left₀ (coefficientNorm_nonneg st a) (coefficientNorm_mono hst a) 2) m) hM0
      _ ≤ (M * coefficientNorm s a) ^ (2 * m) := by
        have hpow : M ≤ M ^ (2 * m) := by
          simpa only [pow_one] using pow_le_pow_right₀ hM (by omega : 1 ≤ 2 * m)
        simp only [mul_pow, ← pow_mul]
        exact mul_le_mul_of_nonneg_right hpow (pow_nonneg (coefficientNorm_nonneg s a) _)
  have hp : 1 ≤ ((2 * m : ℕ) : ℝ≥0∞) := by exact_mod_cast (by omega : 1 ≤ 2 * m)
  have : Fact (1 ≤ ((2 * m : ℕ) : ℝ≥0∞)) := ⟨hp⟩
  have hsplit : polynomial s a = polynomial sh a + polynomial st a := by
    exact (Finset.sum_filter_add_sum_filter_not s (fun j => j < J)
      (fun j => a j • fourier (frequency j : ℤ))).symm
  have htriangle : polynomialNorm ((2 * m : ℕ) : ℝ≥0∞) s a ≤
      polynomialNorm ((2 * m : ℕ) : ℝ≥0∞) sh a +
        polynomialNorm ((2 * m : ℕ) : ℝ≥0∞) st a := by
    simp only [polynomialNorm_toLp]
    rw [hsplit, map_add]
    exact norm_add_le _ _
  calc
    _ ≤ Real.sqrt (J : ℝ) * coefficientNorm s a + M * coefficientNorm s a :=
      htriangle.trans (add_le_add hhead htailnorm)
    _ = _ := by ring

/-- Analytic assembly of the full finite-family norm conclusion. -/
theorem norm_equivalence_of_tail (htail : TailEvenMoment) : NormEquivalence :=
  norm_equivalence_of_even_upper (even_upper_of_tail htail)


theorem tuple_permutation_of_equal_counts {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (f g : Fin m → ι)
    (h : ∀ i, (Finset.univ.filter (fun k => f k = i)).card =
      (Finset.univ.filter (fun k => g k = i)).card) :
    ∃ σ : Equiv.Perm (Fin m), g = f ∘ σ := by
  classical
  let e : ∀ i, {k // g k = i} ≃ {k // f k = i} := fun i =>
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype] using (h i).symm)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext k
  exact (Equiv.ofFiberEquiv_map e k).symm

theorem tuple_frequency_matching (m : ℕ) : ∃ J : ℕ,
    ∀ (s : Finset ℕ), (∀ j ∈ s, J ≤ j) → ∀ (f g : Fin m → s),
    (∑ k, frequency (f k)) = (∑ k, frequency (g k)) →
    ∃ σ : Equiv.Perm (Fin m), g = f ∘ σ := by
  classical
  obtain ⟨J, hJ⟩ := tail_multiplicity m
  refine ⟨J, ?_⟩
  intro s hs f g heq
  let N := s.sup id + 1
  let r (j : ℕ) := (Finset.univ.filter (fun k => (f k : ℕ) = j)).card
  let q (j : ℕ) := (Finset.univ.filter (fun k => (g k : ℕ) = j)).card
  have hlt (i : s) : (i : ℕ) < N := Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)
  have hsum (F : Fin m → s) :
      (∑ j ∈ Finset.range N,
        (Finset.univ.filter (fun k => (F k : ℕ) = j)).card * frequency j) =
        ∑ k, frequency (F k) := by
    simpa only [Finset.sum_const, smul_eq_mul] using
      (Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin m)))
        (t := Finset.range N) (g := fun k => (F k : ℕ))
        (fun k _ => Finset.mem_range.mpr (hlt (F k))) frequency)
  have hz (F : Fin m → s) (j : ℕ) (hj : j < J) :
      (Finset.univ.filter (fun k => (F k : ℕ) = j)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro k _ hk
    have hb := hs (F k) (F k).property
    omega
  have hbound (F : Fin m → s) (j : ℕ) :
      (Finset.univ.filter (fun k => (F k : ℕ) = j)).card ≤ m := by
    exact (Finset.card_filter_le _ _).trans_eq (by simp)
  have hsmall : ∀ j, j < J → r j = 0 ∧ q j = 0 := by
    exact fun j hj => ⟨hz f j hj, hz g j hj⟩
  have hbounds : ∀ j, r j ≤ m ∧ q j ≤ m := fun j => ⟨hbound f j, hbound g j⟩
  have hweighted : (∑ j ∈ Finset.range N, r j * frequency j) =
      ∑ j ∈ Finset.range N, q j * frequency j := by
    exact (hsum f).trans (heq.trans (hsum g).symm)
  have hunique : ∀ j, j < N → r j = q j :=
    hJ N r q hsmall hbounds hweighted
  apply tuple_permutation_of_equal_counts f g
  intro i
  let j : ℕ := i
  suffices (Finset.univ.filter (fun k => (f k : ℕ) = j)).card =
      (Finset.univ.filter (fun k => (g k : ℕ) = j)).card by
    simpa only [Subtype.ext_iff] using this
  by_cases hj : j < N
  · exact hunique j hj
  · have hzero (F : Fin m → s) :
        (Finset.univ.filter (fun k => (F k : ℕ) = j)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro k _ hk
      have := hlt (F k)
      omega
    rw [hzero f, hzero g]


lemma tuple_relation_class_card_le {ι : Type*} [Fintype ι] (m : ℕ)
    (R : (Fin m → ι) → (Fin m → ι) → Prop) [DecidableRel R]
    (hR : ∀ f g, R f g → ∃ σ : Equiv.Perm (Fin m), g = f ∘ σ)
    (f : Fin m → ι) :
    (Finset.univ.filter (R f)).card ≤ m.factorial := by
  classical
  calc
    (Finset.univ.filter (R f)).card ≤
        (Finset.univ.image (fun σ : Equiv.Perm (Fin m) => f ∘ σ)).card := by
      apply Finset.card_le_card
      intro g hg
      obtain ⟨σ, hσ⟩ := hR f g (Finset.mem_filter.mp hg).2
      exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ σ, hσ.symm⟩
    _ ≤ Fintype.card (Equiv.Perm (Fin m)) := by
      exact Finset.card_image_le
    _ = m.factorial := by simp [Fintype.card_perm]

lemma tuple_relation_sum_le {ι : Type*} [Fintype ι] (m : ℕ)
    (b : ι → ℝ)
    (R : (Fin m → ι) → (Fin m → ι) → Prop) [DecidableRel R]
    (hR : ∀ f g, R f g → ∃ σ : Equiv.Perm (Fin m), g = f ∘ σ) :
    (∑ f : Fin m → ι, ∑ g : Fin m → ι,
      if R f g then (∏ k, b (f k)) * (∏ k, b (g k)) else 0) ≤
      (m.factorial : ℝ) * (∑ i, b i ^ 2) ^ m := by
  classical
  calc
    _ = ∑ f : Fin m → ι,
        ((Finset.univ.filter (R f)).card : ℝ) * (∏ k, b (f k)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [← Finset.sum_filter]
      have hinv : ∀ g ∈ Finset.univ.filter (R f),
          (∏ k, b (f k)) * (∏ k, b (g k)) = (∏ k, b (f k)) ^ 2 := by
        intro g hg
        obtain ⟨σ, rfl⟩ := hR f g (Finset.mem_filter.mp hg).2
        have hprod := Equiv.prod_comp σ (fun k => b (f k))
        simp only [Function.comp_apply] at *
        rw [hprod, pow_two]
      rw [Finset.sum_congr rfl hinv]
      simp
    _ ≤ ∑ f : Fin m → ι, (m.factorial : ℝ) * (∏ k, b (f k)) ^ 2 := by
      apply Finset.sum_le_sum
      intro f hf
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact Nat.cast_le.mpr (tuple_relation_class_card_le m R hR f)
    _ = (m.factorial : ℝ) * (∑ i, b i ^ 2) ^ m := by
      rw [← Finset.mul_sum, Fintype.sum_pow]
      congr 1
      apply Finset.sum_congr rfl
      intro f hf
      rw [Finset.prod_pow]


open scoped ComplexConjugate

private theorem fourier_product {ι : Type*} (s : Finset ι) (n : ι → ℤ)
    (t : LacunaryNormsSpec.Circle) :
    (∏ i ∈ s, fourier (n i) t) = fourier (∑ i ∈ s, n i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih, fourier_add]

private theorem fourier_tuple_expansion {ι : Type*} [Fintype ι] (b : ι → ℂ)
    (n : ι → ℤ) (m : ℕ) :
    (∑ i, b i • fourier (T := 2 * π) (n i)) ^ m =
      ∑ f : Fin m → ι, (∏ k, b (f k)) • fourier (∑ k, n (f k)) := by
  classical
  ext t
  simp only [ContinuousMap.pow_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Finset.prod_mul_distrib, fourier_product]


private theorem fourier_sum_l2_sq {ι : Type*} [Fintype ι] (b : ι → ℂ) (n : ι → ℤ) :
    ‖∑ i, b i • fourierLp (T := 2 * π) 2 (n i)‖ ^ 2 =
      ∑ i, ∑ j, if n i = n j then (b j * conj (b i)).re else 0 := by
  classical
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    orthonormal_iff_ite.mp (orthonormal_fourier (T := 2 * π))]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp_all [mul_comm]

private theorem fourier_sum_l2_sq_le {ι : Type*} [Fintype ι] (b : ι → ℂ) (n : ι → ℤ) :
    ‖∑ i, b i • fourierLp (T := 2 * π) 2 (n i)‖ ^ 2 ≤
      ∑ i, ∑ j, if n i = n j then ‖b i‖ * ‖b j‖ else 0 := by
  classical
  rw [fourier_sum_l2_sq]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  split_ifs
  · exact (Complex.re_le_norm _).trans_eq (by simp [mul_comm])
  · exact le_rfl

private theorem fourier_even_moment_le {ι : Type*} [Fintype ι] (b : ι → ℂ)
    (n : ι → ℤ) (m : ℕ) :
    (∫ t : LacunaryNormsSpec.Circle,
      ‖∑ i, b i * fourier (n i) t‖ ^ (2 * m) ∂μ) ≤
      ∑ f : Fin m → ι, ∑ g : Fin m → ι,
        if (∑ k, n (f k)) = ∑ k, n (g k) then
          (∏ k, ‖b (f k)‖) * (∏ k, ‖b (g k)‖) else 0 := by
  classical
  let P : C(LacunaryNormsSpec.Circle, ℂ) := ∑ i, b i • fourier (n i)
  have hpoint (t : LacunaryNormsSpec.Circle) :
      ‖∑ i, b i * fourier (n i) t‖ ^ (2 * m) = ‖(P ^ m) t‖ ^ 2 := by
    simp only [ContinuousMap.pow_apply, P, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul, norm_pow]
    rw [← pow_mul, Nat.mul_comm m 2]
  simp_rw [hpoint]
  rw [integral_norm_sq_toLp, fourier_tuple_expansion, map_sum]
  simp only [map_smul]
  convert fourier_sum_l2_sq_le (fun f : Fin m → ι => ∏ k, b (f k))
    (fun f : Fin m → ι => ∑ k, n (f k)) using 1
  simp only [norm_prod]

private theorem fourier_even_moment_le_nat {ι : Type*} [Fintype ι] (b : ι → ℂ)
    (n : ι → ℕ) (m : ℕ) :
    (∫ t : LacunaryNormsSpec.Circle,
      ‖∑ i, b i * fourier (n i : ℤ) t‖ ^ (2 * m) ∂μ) ≤
      ∑ f : Fin m → ι, ∑ g : Fin m → ι,
        if (∑ k, n (f k)) = ∑ k, n (g k) then
          (∏ k, ‖b (f k)‖) * (∏ k, ‖b (g k)‖) else 0 := by
  classical
  simpa only [← Nat.cast_sum, Int.natCast_inj] using
    fourier_even_moment_le b (fun i => (n i : ℤ)) m

/-- The exact factorial tail-moment estimate, for the same fixed sequence at
all moment orders and for every finite complex coefficient family. -/
theorem tail_even_moment : TailEvenMoment := by
  classical
  intro m hm
  obtain ⟨J, hJ⟩ := tuple_frequency_matching m
  refine ⟨J, ?_⟩
  intro s a hs
  have hmoment := fourier_even_moment_le_nat
    (fun i : s => a i) (fun i : s => frequency i) m
  have hcount := tuple_relation_sum_le m (fun i : s => ‖a i‖)
    (fun f g : Fin m → s => (∑ k, frequency (f k)) = ∑ k, frequency (g k))
    (hJ s hs)
  have hpoly (t : LacunaryNormsSpec.Circle) :
      (∑ i : s, a i * fourier (frequency i : ℤ) t) = polynomial s a t := by
    simp only [polynomial, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    exact Finset.sum_coe_sort s (fun i => a i * fourier (frequency i : ℤ) t)
  have htotal := hmoment.trans hcount
  rw [Finset.sum_coe_sort s (fun i => ‖a i‖ ^ 2)] at htotal
  simpa only [hpoly, coefficientSq] using htotal

/-- Uniform upper estimates at all even exponents, including the finite head. -/
theorem even_norm_upper : EvenNormUpper := even_upper_of_tail tail_even_moment

/-- Two-sided coefficient and Lp norm bounds for every finite p≥1, with the
fixed frequencies 2^(2^j) and constants independent of the finite family. -/
theorem norm_equivalence : NormEquivalence := norm_equivalence_of_tail tail_even_moment

end ExpandedFA.PartIV.LacunaryNorms
