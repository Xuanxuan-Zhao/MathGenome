import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch09.IndependentRowObjects
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.LevyContinuity
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.GaussianLaws
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.LindebergTheorem

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace ProbabilityFoundations.Ch09.IndependentRows
variable {r : ℕ → ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The elementary truncation bound, before taking the maximum. -/
theorem variance_le_lindeberg (R : Row r Ω) (n : ℕ) (j : Fin (r n))
    {ε : ℝ} (hε : 0 ≤ ε) : variance R n j ≤ ε ^ 2 + lindeberg R n ε := by
  let f := Set.indicator {ω | ε < |normalized R n j ω|}
    (fun ω => (normalized R n j ω)^2)
  have hf : Integrable f (R.μ n) := lindeberg_integrable R n j ε
  have hpoint (ω : Ω n) : (normalized R n j ω)^2 ≤ ε^2 + f ω := by
    by_cases h : ε < |normalized R n j ω|
    · simp [f, h, sq_nonneg]
    · simp only [f, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right h, add_zero]
      nlinarith [sq_abs (normalized R n j ω), le_of_not_gt h,
        abs_nonneg (normalized R n j ω)]
  have hi : variance R n j ≤ ε^2 + ∫ ω, f ω ∂R.μ n := by
    calc
      _ ≤ ∫ ω, ε^2 + f ω ∂R.μ n :=
        integral_mono (normalized_square_integrable R n j) ((integrable_const _).add hf) hpoint
      _ = _ := by rw [integral_add (integrable_const _) hf]; simp
  refine hi.trans (add_le_add_right ?_ _)
  exact Finset.single_le_sum (f := fun j => ∫ ω,
    Set.indicator {ω | ε < |normalized R n j ω|}
      (fun ω => (normalized R n j ω)^2) ω ∂R.μ n)
    (fun k _ => integral_nonneg fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω)
    (Finset.mem_univ j)

theorem maxVariance_le_lindeberg (R : Row r Ω) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    maxVariance R n ≤ ε^2 + lindeberg R n ε :=
  rowMax_le _ _ (add_nonneg (sq_nonneg _) (lindeberg_nonneg _ _ _))
    (fun j => variance_le_lindeberg R n j hε)

/-- Lindeberg's condition implies infinitesimal maximal variance. -/
theorem maxVariance_tendsto_zero (R : Row r Ω)
    (hL : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => lindeberg R n ε) atTop (𝓝 0)) :
    Tendsto (maxVariance R) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n => ha.trans_le (maxVariance_nonneg R n)
  · intro b hb
    obtain ⟨ε, hε, hεb⟩ : ∃ ε : ℝ, 0 < ε ∧ ε^2 < b / 2 := by
      refine ⟨min (b / 4) (1 / 2), lt_min (by positivity) (by norm_num), ?_⟩
      have h1 : min (b / 4) (1 / 2) ≤ b / 4 := min_le_left _ _
      have h2 : min (b / 4) (1 / 2) ≤ 1 / 2 := min_le_right _ _
      have h0 : 0 ≤ min (b / 4) (1 / 2) := le_min (by positivity) (by norm_num)
      nlinarith
    filter_upwards [(hL ε hε).eventually (gt_mem_nhds (show (0:ℝ) < b / 2 by positivity))] with n hn
    exact (maxVariance_le_lindeberg R n hε.le).trans_lt (by linarith)

theorem sum_measurable (R : Row r Ω) (n : ℕ) : Measurable (sum R n) :=
  Finset.measurable_sum _ (fun j _ => normalized_measurable R n j)

/-- Only within-row independence is used in this exact identity. -/
theorem charFun_sum (R : Row r Ω) (n : ℕ) (t : ℝ) :
    charFun ((R.μ n).map (sum R n)) t =
      ∏ j, charFun ((R.μ n).map (normalized R n j)) t := by
  change charFun ((R.μ n).map (fun ω => ∑ j, normalized R n j ω)) t = _
  simpa only [Finset.prod_apply] using congrFun
    ((normalized_independent R n).charFun_map_fun_sum_eq_prod
      (fun j => (normalized_measurable R n j).aemeasurable)) t


/-- The quadratic Taylor remainder of the unit-modulus exponential. -/
private def expRemainder (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I + (x : ℂ)^2 / 2

private lemma norm_expRemainder_series (x : ℝ) :
    ‖expRemainder x‖ ≤ |x|^3 * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((x : ℂ) * Complex.I) 3
  have he : (Complex.exp ((x : ℂ) * Complex.I) -
      ∑ m ∈ Finset.range 3, ((x : ℂ) * Complex.I)^m / (m.factorial : ℂ)) =
      expRemainder x := by
    simp [expRemainder, Finset.sum_range_succ, mul_pow, Complex.I_sq]
    ring
  rw [he] at h
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] using h

private lemma norm_expRemainder_small {x : ℝ} (hx : |x| ≤ 1) :
    ‖expRemainder x‖ ≤ Real.exp 1 * |x|^3 := by
  calc
    _ ≤ |x|^3 * Real.exp |x| := norm_expRemainder_series x
    _ ≤ |x|^3 * Real.exp 1 := by gcongr
    _ = _ := mul_comm _ _

private lemma norm_expRemainder_global (x : ℝ) :
    ‖expRemainder x‖ ≤ (Real.exp 1 + 4) * x^2 := by
  by_cases hx : |x| ≤ 1
  · calc
      _ ≤ Real.exp 1 * |x|^3 := norm_expRemainder_small hx
      _ ≤ Real.exp 1 * x^2 := by
        gcongr
        nlinarith [sq_abs x, abs_nonneg x]
      _ ≤ _ := by nlinarith [sq_nonneg x]
  · have hn : ‖expRemainder x‖ ≤ 2 + |x| + x^2 / 2 := by
      calc
        _ ≤ ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I‖ +
            ‖(x : ℂ)^2 / 2‖ := norm_add_le _ _
        _ ≤ (‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖) +
            ‖(x : ℂ) * Complex.I‖ + ‖(x : ℂ)^2 / 2‖ := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
        _ = _ := by simp [norm_pow, sq_abs]; norm_num
    have hx1 : 1 < |x| := lt_of_not_ge hx
    have hx2 : 1 ≤ x^2 := by nlinarith [sq_abs x]
    have hx3 : |x| ≤ x^2 := by nlinarith [sq_abs x]
    have he : 0 ≤ Real.exp 1 * x^2 := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    nlinarith

private lemma norm_expRemainder_truncation (t y ε : ℝ) (hε : 0 < ε)
    (htε : |t| * ε ≤ 1) :
    ‖expRemainder (t * y)‖ ≤ Real.exp 1 * |t|^3 * ε * y^2 +
      ((Real.exp 1 + 4) * t^2) *
        Set.indicator {y : ℝ | ε < |y|} (fun y => y^2) y := by
  by_cases hy : ε < |y|
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hy]
    have h := norm_expRemainder_global (t * y)
    rw [mul_pow] at h
    have hz : 0 ≤ Real.exp 1 * |t|^3 * ε * y^2 := by positivity
    nlinarith
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hy, mul_zero, add_zero]
    have hab : |t * y| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (le_of_not_gt hy) (abs_nonneg _)).trans htε
    calc
      _ ≤ Real.exp 1 * |t * y|^3 := norm_expRemainder_small hab
      _ = Real.exp 1 * |t|^3 * |y| * y^2 := by rw [abs_mul, mul_pow]; rw [show |y|^3 = |y| * y^2 by rw [pow_succ, sq_abs]; ring]; ring
      _ ≤ _ := by gcongr; exact le_of_not_gt hy


/-- Integrate the remainder using centering and the actual second moment. -/
private lemma integral_expRemainder (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (t : ℝ) :
    (∫ ω, expRemainder (t * normalized R n j ω) ∂R.μ n) =
      charFun ((R.μ n).map (normalized R n j)) t -
        (1 - ((t^2 / 2 * variance R n j : ℝ) : ℂ)) := by
  let Y := normalized R n j
  have hY : Measurable Y := normalized_measurable R n j
  have hlin : Integrable (fun ω => ((t : ℂ) * Complex.I) * (Y ω : ℂ)) (R.μ n) :=
    (normalized_integrable R n j).ofReal.const_mul _
  have hquad : Integrable (fun ω => ((t : ℂ)^2 / 2) * ((Y ω)^2 : ℝ)) (R.μ n) :=
    (normalized_square_integrable R n j).ofReal.const_mul _
  have hexp : Integrable (fun ω => Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I)) (R.μ n) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [] with ω
    rw [Complex.norm_exp]
    simp
  have he (ω) : expRemainder (t * Y ω) =
      Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I) - 1 -
        ((t : ℂ) * Complex.I) * (Y ω : ℂ) + ((t : ℂ)^2 / 2) * ((Y ω)^2 : ℝ) := by
    simp only [expRemainder, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  change (∫ ω, expRemainder (t * Y ω) ∂R.μ n) = _
  simp_rw [he]
  have ha := integral_add ((hexp.sub (integrable_const (1 : ℂ))).sub hlin) hquad
  have hs := integral_sub (hexp.sub (integrable_const (1 : ℂ))) hlin
  simp only [Pi.sub_apply] at ha hs
  rw [ha, hs, integral_sub hexp (integrable_const (1 : ℂ))]
  have hc : charFun ((R.μ n).map (normalized R n j)) t =
      ∫ ω, Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I) ∂R.μ n := by
    rw [charFun_apply_real, integral_map hY.aemeasurable (by fun_prop)]
    simp only [Complex.ofReal_mul]
  rw [hc]
  have hyint : (∫ ω, (Y ω : ℂ) ∂R.μ n) = 0 := by
    rw [integral_complex_ofReal, show (∫ ω, Y ω ∂R.μ n) = 0 from normalized_centered R n j]
    rfl
  have hysq : (∫ ω, ((Y ω)^2 : ℝ) ∂R.μ n : ℂ) = (variance R n j : ℂ) :=
    integral_complex_ofReal
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [hyint, hysq]
  simp only [mul_zero, sub_zero, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

/-- Uniform quadratic approximation, with the strict Lindeberg tail. -/
theorem charFun_quadratic_error (R : Row r Ω) (n : ℕ) (j : Fin (r n))
    (t ε : ℝ) (hε : 0 < ε) (htε : |t| * ε ≤ 1) :
    ‖charFun ((R.μ n).map (normalized R n j)) t -
        (1 - ((t^2 / 2 * variance R n j : ℝ) : ℂ))‖ ≤
      Real.exp 1 * |t|^3 * ε * variance R n j +
        ((Real.exp 1 + 4) * t^2) * ∫ ω,
          Set.indicator {ω | ε < |normalized R n j ω|}
            (fun ω => (normalized R n j ω)^2) ω ∂R.μ n := by
  rw [← integral_expRemainder]
  have hi := ((normalized_square_integrable R n j).const_mul (Real.exp 1 * |t|^3 * ε)).add
    ((lindeberg_integrable R n j ε).const_mul ((Real.exp 1 + 4) * t^2))
  calc
    _ ≤ ∫ ω, Real.exp 1 * |t|^3 * ε * (normalized R n j ω)^2 +
        ((Real.exp 1 + 4) * t^2) * Set.indicator {ω | ε < |normalized R n j ω|}
          (fun ω => (normalized R n j ω)^2) ω ∂R.μ n := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [] with ω
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.add_apply] using
        norm_expRemainder_truncation t (normalized R n j ω) ε hε htε
    _ = _ := by
      rw [integral_add ((normalized_square_integrable R n j).const_mul _)
        ((lindeberg_integrable R n j ε).const_mul _)]
      simp only [integral_const_mul, variance]


/-- A finite-product comparison for factors in the closed unit disk. -/
private lemma norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  revert hf hg
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    intro hf hg
    have hf' : ∀ k ∈ s, ‖f k‖ ≤ 1 := fun k hk => hf k (Finset.mem_insert_of_mem hk)
    have hg' : ∀ k ∈ s, ‖g k‖ ≤ 1 := fun k hk => hg k (Finset.mem_insert_of_mem hk)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      _ = ‖(f i - g i) * (∏ k ∈ s, f k) + g i * ((∏ k ∈ s, f k) - ∏ k ∈ s, g k)‖ := by
        congr 1; ring
      _ ≤ ‖(f i - g i) * (∏ k ∈ s, f k)‖ +
          ‖g i * ((∏ k ∈ s, f k) - ∏ k ∈ s, g k)‖ := norm_add_le _ _
      _ = ‖f i - g i‖ * ‖∏ k ∈ s, f k‖ +
          ‖g i‖ * ‖(∏ k ∈ s, f k) - ∏ k ∈ s, g k‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖f i - g i‖ * 1 + 1 * (∑ k ∈ s, ‖f k - g k‖) := by
        gcongr
        · exact (Finset.norm_prod_le s f).trans (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) hf')
        · exact hg i (Finset.mem_insert_self _ _)
        · exact ih hf' hg'
      _ = _ := by ring

private lemma gaussian_factor_error {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖(1 - (a : ℂ)) - Complex.exp ((-a : ℝ) : ℂ)‖ ≤ a^2 := by
  have hnorm : ‖((-a : ℝ) : ℂ)‖ ≤ 1 := by simpa [abs_of_nonneg ha] using ha1
  have h := Complex.norm_exp_sub_one_sub_id_le hnorm
  have he : (1 - (a : ℂ)) - Complex.exp ((-a : ℝ) : ℂ) =
      -(Complex.exp ((-a : ℝ) : ℂ) - 1 - ((-a : ℝ) : ℂ)) := by push_cast; ring
  rw [he, norm_neg]
  simpa [abs_of_nonneg ha] using h

/-- Sum of squared variances is controlled by the maximum. -/
theorem sum_variance_sq_le_max (R : Row r Ω) (n : ℕ) (h : 0 < varianceSum R n) :
    ∑ j, (variance R n j)^2 ≤ maxVariance R n := by
  calc
    _ ≤ ∑ j, maxVariance R n * variance R n j := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [mul_le_mul_of_nonneg_right (variance_le_max R n j) (variance_nonneg R n j)]
    _ = _ := by rw [← Finset.mul_sum, sum_variance_one R n h, mul_one]

/-- A quantitative finite-row comparison with the standard normal transform.
Its hypotheses about ε and the maximum will hold after fixing ε and taking n large. -/
theorem charFun_sum_error (R : Row r Ω) (n : ℕ) (hn : 0 < varianceSum R n)
    (t ε : ℝ) (hε : 0 < ε) (htε : |t| * ε ≤ 1)
    (hmax : (t^2 / 2) * maxVariance R n ≤ 1) :
    ‖charFun ((R.μ n).map (sum R n)) t - Complex.exp ((-(t^2 / 2) : ℝ) : ℂ)‖ ≤
      Real.exp 1 * |t|^3 * ε + (Real.exp 1 + 4) * t^2 * lindeberg R n ε +
        (t^2 / 2)^2 * maxVariance R n := by
  let q := t^2 / 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hgprod : (∏ j, Complex.exp ((-(q * variance R n j) : ℝ) : ℂ)) =
      Complex.exp ((-q : ℝ) : ℂ) := by
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum, sum_variance_one R n hn]
    simp
  rw [charFun_sum, ← hgprod]
  calc
    _ ≤ ∑ j, ‖charFun ((R.μ n).map (normalized R n j)) t -
        Complex.exp ((-(q * variance R n j) : ℝ) : ℂ)‖ := by
      apply norm_prod_sub_prod_le
      · intro j _
        have : IsProbabilityMeasure ((R.μ n).map (normalized R n j)) :=
          (Measure.isProbabilityMeasure_map_iff (normalized_measurable R n j).aemeasurable).2 inferInstance
        exact norm_charFun_le_one t
      · intro j _
        rw [Complex.norm_exp]
        simp only [Complex.ofReal_re]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hq (variance_nonneg R n j)))
    _ ≤ ∑ j, ((Real.exp 1 * |t|^3 * ε * variance R n j +
        (Real.exp 1 + 4) * t^2 * ∫ ω,
          Set.indicator {ω | ε < |normalized R n j ω|}
            (fun ω => (normalized R n j ω)^2) ω ∂R.μ n) +
        (q * variance R n j)^2) := by
      apply Finset.sum_le_sum
      intro j _
      have ha : q * variance R n j ≤ 1 :=
        (mul_le_mul_of_nonneg_left (variance_le_max R n j) hq).trans hmax
      exact (norm_sub_le_norm_sub_add_norm_sub _
        (1 - ((q * variance R n j : ℝ) : ℂ)) _).trans
          (add_le_add (charFun_quadratic_error R n j t ε hε htε)
            (gaussian_factor_error (mul_nonneg hq (variance_nonneg R n j)) ha))
    _ = Real.exp 1 * |t|^3 * ε + (Real.exp 1 + 4) * t^2 * lindeberg R n ε +
        q^2 * ∑ j, (variance R n j)^2 := by
      simp_rw [Finset.sum_add_distrib, mul_pow]
      rw [← Finset.mul_sum, sum_variance_one R n hn, mul_one,
        ← Finset.mul_sum, ← Finset.mul_sum]
      rfl
    _ ≤ _ := by gcongr; exact sum_variance_sq_le_max R n hn


/-- Pointwise convergence of transforms, deduced solely from Lindeberg's condition. -/
theorem charFun_sum_tendsto (R : Row r Ω) (hvar : ∀ n, 0 < varianceSum R n)
    (hL : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => lindeberg R n ε) atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => charFun ((R.μ n).map (sum R n)) t) atTop
      (𝓝 (Complex.exp ((-(t^2 / 2) : ℝ) : ℂ))) := by
  let A := Real.exp 1 * |t|^3
  let B := (Real.exp 1 + 4) * t^2
  let q := t^2 / 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hA1 : 0 < A + 1 := by positivity
  have hm := maxVariance_tendsto_zero R hL
  have hsmall : Tendsto (fun n => q * maxVariance R n) atTop (𝓝 0) := by
    simpa using hm.const_mul q
  apply Metric.tendsto_nhds.2
  intro δ hδ
  let ε := min (δ / (4 * (A + 1))) (1 / (|t| + 1))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have he1 : ε ≤ δ / (4 * (A + 1)) := min_le_left _ _
  have he2 : ε ≤ 1 / (|t| + 1) := min_le_right _ _
  have htε : |t| * ε ≤ 1 := by
    have h : (|t| + 1) * ε ≤ 1 :=
      by simpa only [mul_comm] using
        (le_div_iff₀ (show (0 : ℝ) < |t| + 1 by positivity)).mp he2
    nlinarith
  have hAε : A * ε < δ / 2 := by
    calc
      _ ≤ (A + 1) * ε := by nlinarith
      _ ≤ (A + 1) * (δ / (4 * (A + 1))) := mul_le_mul_of_nonneg_left he1 hA1.le
      _ = δ / 4 := by field_simp
      _ < δ / 2 := by linarith
  have hrest : Tendsto (fun n => B * lindeberg R n ε + q^2 * maxVariance R n)
      atTop (𝓝 0) := by
    simpa using ((hL ε hε).const_mul B).add (hm.const_mul (q^2))
  filter_upwards [hsmall.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hrest.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 2 by positivity))] with n hn hr
  rw [dist_eq_norm]
  have h := charFun_sum_error R n (hvar n) t ε hε htε hn.le
  change ‖_ - _‖ ≤ A * ε + B * lindeberg R n ε + q^2 * maxVariance R n at h
  exact h.trans_lt (by linarith)

/-- Lindeberg's central limit theorem for arbitrary finite independent rows.
The normalization is by the actual positive total standard deviation. -/
theorem lindeberg_central_limit (R : Row r Ω) (hvar : ∀ n, 0 < varianceSum R n)
    (hL : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => lindeberg R n ε) atTop (𝓝 0)) :
    TendstoInDistribution (sum R) atTop (id : ℝ → ℝ) R.μ (gaussianReal 0 1) where
  forall_aemeasurable n := (sum_measurable R n).aemeasurable
  tendsto := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.2
    intro t
    simpa [Measure.map_id, charFun_gaussianReal, neg_div] using
      charFun_sum_tendsto R hvar hL t

end ProbabilityFoundations.Ch09.IndependentRows
