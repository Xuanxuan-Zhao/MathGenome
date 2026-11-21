import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.RareEventPoissonLimit
import Mathlib.Probability.Independence.CharacteristicFunction
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.LevyContinuity

/-! Theorem `rare-poisson`, paper.tex:3203–3222.
The proof compares the finite characteristic-function product with the
exponential of its linear term. All estimates allow an empty finite set. -/
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option maxHeartbeats 800000

namespace ProbabilityFoundations.Ch09

lemma bernoulli_parameter_le_rowMaximum {r : ℕ}
    (p : Fin r → Set.Icc (0 : ℝ) 1) (j : Fin r) :
    (p j : ℝ) ≤ bernoulliRowMaximum p := by
  exact_mod_cast (Finset.le_sup (f := fun j =>
    (⟨(p j : ℝ), (p j).property.1⟩ : ℝ≥0)) (Finset.mem_univ j))

@[simp] lemma bernoulliRowMaximum_empty (p : Fin 0 → Set.Icc (0 : ℝ) 1) :
    bernoulliRowMaximum p = 0 := by simp [bernoulliRowMaximum]

/-- Telescoping bound when both sets of factors lie in the closed unit disk. -/
lemma norm_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    have ha' : ∀ j ∈ s, ‖a j‖ ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hb' : ∀ j ∈ s, ‖b j‖ ≤ 1 := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hprod : ‖∏ j ∈ s, b j‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun j _ => norm_nonneg _) hb'
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      _ = ‖a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) +
          (a i - b i) * ∏ j ∈ s, b j‖ := by congr 1; ring
      _ ≤ ‖a i‖ * ‖∏ j ∈ s, a j - ∏ j ∈ s, b j‖ +
          ‖a i - b i‖ * ‖∏ j ∈ s, b j‖ := by
        simpa only [norm_mul] using norm_add_le
          (a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j))
          ((a i - b i) * ∏ j ∈ s, b j)
      _ ≤ 1 * (∑ j ∈ s, ‖a j - b j‖) + ‖a i - b i‖ * 1 := by
        gcongr
        · exact ha i (Finset.mem_insert_self _ _)
        · exact ih ha' hb'
      _ = _ := by ring

lemma norm_bernoulli_factor_le_one (p : Set.Icc (0 : ℝ) 1)
    {q : ℂ} (hq : ‖q‖ = 1) : ‖1 + (p : ℂ) * (q - 1)‖ ≤ 1 := by
  have hp : ‖(p : ℂ)‖ = (p : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg p.property.1]
  have hp' : ‖((1 - (p : ℝ) : ℝ) : ℂ)‖ = 1 - (p : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr p.property.2)]
  calc
    _ = ‖(p : ℂ) * q + ((1 - (p : ℝ) : ℝ) : ℂ)‖ := by push_cast; congr 1; ring
    _ ≤ ‖(p : ℂ) * q‖ + ‖((1 - (p : ℝ) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = 1 := by rw [norm_mul, hp, hp', hq]; ring

lemma norm_exp_bernoulli_le_one (p : Set.Icc (0 : ℝ) 1)
    {q : ℂ} (hq : ‖q‖ = 1) : ‖Complex.exp ((p : ℂ) * (q - 1))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hq' : q.re ≤ 1 := (Complex.re_le_norm q).trans_eq hq
  simpa using mul_nonpos_of_nonneg_of_nonpos p.property.1 (sub_nonpos.mpr hq')

lemma bernoulli_factor_exp_error (p : Set.Icc (0 : ℝ) 1) (hp : (p : ℝ) ≤ 1 / 2)
    {q : ℂ} (hq : ‖q‖ = 1) :
    ‖(1 + (p : ℂ) * (q - 1)) - Complex.exp ((p : ℂ) * (q - 1))‖ ≤
      4 * (p : ℝ) ^ 2 := by
  have hn : ‖(p : ℂ) * (q - 1)‖ ≤ 2 * (p : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg p.property.1]
    have hq' : ‖q - 1‖ ≤ 2 := by simpa only [hq, norm_one, one_add_one_eq_two] using norm_sub_le q 1
    nlinarith [mul_le_mul_of_nonneg_left hq' p.property.1]
  have hs : ‖(p : ℂ) * (q - 1)‖ ≤ 1 := by linarith
  calc
    _ = ‖Complex.exp ((p : ℂ) * (q - 1)) - 1 - (p : ℂ) * (q - 1)‖ := by
      rw [← norm_neg]; congr 1; ring
    _ ≤ ‖(p : ℂ) * (q - 1)‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hs
    _ ≤ 4 * (p : ℝ) ^ 2 := by nlinarith [norm_nonneg ((p : ℂ) * (q - 1))]

/-- The squared probabilities are bounded by maximum times sum. -/
lemma sum_sq_bernoulli_parameters_le {r : ℕ} (p : Fin r → Set.Icc (0 : ℝ) 1) :
    (∑ j, (p j : ℝ) ^ 2) ≤ bernoulliRowMaximum p * ∑ j, (p j : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  nlinarith [mul_le_mul_of_nonneg_right (bernoulli_parameter_le_rowMaximum p j)
    (p j).property.1]

/-- The real Poisson law has exactly the source's probability masses. -/
theorem poissonLaw_mass (rate : ℝ≥0) (k : ℕ) :
    (poissonLaw rate : Measure ℝ) {(k : ℝ)} =
      ENNReal.ofReal (Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ k / (k.factorial : ℝ)) := by
  change (poissonMeasure rate).map (Nat.cast : ℕ → ℝ) {(k : ℝ)} = _
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' {(k : ℝ)} = {k} := by
    ext n
    simp
  rw [hpre, poissonMeasure_singleton]

/-- Finite-row transform approximation, including the empty product. -/
lemma bernoulli_product_exp_error {r : ℕ} (p : Fin r → Set.Icc (0 : ℝ) 1)
    (hp : bernoulliRowMaximum p ≤ 1 / 2) {q : ℂ} (hq : ‖q‖ = 1) :
    ‖(∏ j, (1 + (p j : ℂ) * (q - 1))) -
      Complex.exp (((∑ j, (p j : ℝ)) : ℂ) * (q - 1))‖ ≤
      4 * bernoulliRowMaximum p * ∑ j, (p j : ℝ) := by
  have hsum : ((∑ j, (p j : ℝ)) : ℂ) * (q - 1) =
      ∑ j, (p j : ℂ) * (q - 1) := by rw [Finset.sum_mul]
  rw [hsum, Complex.exp_sum]
  calc
    _ ≤ ∑ j, ‖(1 + (p j : ℂ) * (q - 1)) -
        Complex.exp ((p j : ℂ) * (q - 1))‖ :=
      norm_prod_sub_prod_le_sum _ _ _
        (fun j _ => norm_bernoulli_factor_le_one (p j) hq)
        (fun j _ => norm_exp_bernoulli_le_one (p j) hq)
    _ ≤ ∑ j, 4 * (p j : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact bernoulli_factor_exp_error (p j)
        ((bernoulli_parameter_le_rowMaximum p j).trans hp) hq
    _ ≤ 4 * bernoulliRowMaximum p * ∑ j, (p j : ℝ) := by
      rw [← Finset.mul_sum, mul_assoc]
      exact mul_le_mul_of_nonneg_left (sum_sq_bernoulli_parameters_le p) (by norm_num)

/-- The analytic law of small numbers for the finite products. -/
lemma tendsto_bernoulli_products (r : ℕ → ℕ)
    (p : ∀ n, Fin (r n) → Set.Icc (0 : ℝ) 1) (rate : ℝ≥0)
    (hmax : Tendsto (fun n => bernoulliRowMaximum (p n)) atTop (𝓝 0))
    (hsum : Tendsto (fun n => ∑ j, (p n j : ℝ)) atTop (𝓝 (rate : ℝ)))
    {q : ℂ} (hq : ‖q‖ = 1) :
    Tendsto (fun n => ∏ j, (1 + (p n j : ℂ) * (q - 1))) atTop
      (𝓝 (Complex.exp ((rate : ℂ) * (q - 1)))) := by
  have hexp : Tendsto
      (fun n => Complex.exp (((∑ j, (p n j : ℝ)) : ℂ) * (q - 1))) atTop
      (𝓝 (Complex.exp ((rate : ℂ) * (q - 1))))  := by
    simpa only [Function.comp_def, Complex.ofReal_sum] using
      Complex.continuous_exp.continuousAt.tendsto.comp
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp hsum).mul_const (q - 1))
  apply hexp.congr_dist
  have hzero : Tendsto (fun n => 4 * bernoulliRowMaximum (p n) * ∑ j, (p n j : ℝ))
      atTop (𝓝 0) := by
    simpa using (hmax.const_mul 4).mul hsum
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hzero
  have hevent : ∀ᶠ n in atTop, bernoulliRowMaximum (p n) ≤ 1 / 2 :=
    ((tendsto_order.1 hmax).2 (1 / 2 : ℝ) (by norm_num)).mono fun _ hn => hn.le
  filter_upwards [hevent] with n hn
  simpa only [dist_eq_norm, norm_sub_rev] using bernoulli_product_exp_error (p n) hn hq

/-- The boundary parameter gives the point mass at zero. -/
theorem poissonLaw_zero : (poissonLaw 0 : Measure ℝ) = Measure.dirac 0 := by
  have hz : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
    apply Measure.ext_of_singleton
    intro k
    rw [poissonMeasure_singleton]
    by_cases hk : k = 0
    · subst k; simp
    · simp [hk, Ne.symm hk]
  change (poissonMeasure 0).map (Nat.cast : ℕ → ℝ) = _
  rw [hz, Measure.map_dirac' (by fun_prop)]
  simp

lemma charFun_bernoulli (p : Set.Icc (0 : ℝ) 1) (t : ℝ) :
    charFun (bernoulliMeasure (1 : ℝ) 0 p) t =
      1 + (p : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1) := by
  rw [charFun_apply, integral_bernoulliMeasure]
  simp only [Real.inner_apply, one_mul, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

universe u

/-- Independent rare Bernoulli events converge to the Poisson law; neither
identical distributions nor independence between different rows is imposed. -/
theorem rare_event_poisson_limit
    {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (r : ℕ → ℕ) (B : ∀ n, Fin (r n) → Ω n → ℝ)
    (p : ∀ n, Fin (r n) → Set.Icc (0 : ℝ) 1)
    (hB : ∀ n j, Measurable (B n j))
    (hInd : ∀ n, iIndepFun (B n) (P n))
    (hLaw : ∀ n j, (P n).map (B n j) = bernoulliMeasure (1 : ℝ) 0 (p n j))
    (rate : ℝ≥0)
    (hmax : Tendsto (fun n => bernoulliRowMaximum (p n)) atTop (𝓝 0))
    (hsum : Tendsto (fun n => ∑ j, (p n j : ℝ)) atTop (𝓝 (rate : ℝ))) :
    Tendsto (fun n => Ch06.probabilityLaw (P n)
      (fun ω => ∑ j, B n j ω) (by fun_prop)) atTop (𝓝 (poissonLaw rate)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have hcf (n : ℕ) :
      charFun (Ch06.probabilityLaw (P n) (fun ω => ∑ j, B n j ω) (by fun_prop)) t =
        ∏ j, (1 + (p n j : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
    change charFun ((P n).map (fun ω => ∑ j, B n j ω)) t = _
    simpa only [Finset.prod_apply, hLaw n, charFun_bernoulli] using
      congrFun ((hInd n).charFun_map_fun_sum_eq_prod
        (fun j => (hB n j).aemeasurable)) t
  simp_rw [hcf]
  change Tendsto _ _ (𝓝 (charFun ((poissonMeasure rate).map (Nat.cast : ℕ → ℝ)) t))
  rw [charFun_map_cast_poissonMeasure]
  exact tendsto_bernoulli_products r p rate hmax hsum (by simp)

end ProbabilityFoundations.Ch09
