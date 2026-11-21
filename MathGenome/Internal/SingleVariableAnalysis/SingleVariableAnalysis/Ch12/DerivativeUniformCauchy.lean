import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.MeanInequality
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.LinearRules
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.DerivativeUniformCauchy

/-!
# Uniform Cauchy convergence from derivative convergence

The mean inequality applied to F n - F m on the interval joining x₀ and x
bounds its oscillation by (b-a) M. Add its value at x₀. With derivative
errors and base-point errors each less than δ = ε/(4((b-a)+1)), this gives
a uniform Cauchy error less than ε/2. Scalar completeness, through the upstream
uniform Cauchy criterion, supplies a uniform limit on the closed interval.

The supremum version allows an infinite derivative supremum for early indices;
its finite case follows by using the real value of the supremum as M.
-/

namespace SingleVariableAnalysis

open Set
open scoped ENNReal

private theorem difference_bound_of_mean
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (mean : ∀ (f : ℝ → K) (u v M : ℝ), u < v → 0 ≤ M →
      ContinuousOn f (Icc u v) →
      (∀ t ∈ Ioo u v, DifferentiableAt ℝ f t) →
      (∀ t ∈ Ioo u v, ‖deriv f t‖ ≤ M) → ‖f v - f u‖ ≤ M * (v-u))
    (F : ℕ → ℝ → K) (a b x₀ x M : ℝ) (m n : ℕ)
    (_hab : a < b) (h₀ : x₀ ∈ Icc a b) (hx : x ∈ Icc a b) (hM : 0 ≤ M)
    (hc : ∀ k, ContinuousOn (F k) (Icc a b))
    (hd : ∀ k, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (F k) t)
    (hb : ∀ t ∈ Ioo a b, ‖deriv (F n) t - deriv (F m) t‖ ≤ M) :
    ‖F n x - F m x‖ ≤ ‖F n x₀ - F m x₀‖ + (b-a) * M := by
  let H : ℝ → K := fun t => F n t - F m t
  have step (u v : ℝ) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u < v) :
      ‖H v - H u‖ ≤ M * (v-u) := by
    apply mean H u v M huv hM
    · exact ((hc n).sub (hc m)).mono fun t ht =>
        ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩
    · intro t ht
      have ht' : t ∈ Ioo a b := ⟨hu.1.trans_lt ht.1, ht.2.trans_le hv.2⟩
      exact (hd n t ht').sub (hd m t ht')
    · intro t ht
      have ht' : t ∈ Ioo a b := ⟨hu.1.trans_lt ht.1, ht.2.trans_le hv.2⟩
      change ‖deriv (fun t => F n t - F m t) t‖ ≤ M
      rw [deriv_fun_sub (hd n t ht') (hd m t ht')]
      exact hb t ht'
  have osc : ‖H x - H x₀‖ ≤ (b-a) * M := by
    rcases lt_trichotomy x₀ x with h | h | h
    · exact (step x₀ x h₀ hx h).trans (by nlinarith [h₀.1, hx.2])
    · subst x
      simpa only [sub_self, norm_zero] using mul_nonneg (sub_nonneg.mpr (h₀.1.trans h₀.2)) hM
    · rw [norm_sub_rev]
      exact (step x x₀ hx h₀ h).trans (by nlinarith [hx.1, h₀.2])
  calc
    ‖F n x - F m x‖ = ‖(H x - H x₀) + H x₀‖ := by simp [H]
    _ ≤ ‖H x - H x₀‖ + ‖H x₀‖ := norm_add_le _ _
    _ ≤ ‖F n x₀ - F m x₀‖ + (b-a) * M := by dsimp [H] at *; linarith

private theorem sup_estimate_of_bound
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (F : ℕ → ℝ → K) (a b x₀ x : ℝ) (m n : ℕ) (hab : a < b)
    (bound : ∀ M : ℝ, 0 ≤ M →
      (∀ t ∈ Ioo a b, ‖deriv (F n) t - deriv (F m) t‖ ≤ M) →
      ‖F n x - F m x‖ ≤ ‖F n x₀ - F m x₀‖ + (b-a) * M) :
    ENNReal.ofReal ‖F n x - F m x‖ ≤
      ENNReal.ofReal ‖F n x₀ - F m x₀‖ + ENNReal.ofReal (b-a) *
        ⨆ t : Ioo a b, ENNReal.ofReal ‖deriv (F n) t - deriv (F m) t‖ := by
  let S : ℝ≥0∞ := ⨆ t : Ioo a b, ENNReal.ofReal ‖deriv (F n) t - deriv (F m) t‖
  change ENNReal.ofReal _ ≤ ENNReal.ofReal _ + ENNReal.ofReal (b-a) * S
  by_cases hS : S = ⊤
  · simp [hS, ENNReal.mul_top ((ENNReal.ofReal_ne_zero_iff).mpr (sub_pos.mpr hab))]
  have hb (t : ℝ) (ht : t ∈ Ioo a b) :
      ‖deriv (F n) t - deriv (F m) t‖ ≤ S.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hS).mp (le_iSup (fun t : Ioo a b =>
      ENNReal.ofReal ‖deriv (F n) t - deriv (F m) t‖) ⟨t, ht⟩)
  have h := ENNReal.ofReal_le_ofReal (bound S.toReal ENNReal.toReal_nonneg hb)
  simpa only [ENNReal.ofReal_add (norm_nonneg _) (mul_nonneg (sub_nonneg.mpr hab.le)
    ENNReal.toReal_nonneg), ENNReal.ofReal_mul (sub_nonneg.mpr hab.le),
    ENNReal.ofReal_toReal hS] using h

private theorem uniform_cauchy_of_difference_bound
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (F : ℕ → ℝ → K) (g : ℝ → K) (a b x₀ : ℝ) (hab : a < b)
    (bound : ∀ (x M : ℝ) (m n : ℕ), x ∈ Icc a b → 0 ≤ M →
      (∀ t ∈ Ioo a b, ‖deriv (F n) t - deriv (F m) t‖ ≤ M) →
      ‖F n x - F m x‖ ≤ ‖F n x₀ - F m x₀‖ + (b-a) * M)
    (hbase : ∃ L : K, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n ≥ N, ‖F n x₀ - L‖ < ε)
    (hderiv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n ≥ N, ∀ t : Ioo a b, ‖deriv (F n) t - g t‖ < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      ∀ x ∈ Icc a b, ‖F n x - F m x‖ < ε := by
  intro ε hε
  let δ : ℝ := ε / (4 * ((b-a)+1))
  have hD : 0 < (b-a)+1 := by linarith
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hD)
  obtain ⟨L, hL⟩ := hbase
  obtain ⟨N₀, h₀⟩ := hL δ hδ
  obtain ⟨N₁, h₁⟩ := hderiv δ hδ
  refine ⟨max N₀ N₁, ?_⟩
  intro m hm n hn x hx
  have hm₀ := (le_max_left N₀ N₁).trans hm
  have hn₀ := (le_max_left N₀ N₁).trans hn
  have hm₁ := (le_max_right N₀ N₁).trans hm
  have hn₁ := (le_max_right N₀ N₁).trans hn
  have hbase' : ‖F n x₀ - F m x₀‖ < 2 * δ := by
    calc
      _ ≤ ‖F n x₀ - L‖ + ‖F m x₀ - L‖ := by
        simpa only [norm_sub_rev (L)] using norm_sub_le_norm_sub_add_norm_sub (F n x₀) L (F m x₀)
      _ < δ + δ := add_lt_add (h₀ n hn₀) (h₀ m hm₀)
      _ = 2 * δ := by ring
  have hderiv' (t : ℝ) (ht : t ∈ Ioo a b) :
      ‖deriv (F n) t - deriv (F m) t‖ ≤ 2 * δ := by
    calc
      _ ≤ ‖deriv (F n) t - g t‖ + ‖deriv (F m) t - g t‖ :=
        by simpa only [norm_sub_rev (g t)] using
          norm_sub_le_norm_sub_add_norm_sub (deriv (F n) t) (g t) (deriv (F m) t)
      _ ≤ δ + δ := add_le_add (h₁ n hn₁ ⟨t, ht⟩).le (h₁ m hm₁ ⟨t, ht⟩).le
      _ = 2 * δ := by ring
  have hid : 2 * δ + (b-a) * (2 * δ) = ε / 2 := by
    dsimp [δ]
    field_simp
    ring
  calc
    _ ≤ ‖F n x₀ - F m x₀‖ + (b-a) * (2 * δ) :=
      bound x (2 * δ) m n hx (by positivity) hderiv'
    _ < 2 * δ + (b-a) * (2 * δ) := by linarith [hbase']
    _ = ε / 2 := hid
    _ < ε := half_lt_self hε

theorem real_derivative_difference_bound :
    ∀ (F : ℕ → ℝ → ℝ) (a b x₀ x M : ℝ) (m n : ℕ),
    a < b → x₀ ∈ Icc a b → x ∈ Icc a b → 0 ≤ M →
    (∀ k, ContinuousOn (F k) (Icc a b)) →
    (∀ k, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (F k) t) →
    (∀ t ∈ Ioo a b, |deriv (F n) t - deriv (F m) t| ≤ M) →
    |F n x - F m x| ≤ |F n x₀ - F m x₀| + (b - a) * M := by
  intro F a b x₀ x M m n hab h₀ hx hM hc hd hb
  have mean := fun (f : ℝ → ℝ) (u v M : ℝ) huv hM hc hd hb =>
    real_mean_inequality f u v M huv hM hc hd
      (by simpa only [Real.norm_eq_abs] using hb)
  simpa only [Real.norm_eq_abs] using difference_bound_of_mean
    (by simpa only [Real.norm_eq_abs] using mean)
    F a b x₀ x M m n hab h₀ hx hM hc hd
    (by simpa only [Real.norm_eq_abs] using hb)

theorem real_derivative_difference_sup_estimate :
    ∀ (F : ℕ → ℝ → ℝ) (a b x₀ x : ℝ) (m n : ℕ),
    a < b → x₀ ∈ Icc a b → x ∈ Icc a b →
    (∀ k, ContinuousOn (F k) (Icc a b)) →
    (∀ k, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (F k) t) →
    ENNReal.ofReal |F n x - F m x| ≤
      ENNReal.ofReal |F n x₀ - F m x₀| +
        ENNReal.ofReal (b - a) *
          ⨆ t : Ioo a b, ENNReal.ofReal |deriv (F n) t - deriv (F m) t| := by
  intro F a b x₀ x m n hab h₀ hx hc hd
  simpa only [Real.norm_eq_abs] using sup_estimate_of_bound F a b x₀ x m n hab
    (fun M hM hb => by
      simpa only [Real.norm_eq_abs] using real_derivative_difference_bound
        F a b x₀ x M m n hab h₀ hx hM hc hd
        (by simpa only [Real.norm_eq_abs] using hb))

theorem real_derivative_uniform_cauchy :
    ∀ (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a b x₀ : ℝ),
    a < b → x₀ ∈ Icc a b →
    (∀ n, ContinuousOn (F n) (Icc a b)) →
    (∀ n, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (F n) t) →
    (∃ L : ℝ, RealSequenceConverges
      (fun n => F n x₀) L) →
    RealUniformConverges
      (fun n (t : Ioo a b) => deriv (F n) t) (fun t => g t) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      ∀ x ∈ Icc a b, |F n x - F m x| < ε) ∧
    ∃ f : Icc a b → ℝ, RealUniformConverges
      (fun n (x : Icc a b) => F n x) f := by
  intro F g a b x₀ hab h₀ hc hd hbase hderiv
  have hC := uniform_cauchy_of_difference_bound F g a b x₀ hab
    (fun x M m n hx hM hb => by
      simpa only [Real.norm_eq_abs] using real_derivative_difference_bound
        F a b x₀ x M m n hab h₀ hx hM hc hd
        (by simpa only [Real.norm_eq_abs] using hb))
    (by simpa only [RealSequenceConverges, SequenceEventually, Real.norm_eq_abs] using hbase)
    (by simpa only [RealUniformConverges, Real.norm_eq_abs] using hderiv)
  have hC' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      ∀ x ∈ Icc a b, |F n x - F m x| < ε := by
    simpa only [Real.norm_eq_abs] using hC
  refine ⟨hC', (real_uniform_cauchy_criterion (fun n (x : Icc a b) => F n x)).mpr ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := hC' ε hε
  exact ⟨N, fun m hm n hn x => hN m hm n hn x x.property⟩

theorem complex_derivative_difference_bound :
    ∀ (F : ℕ → ℝ → ℂ) (a b x₀ x M : ℝ) (m n : ℕ),
    a < b → x₀ ∈ Icc a b → x ∈ Icc a b → 0 ≤ M →
    (∀ k, ContinuousOn (F k) (Icc a b)) →
    (∀ k, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (F k) t) →
    (∀ t ∈ Ioo a b, ‖deriv (F n) t - deriv (F m) t‖ ≤ M) →
    ‖F n x - F m x‖ ≤ ‖F n x₀ - F m x₀‖ + (b - a) * M := by
  intro F a b x₀ x M m n hab h₀ hx hM hc hd hb
  exact difference_bound_of_mean complex_mean_inequality F a b x₀ x M m n
    hab h₀ hx hM hc hd hb

theorem complex_derivative_difference_sup_estimate :
    ∀ (F : ℕ → ℝ → ℂ) (a b x₀ x : ℝ) (m n : ℕ),
    a < b → x₀ ∈ Icc a b → x ∈ Icc a b →
    (∀ k, ContinuousOn (F k) (Icc a b)) →
    (∀ k, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (F k) t) →
    ENNReal.ofReal ‖F n x - F m x‖ ≤
      ENNReal.ofReal ‖F n x₀ - F m x₀‖ +
        ENNReal.ofReal (b - a) *
          ⨆ t : Ioo a b, ENNReal.ofReal ‖deriv (F n) t - deriv (F m) t‖ := by
  intro F a b x₀ x m n hab h₀ hx hc hd
  exact sup_estimate_of_bound F a b x₀ x m n hab
    (fun M hM hb => complex_derivative_difference_bound
      F a b x₀ x M m n hab h₀ hx hM hc hd hb)

theorem complex_derivative_uniform_cauchy :
    ∀ (F : ℕ → ℝ → ℂ) (g : ℝ → ℂ) (a b x₀ : ℝ),
    a < b → x₀ ∈ Icc a b →
    (∀ n, ContinuousOn (F n) (Icc a b)) →
    (∀ n, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (F n) t) →
    (∃ L : ℂ, ComplexSequenceConverges
      (fun n => F n x₀) L) →
    ComplexUniformConverges
      (fun n (t : Ioo a b) => deriv (F n) t) (fun t => g t) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      ∀ x ∈ Icc a b, ‖F n x - F m x‖ < ε) ∧
    ∃ f : Icc a b → ℂ, ComplexUniformConverges
      (fun n (x : Icc a b) => F n x) f := by
  intro F g a b x₀ hab h₀ hc hd hbase hderiv
  have hC := uniform_cauchy_of_difference_bound F g a b x₀ hab
    (fun x M m n hx hM hb => complex_derivative_difference_bound
      F a b x₀ x M m n hab h₀ hx hM hc hd hb)
    hbase hderiv
  refine ⟨hC, (complex_uniform_cauchy_criterion (fun n (x : Icc a b) => F n x)).mpr ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := hC ε hε
  exact ⟨N, fun m hm n hn x => hN m hm n hn x x.property⟩

end SingleVariableAnalysis
