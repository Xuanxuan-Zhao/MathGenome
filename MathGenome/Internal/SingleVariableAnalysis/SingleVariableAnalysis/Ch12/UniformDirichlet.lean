import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.SummationParts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.UniformDirichlet
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform Dirichlet test

The finite Abel transformation is the proved upstream tail identity.
A real monotone null sequence has constant sign; its absolute variation
therefore telescopes. Partial sums anchored at p have norm at most 2M,
which gives the exact finite-tail estimate 2M |b p|. Its uniform decay
makes the ordered product partial sums uniformly Cauchy. The upstream
real and complex uniform Cauchy criteria supply the respective limits.
-/
namespace SingleVariableAnalysis

open scoped BigOperators
universe u

/-- Absolute variation of a real monotone null sequence, in either direction. -/
theorem monotone_null_variation (b : ℕ → ℝ)
    (hm : Monotone b ∨ Antitone b)
    (hlim : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |b n| < ε)
    (p q : ℕ) (hpq : p ≤ q) :
    |b q| + (∑ n ∈ Finset.Ico p q, |b n - b (n + 1)|) = |b p| := by
  have hstep : ∀ n, |b n - b (n + 1)| = |b n| - |b (n + 1)| := by
    rcases hm with hm | hm
    · have hsign : ∀ n, b n ≤ 0 := by
        intro n
        by_contra h
        have hpos : 0 < b n := lt_of_not_ge h
        obtain ⟨N, hN⟩ := hlim (b n) hpos
        have hsmall := hN (max n N) (le_max_right n N)
        have hlarge := hm (le_max_left n N)
        have habs := le_abs_self (b (max n N))
        linarith
      intro n
      rw [abs_of_nonpos (sub_nonpos.mpr (hm (Nat.le_succ n))),
        abs_of_nonpos (hsign n), abs_of_nonpos (hsign (n + 1))]
      ring
    · have hsign : ∀ n, 0 ≤ b n := by
        intro n
        by_contra h
        have hneg : b n < 0 := lt_of_not_ge h
        obtain ⟨N, hN⟩ := hlim (-b n) (neg_pos.mpr hneg)
        have hsmall := hN (max n N) (le_max_right n N)
        have hlarge := hm (le_max_left n N)
        have habs := neg_abs_le (b (max n N))
        linarith
      intro n
      rw [abs_of_nonneg (sub_nonneg.mpr (hm (Nat.le_succ n))),
        abs_of_nonneg (hsign n), abs_of_nonneg (hsign (n + 1))]
  induction q, hpq using Nat.le_induction with
  | base => simp
  | succ q hpq ih =>
    rw [Finset.sum_Ico_succ_top hpq, hstep q]
    linarith

/-- Finite Dirichlet estimate, shared by the two canonical scalar fields. -/
theorem dirichlet_tail_bound {K : Type*} [RCLike K]
    (a : ℕ → K) (b : ℕ → ℝ) (M : ℝ)
    (ha : ∀ N, ‖∑ n ∈ Finset.range (N + 1), a n‖ ≤ M)
    (hm : Monotone b ∨ Antitone b)
    (hb : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |b n| < ε)
    (p q : ℕ) (hpq : p ≤ q) :
    ‖∑ n ∈ Finset.Icc p q, a n * (b n : K)‖ ≤ 2 * M * |b p| := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (ha 0)
  have hprefix : ∀ n, ‖∑ j ∈ Finset.range n, a j‖ ≤ M := by
    intro n
    cases n with
    | zero => simpa using hM
    | succ n => exact ha n
  have htail : ∀ n, p ≤ n → ‖∑ j ∈ Finset.Icc p n, a j‖ ≤ 2 * M := by
    intro n hpn
    have hid := Finset.sum_Ico_eq_sub a (Nat.le_succ_of_le hpn)
    simp only [Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc] at hid
    rw [hid]
    calc
      ‖(∑ j ∈ Finset.range (n + 1), a j) - ∑ j ∈ Finset.range p, a j‖ ≤
          ‖∑ j ∈ Finset.range (n + 1), a j‖ + ‖∑ j ∈ Finset.range p, a j‖ :=
        norm_sub_le _ _
      _ ≤ M + M := add_le_add (ha n) (hprefix p)
      _ = 2 * M := by ring
  rw [summation_parts_tail a (fun n => (b n : K)) p q hpq]
  calc
    ‖(∑ j ∈ Finset.Icc p q, a j) * (b q : K) +
        ∑ n ∈ Finset.Ico p q,
          (∑ j ∈ Finset.Icc p n, a j) * ((b n : K) - (b (n + 1) : K))‖ ≤
        ‖(∑ j ∈ Finset.Icc p q, a j) * (b q : K)‖ +
          ∑ n ∈ Finset.Ico p q,
            ‖(∑ j ∈ Finset.Icc p n, a j) * ((b n : K) - (b (n + 1) : K))‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ (2 * M) * |b q| +
        ∑ n ∈ Finset.Ico p q, (2 * M) * |b n - b (n + 1)| := by
      apply add_le_add
      · rw [norm_mul, RCLike.norm_ofReal]
        exact mul_le_mul_of_nonneg_right (htail q hpq) (abs_nonneg _)
      · apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, ← RCLike.ofReal_sub, RCLike.norm_ofReal]
        exact mul_le_mul_of_nonneg_right (htail n (Finset.mem_Ico.mp hn).1)
          (abs_nonneg _)
    _ = (2 * M) * (|b q| + ∑ n ∈ Finset.Ico p q, |b n - b (n + 1)|) := by
      rw [mul_add, Finset.mul_sum]
    _ = 2 * M * |b p| := by rw [monotone_null_variation b hm hb p q hpq]

/-- Uniform decay of the finite-tail bound gives a common Cauchy threshold. -/
theorem uniform_cauchy_of_dirichlet_bound {E : Type u} {K : Type*} [NormedAddCommGroup K]
    (v : ℕ → E → K) (b : ℕ → E → ℝ) (M : ℝ)
    (htail : ∀ x p q, p ≤ q →
      ‖∑ n ∈ Finset.Icc p q, v n x‖ ≤ 2 * M * |b p x|)
    (hb : RealUniformConverges b (fun _ => 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ x,
      ‖(∑ j ∈ Finset.range (n + 1), v j x) -
        ∑ j ∈ Finset.range (m + 1), v j x‖ < ε := by
  intro ε hε
  let C := 2 * |M| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N, hN⟩ := hb (ε / C) (div_pos hε hC)
  have hordered : ∀ m n, N ≤ m → m ≤ n → ∀ x,
      ‖(∑ j ∈ Finset.range (n + 1), v j x) -
        ∑ j ∈ Finset.range (m + 1), v j x‖ < ε := by
    intro m n hm hmn x
    by_cases heq : m = n
    · subst n
      simpa using hε
    · have hmn' : m + 1 ≤ n := Nat.lt_of_le_of_ne hmn heq
      have hid := Finset.sum_Ico_eq_sub (fun j => v j x) (Nat.succ_le_succ hmn)
      simp only [Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc] at hid
      rw [← hid]
      calc
        ‖∑ j ∈ Finset.Icc (m + 1) n, v j x‖ ≤ 2 * M * |b (m + 1) x| :=
          htail x (m + 1) n hmn'
        _ ≤ C * |b (m + 1) x| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          dsimp [C]
          linarith [le_abs_self M]
        _ < C * (ε / C) := by
          apply mul_lt_mul_of_pos_left _ hC
          simpa only [sub_zero] using hN (m + 1) (hm.trans (Nat.le_succ m)) x
        _ = ε := mul_div_cancel₀ ε (ne_of_gt hC)
  refine ⟨N, ?_⟩
  intro m hm n hn x
  rcases le_total m n with hmn | hnm
  · exact hordered m n hm hmn x
  · simpa only [norm_sub_rev] using hordered n m hn hnm x

/-- Source finite-tail bound for real coefficients. -/
theorem real_uniform_dirichlet_tail_bound :
    Specs.SingleVariableAnalysis.Ch12.UniformDirichlet.realTailBound := by
  intro E a b M ha hm hb x p q hpq
  have hb' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |b n x| < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hb ε hε
    exact ⟨N, fun n hn => by simpa using hN n hn x⟩
  simpa only [Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq] using
    dirichlet_tail_bound (fun n => a n x) (fun n => b n x) M
      (by simpa only [Real.norm_eq_abs] using ha x) (hm x) hb' p q hpq

/-- Source finite-tail bound for complex coefficients and real weights. -/
theorem complex_uniform_dirichlet_tail_bound :
    Specs.SingleVariableAnalysis.Ch12.UniformDirichlet.complexTailBound := by
  intro E a b M ha hm hb x p q hpq
  apply dirichlet_tail_bound (fun n => a n x) (fun n => b n x) M (ha x) (hm x) _ p q hpq
  intro ε hε
  obtain ⟨N, hN⟩ := hb ε hε
  exact ⟨N, fun n hn => by simpa using hN n hn x⟩

/-- Uniform convergence of the ordinary real product series. -/
theorem real_uniform_dirichlet :
    Specs.SingleVariableAnalysis.Ch12.UniformDirichlet.realUniformDirichlet := by
  intro E a b M ha hm hb
  apply (real_uniform_cauchy_criterion _).mpr
  have hc := uniform_cauchy_of_dirichlet_bound
    (fun n x => a n x * b n x) b M
    (by simpa only [Real.norm_eq_abs] using
      real_uniform_dirichlet_tail_bound a b M ha hm hb) hb
  simpa only [Real.norm_eq_abs] using hc

/-- Uniform convergence of the ordinary complex product series. -/
theorem complex_uniform_dirichlet :
    Specs.SingleVariableAnalysis.Ch12.UniformDirichlet.complexUniformDirichlet := by
  intro E a b M ha hm hb
  apply (complex_uniform_cauchy_criterion _).mpr
  exact uniform_cauchy_of_dirichlet_bound
    (fun n x => a n x * (b n x : ℂ)) b M
    (complex_uniform_dirichlet_tail_bound a b M ha hm hb) hb

end SingleVariableAnalysis
